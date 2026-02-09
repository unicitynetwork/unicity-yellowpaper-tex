# This implementation illustrates the path-compressed Sparse Merkle Tree (SMT)
# with non-deletion proofs
# specification defined in Appendix A.3 of the Unicity Whitepaper.

import hashlib
import sys
import random
import json

default = 0  # default 'empty' leaf/node (represented as ⊥ in spec)

def hash_leaf(path_segment: int, data: int) -> int:
    """
    Computes hash of an SMT leaf node.
    h = H(p, d) where p is path segment, d is leaf data
    """
    h = hashlib.sha256()
    h.update(b'leaf')  # Domain separator
    h.update(path_segment.to_bytes(32, byteorder='big', signed=False))
    h.update(data.to_bytes(32, byteorder='big', signed=False))
    return int.from_bytes(h.digest(), byteorder='big', signed=False)

def hash_branch(path_segment: int, left_hash: int, right_hash: int) -> int:
    """
    Computes hash of an SMT branch node.
    h = H(p, h_L, h_R) where p is path segment, h_L and h_R are child hashes
    Returns default (⊥) if both children are empty
    """
    if left_hash == default and right_hash == default:
        return default  # Empty subtree

    h = hashlib.sha256()
    h.update(b'branch')  # Domain separator
    h.update(path_segment.to_bytes(32, byteorder='big', signed=False))
    # Encode default (⊥) as zero bytes
    h.update(left_hash.to_bytes(32, byteorder='big', signed=False))
    h.update(right_hash.to_bytes(32, byteorder='big', signed=False))
    return int.from_bytes(h.digest(), byteorder='big', signed=False)

class SparseMerkleTree:
    def __init__(self, depth=256):
        self.depth = depth
        # Node dictionary stores (level, key_integer) -> hash_value
        self.nodes = {}
        self.default = default  # All empty nodes have value ⊥ (default)

    def get_root(self):
        return self.get_node(self.depth, 0)

    def get_node(self, level, key):
        """Gets a node's hash value. key is an integer."""
        return self.nodes.get((level, key), default)

    def update_node(self, level, key, value):
        """Updates a node's hash value."""
        if value == default:
            # Remove default values to keep sparse representation
            self.nodes.pop((level, key), None)
        else:
            self.nodes[(level, key)] = value

    def get_path_segment(self, level, key):
        """
        Computes the path segment for a node at given level with given key.
        In this simplified implementation, path segment encodes the position.
        For leaf nodes (level 0), the path segment is the full key.
        For branch nodes, the path segment is empty (0) at root, or derived from position.
        """
        if level == 0:
            # Leaf node: path segment is the key itself
            return key
        elif level == self.depth:
            # Root node: empty path segment
            return 0
        else:
            # Branch node: path segment could encode the bit position
            # For simplicity, we use the key at this level as path segment
            return key

    def batch_insert(self, nodes):
        """
        Inserts a batch of nodes into the tree and generates a consistency proof.

        The proof consists of sibling nodes required to verify the state transition
        from old root to new root, proving that only new leaves were added.

        Returns: proof where proof[level] = [(sid, hash), ...]
        """
        # Filter out keys that already exist in the tree to avoid failing the entire batch
        new_nodes = []
        for key, value in nodes:
            if (0, key) in self.nodes:
                print(f"The leaf '{key}' is already set, skipping.", file=sys.stderr)
            else:
                new_nodes.append((key, value))

        if not new_nodes:
            return [[] for _ in range(self.depth)]  # No changes, empty proof

        # Sort the new key-value pairs by key
        new_nodes.sort()
        new_keys = [k for k, _ in new_nodes]

        # Insert all new leaves at level 0 (compute leaf hashes)
        for key, value in new_nodes:
            path_seg = self.get_path_segment(0, key)
            leaf_hash = hash_leaf(path_seg, value)
            self.update_node(0, key, leaf_hash)

        proof = [[] for _ in range(self.depth)]  # proof[level] = [(sid, hash), ...]

        # 'affected_keys_at_level' are the keys of nodes at a given level
        # that are on the path of the inserted leaves.
        affected_keys_at_level = set(new_keys)

        for level in range(self.depth):  # Iterate from leaves (level 0) up to root
            parent_keys = {k >> 1 for k in affected_keys_at_level}

            # For each parent, find the required siblings at the current level
            for p_key in parent_keys:
                left_child_key = p_key << 1
                right_child_key = left_child_key | 1

                is_left_affected = left_child_key in affected_keys_at_level
                is_right_affected = right_child_key in affected_keys_at_level

                # If one child is affected and the other is not, the unaffected one is a
                # sibling needed for the proof.
                if is_left_affected and not is_right_affected:
                    sibling_val = self.get_node(level, right_child_key)
                    if sibling_val != default:
                        proof[level].append((right_child_key, sibling_val))

                if is_right_affected and not is_left_affected:
                    sibling_val = self.get_node(level, left_child_key)
                    if sibling_val != default:
                        proof[level].append((left_child_key, sibling_val))

            # Calculate and update the parent nodes in the tree using branch hash
            for p_key in parent_keys:
                left_child_key = p_key << 1
                right_child_key = left_child_key | 1

                left_val = self.get_node(level, left_child_key)
                right_val = self.get_node(level, right_child_key)

                path_seg = self.get_path_segment(level + 1, p_key)
                p_val = hash_branch(path_seg, left_val, right_val)
                self.update_node(level + 1, p_key, p_val)

            # The affected keys for the next level are the parent keys we just processed
            affected_keys_at_level = parent_keys

        # Sort the proof lists for deterministic output
        for level_proof in proof:
            level_proof.sort()

        return proof

def get_path_segment_for_verification(level, key, depth):
    """Helper to compute path segment during verification."""
    if level == 0:
        return key
    elif level == depth:
        return 0
    else:
        return key

def smt_compute_tree_root(proof, batch, depth):
    """
    Computes the SMT root hash from a batch of leaves and proof siblings.
    Corresponds to smt_compute_tree_root in spec (Appendix A.3, sec:smt-compute-tree-root).

    This implements the algorithm that:
    1. Starts with leaves (batch)
    2. For each level, computes parent hashes using siblings from proof or from batch
    3. Returns the root hash
    """
    # Start with leaf layer - convert (key, value) to (key, hash)
    nodes = []
    for key, value in batch:
        path_seg = get_path_segment_for_verification(0, key, depth)
        if value == default:
            # Empty leaf
            leaf_hash = default
        else:
            leaf_hash = hash_leaf(path_seg, value)
        nodes.append((key, leaf_hash))

    # Process each level from leaves to root
    for level in range(depth):
        next_nodes = []
        lproof = proof[level]
        i, j = 0, 0

        while i < len(nodes):
            k, kval = nodes[i]
            parent = k // 2
            last_bit = k % 2
            sibling = parent * 2 + (1 - last_bit)

            # Find sibling value: from next node in batch, from proof, or default
            if last_bit == 0 and i != len(nodes)-1 and nodes[i+1][0] == sibling:
                # Sibling is next in layer (both children in batch)
                i = i + 1
                siblingval = nodes[i][1]
            elif j < len(lproof) and lproof[j][0] == sibling:
                # Sibling from proof
                siblingval = lproof[j][1]
                j = j + 1
            else:
                # Sibling is empty
                siblingval = default

            # Compute parent hash using branch hash function
            path_seg = get_path_segment_for_verification(level + 1, parent, depth)
            if last_bit == 0:
                pv = hash_branch(path_seg, kval, siblingval)
            else:
                pv = hash_branch(path_seg, siblingval, kval)

            next_nodes.append((parent, pv))
            i = i + 1

        nodes = next_nodes

    assert len(nodes) == 1, "Should have exactly 1 node at root level"
    return nodes[0][1]

def verify_non_deletion(proof, old_root, new_root, batch, depth):
    """
    Verifies a consistency proof (non-deletion proof).
    """
    if not batch:
        return old_root == new_root

    # Step 1: Compute root with empty leaves (B_⊥)
    # This proves the positions were empty before insertion
    batch_empty = [(key, default) for key, _ in batch]
    r1 = smt_compute_tree_root(proof, batch_empty, depth)
    if r1 != old_root:
        print(f"Non-deletion proof verification failed at step 1:", file=sys.stderr)
        print(f"  Computed root with empty leaves: {r1}", file=sys.stderr)
        print(f"  Expected old root: {old_root}", file=sys.stderr)
        return False

    # Step 2: Compute root with actual batch values (B)
    # This proves the new leaves are correctly placed
    r2 = smt_compute_tree_root(proof, batch, depth)
    if r2 != new_root:
        print(f"Non-deletion proof verification failed at step 2:", file=sys.stderr)
        print(f"  Computed root with batch: {r2}", file=sys.stderr)
        print(f"  Expected new root: {new_root}", file=sys.stderr)
        return False

    # Success: The proof demonstrates that:
    # 1. All newly inserted leaves were at empty (⊥) positions before
    # 2. After insertion, new leaves are correctly placed
    # 3. No other changes were made (siblings in proof are unchanged)
    return True


def main():
    depth = 32

    def to_int(aa):
        if isinstance(aa, (list, tuple)):
            return [to_int(a) for a in aa]
        elif isinstance(aa, bytes):
            return int.from_bytes(aa, byteorder='big')
        else:
            # Fallback for whatever with __str__
            return int.from_bytes(str(aa).encode(), byteorder='big')

    smt = SparseMerkleTree(depth)

    keys = to_int([b'\x01', b'\x02', b'\x03']) # test adjacent key handling
    values = to_int([b'value1', b'value2', b'value3'])
    batch = sorted(zip(keys, values))

    old_root = smt.get_root()
    proof = smt.batch_insert(batch)
    new_root = smt.get_root()
    assert verify_non_deletion(proof, old_root, new_root, batch, depth)

    # --- pre-filling the tree ---
    batch = []
    for i in range(500):
        rk = hash("a" + str(i)) % (2**depth)
        rv = to_int("Val " + str(rk))
        if (rk, rv) in batch: continue
        batch.append((rk, rv))

    print(f"Pre-filling the SMT with {len(batch)} items.", file=sys.stderr)

    old_root = new_root
    proof = smt.batch_insert(batch)
    new_root = smt.get_root()
    assert verify_non_deletion(proof, old_root, new_root, sorted(batch), depth)

    # --- batch for proving ---
    batch = []
    for i in range(50):
        rk = hash("b" + str(i)) % (2**depth)
        rv = to_int("Val " + str(rk))
        if (rk, rv) in batch: continue
        batch.append((rk, rv))

    batch = sorted(batch)
    old_root = new_root
    print(f"Preparing witness for a batch of {len(batch)} items.", file=sys.stderr)
    proof = smt.batch_insert(batch)
    print("Insertion and proof generation done.", file=sys.stderr)
    new_root = smt.get_root()
    assert verify_non_deletion(proof, old_root, new_root, batch, depth)

    witness_data = {
        "old_root": old_root,
        "new_root": new_root,
        "batch": batch,
        "proof": proof,
        "depth": depth
    }
    print(json.dumps(witness_data, indent=4))


if __name__ == "__main__":
    main()
