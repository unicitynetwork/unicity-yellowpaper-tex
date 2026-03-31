# ===========================================================================
# Radix Sparse Merkle Tree v3 (RSMT3) - with optimizations
# ===========================================================================
#
# Leaf-anchored topology: each leaf hashes the full 256-bit key, making
# leaves the spatial anchors. Internal nodes hash exactly two children and
# commit to their explicit bifurcation depth:
#   H_node(lh, rh, depth) = SHA256(0x01 || depth_1B || lh || rh)
#   H_leaf(key, value)    = SHA256(0x00 || key_32B  || value)
#
# Because neither leaf nor node hashes depend on the tree's edge structure
# (path / common prefix), inserting a new key only creates hashes for
# the new leaf and new internal bifurcation nodes. Pre-existing node hashes
# are strictly read-only; splitting an edge above them does not alter their
# split-bit depth, rendering their hash immutable.
#
# ---------------------------------------------------------------------------
# Consistency Proof
# -----------------
# Demonstrates that batch B was correctly inserted into tree state ρ_0,
# producing state ρ_1, without modifying or deleting pre-existing records.
#
# Format (flat opcode stream from LSB-first post-order traversal):
#   'S' (Subtree): Stream: ['S', hash]. Represents an unmodified existing branch.
#   'L' (Leaf):    Stream: ['L']. Denotes a newly inserted key-value pair.
#   'N' (Node):    Stream: ['N', depth]. Two children precede (left, right).
#
# Verification Algorithm -- Eval(π, B) --> (h_0, h_1):
#   1. Sort batch B by LSB-first traversal order (bit-reversed sort keys).
#   2. Initialize a result stack and iterators for π and sorted B.
#   3. Scan tokens in π (stack machine, no recursion):
#      - 'S': push (hash, hash).
#      - 'L': pop (k, v) from B. Push (null, H_leaf(k, v)).
#      - 'N': pop depth. Pop right (rh_0, rh_1), pop left (lh_0, lh_1).
#             h_0 = resolve_pre_state(lh_0, rh_0, depth)
#             h_1 = H_node(lh_1, rh_1, depth)
#             Push (h_0, h_1).
#   4. Accept iff π and B are fully consumed, the stack holds exactly
#      one element, and that element equals (ρ_0, ρ_1).
#
# Security Argument (Dishonest Operator):
#   Threat Model: The operator controls the tree and proof generation.
#     Root hashes are committed to a trusted repository; the verifier
#     and batch B are trusted inputs (we inore how leaf is validated).
#   Theorem: The operator cannot silently modify/delete existing data,
#     omit batch insertions, or inject phantom data while producing a
#     proof π that satisfies verify_consistency(π, ρ_0, ρ_1, B).
#
#   Trusted Data Structure Design:
#     - Domain Separation: prefix 0x00 (leaf) vs 0x01 (node) ensures
#       leaf and node hashes have disjoint preimage spaces.
#     - Non-commutativity: H_node(lh, rh, d) places lh, rh at distinct
#       positions, so swapping children produces a different hash.
#     - Depth Commitment: explicit depth in H_node binds each internal
#       node to its tree level, preventing level-shifting attacks.
#     - Full Key Commitment: H_leaf includes the complete 256-bit key,
#       anchoring each leaf to a unique identity.
#
#   Security Argument:
#   1. Integrity (no modification/deletion of existing data):
#      a) Binding Pre-state: The proof's recursive evaluation reconstructs
#         ρ_0 from 'S' hashes chained through 'N' depths. Since ρ_0 is
#         committed and fixed, substituting a modified subtree hash at
#         any 'S' position alters ρ_0 — contradicting the commitment.
#         (Collision resistance)
#      b) Complete Coverage: To reconstruct ρ_0, every branch of the
#         pre-state tree must be represented in the proof. Omitting any
#         subtree alters the hash chain, failing to match ρ_0.
#      c) Preservation: 'S' returns (h, h) -- identical hashes for both
#         pre-state and post-state. Every subtree present in ρ_0 appears
#         unchanged in ρ_1.
#      d) Depth Binding: Relocating an 'S' subtree to a different level
#         changes the depth argument of ancestor 'N' nodes, altering
#         the hash chain and failing to reconstruct ρ_0.
#      e) Non-commutativity: Swapping left/right children of any 'N'
#         node changes hash_node's output, detected via ρ_0 mismatch.
#   2. Completeness (all elements in B inserted):
#      a) Independent Sort: The verifier sorts B by get_sort_key()
#         independently. Each 'L' opcode consumes the next element in
#         this deterministic order.
#      b) Exhaustion Check: Post-evaluation, the verifier asserts both
#         proof stream and batch iterator are fully consumed. Omitting
#         any batch element leaves the iterator non-exhausted -> reject.
#      c) Order Binding: Reordering maps an 'L' to the wrong (k, v),
#         producing an incorrect H_leaf, failing to reconstruct ρ_1.
#   3. No Phantom Data: Every proof terminal is 'S' (hash-bound to ρ_0)
#      or 'L' (consumed from provided B). No opcode mechanism
#      exists to introduce key-value pairs outside B.
#   4. Pre-state Resolution Correctness: When a node has one purely-new
#      child (h_0 = None), the parent's h_0 passes through the existing
#      child's h_0 without hashing. This is correct: in the pre-state
#      the parent node did not exist -- only the existing subtree occupied
#      that position.
#
# ---------------------------------------------------------------------------
# Inclusion Proof
# ---------------
# Demonstrates that a specific (key, value) exists within state ρ.
#
# Format:
#   - bitmap: bit string (here 256-bit integer). Set bits indicate branch
#             node depth positions.
#   - siblings: Array of sibling hashes ordered leaf-to-root.
#
# Security Argument:
#   Theorem: The operator cannot produce an inclusion proof for a
#     (key, value) pair not in the tree committed under ρ.
#   Proof:
#   1. Leaf Anchorage: H_leaf commits to the full 256-bit key and the
#      complete value. No shortened key or altered value produces the
#      same leaf hash. (Preimage resistance of SHA-256.)
#   2. Domain Separation?: The 0x00/0x01 prefix prevents a leaf hash from
#      colliding with a node hash, ruling out type confusion in the chain.
#   3. Path Binding: At each internal node the verifier determines the
#      combination order (left/right) from the key's bit at that depth.
#      A leaf placed at a position inconsistent with its key bits causes
#      the verifier to combine hashes in the wrong order, producing a
#      different root — detectable because ρ is committed.
#   4. Structural Rigidity: The bitmap encodes explicit node depths used
#      in H_node. Omitting levels or shifting the leaf to a different
#      depth changes the depth argument, altering the hash.
#   5. Hash Chain Integrity: Forging a valid sibling sequence requires
#      finding hashes that, combined with H_leaf through the claimed
#      depths, produce ρ — a second-preimage attack on the iterated
#      hash chain.
#
# ---------------------------------------------------------------------------
# Protocol Considerations
# ---------------------------------------------------------------------------
# - Already-existing keys: batch_insert silently filters keys already in
#   the tree. The consistency proof covers only actually-inserted keys.
#   If the operator claims a batch key pre-exists and omits it, the
#   protocol must independently verify pre-existence via an inclusion
#   proof against ρ_0. Without this check, the operator can drop items.
# - Denial of service: A malicious proof with excessive 'N' nesting can
#   cause deep recursion. Production verifiers should enforce a recursion
#   depth limit (256 for a 256-bit key space).


import hashlib

# ---------------------------------------------------------------------------
# Constants & Hashers and lookup tables
# ---------------------------------------------------------------------------

KEY_BYTES = 32

# Pre-compute depth byte strings to avoid calling .to_bytes() millions of times
DEPTH_BYTES = [d.to_bytes(1, "big") for d in range(256)]

# Pre-compute table to reverse bits in a byte at C-speed
BIT_REVERSE_TABLE = bytes(int(f"{i:08b}"[::-1], 2) for i in range(256))


def get_sort_key(k):
    """
    Converts integer key to LSB-first lexicographical sort key.
    (Reverse byte order, then reverse bits in each byte).
    """
    return k.to_bytes(KEY_BYTES, "big")[::-1].translate(BIT_REVERSE_TABLE)


def hash_leaf(key, value):
    return hashlib.sha256(b"\x00" + key.to_bytes(KEY_BYTES, "big") + value).digest()


def hash_node(lh, rh, depth):
    # Uses pre-computed depth bytes for speed
    return hashlib.sha256(b"\x01" + DEPTH_BYTES[depth] + lh + rh).digest()


# ---------------------------------------------------------------------------
# Path utilities
# ---------------------------------------------------------------------------


def path_len(p):
    return p.bit_length() - 1


# ---------------------------------------------------------------------------
# Node types
# ---------------------------------------------------------------------------


class LeafBranch:
    __slots__ = ["key", "value", "_hash"]

    def __init__(self, key, value):
        self.key = key
        self.value = value
        self._hash = hash_leaf(key, value)

    def get_hash(self):
        return self._hash


class NodeBranch:
    __slots__ = ["path", "left", "right", "depth", "_hash"]

    def __init__(self, path, left, right, depth):
        self.path = path
        self.left = left
        self.right = right
        self.depth = depth
        self._hash = None

    def get_hash(self):
        if self._hash is None:
            self._hash = hash_node(
                self.left.get_hash(), self.right.get_hash(), self.depth
            )
        return self._hash


# ---------------------------------------------------------------------------
# Radix Sparse Merkle Tree
# ---------------------------------------------------------------------------


class SparseMerkleTree:
    def __init__(self, depth=256):
        self.depth = depth  # not used, capacity is determined by key length
        self.root = None

    def get_root(self):
        return self.root.get_hash() if self.root else None

    def batch_insert(self, batch):
        new_items = {}
        for key, data in batch:
            if key in new_items or self._find_leaf(key) is not None:
                continue
            new_items[key] = data

        if not new_items:
            return [], ["S", None]

        # Sort the batch into tree-traversal order
        items = list(new_items.items())
        items.sort(key=lambda x: get_sort_key(x[0]))

        proof_out = []
        self.root = self._insert_proof(self.root, items, 0, len(items), 0, proof_out)

        return items, proof_out

    def _build_subtree(self, batch, start, end, start_bit, proof_out, frozen):
        if end - start == 1:
            k, v = batch[start]
            if k in frozen:
                proof_out.extend(["S", frozen[k]])
            else:
                proof_out.append("L")
            return LeafBranch(k, v)

        # O(1) split-point from extremes, O(log N) binary search partition
        xor = (batch[start][0] ^ batch[end - 1][0]) >> start_bit
        split = start_bit + (xor & -xor).bit_length() - 1

        low, high = start, end
        while low < high:
            mid = (low + high) // 2
            if (batch[mid][0] >> split) & 1:
                high = mid
            else:
                low = mid + 1
        mid = low

        n_common = split - start_bit
        cp = (1 << n_common) | ((batch[start][0] >> start_bit) & ((1 << n_common) - 1))

        ln = self._build_subtree(batch, start, mid, split, proof_out, frozen)
        rn = self._build_subtree(batch, mid, end, split, proof_out, frozen)
        proof_out.extend(["N", split])
        return NodeBranch(cp, ln, rn, split)

    def _insert_proof(self, node, batch, start, end, start_bit, proof_out):
        if start == end:
            proof_out.extend(["S", node.get_hash() if node else None])
            return node

        if node is None:
            return self._build_subtree(batch, start, end, start_bit, proof_out, {})

        if isinstance(node, LeafBranch):
            frozen = {node.key: node.get_hash()}
            mixed = batch[start:end] + [(node.key, node.value)]
            mixed.sort(key=lambda x: get_sort_key(x[0]))
            return self._build_subtree(
                mixed, 0, len(mixed), start_bit, proof_out, frozen
            )

        n_path = path_len(node.path)
        node_prefix = node.path & ((1 << n_path) - 1)

        # O(1) checks to see if the batch bounds diverge from the node path
        first_div = n_path
        xor_start = ((batch[start][0] >> start_bit) & ((1 << n_path) - 1)) ^ node_prefix
        if xor_start:
            first_div = min(first_div, (xor_start & -xor_start).bit_length() - 1)
        xor_end = ((batch[end - 1][0] >> start_bit) & ((1 << n_path) - 1)) ^ node_prefix
        if xor_end:
            first_div = min(first_div, (xor_end & -xor_end).bit_length() - 1)

        if first_div < n_path:
            return self._node_split_proof(
                node, batch, start, end, start_bit, first_div, proof_out
            )

        split = start_bit + n_path

        low, high = start, end
        while low < high:
            mid = (low + high) // 2
            if (batch[mid][0] >> split) & 1:
                high = mid
            else:
                low = mid + 1
        mid = low

        new_left = self._insert_proof(node.left, batch, start, mid, split, proof_out)
        new_right = self._insert_proof(node.right, batch, mid, end, split, proof_out)
        proof_out.extend(["N", split])

        node.left, node.right, node._hash = new_left, new_right, None
        return node

    def _node_split_proof(
        self, node, batch, start, end, start_bit, first_div, proof_out
    ):
        n_path = path_len(node.path)
        node_prefix = node.path & ((1 << n_path) - 1)

        n_common = first_div
        new_cp = (1 << n_common) | (node_prefix & ((1 << n_common) - 1))
        new_split = start_bit + n_common
        old_dir = (node_prefix >> n_common) & 1

        new_path = node.path >> n_common
        node.path = new_path if new_path != 0 else 1

        low, high = start, end
        while low < high:
            mid = (low + high) // 2
            if (batch[mid][0] >> new_split) & 1:
                high = mid
            else:
                low = mid + 1
        mid = low

        if old_dir == 0:
            new_left = self._insert_proof(node, batch, start, mid, new_split, proof_out)
            new_right = self._insert_proof(None, batch, mid, end, new_split, proof_out)
        else:
            new_left = self._insert_proof(None, batch, start, mid, new_split, proof_out)
            new_right = self._insert_proof(node, batch, mid, end, new_split, proof_out)
        proof_out.extend(["N", new_split])

        return NodeBranch(new_cp, new_left, new_right, new_split)

    def _find_leaf(self, key):
        node = self.root
        bit = 0
        while node is not None:
            if isinstance(node, LeafBranch):
                return node if node.key == key else None
            n = path_len(node.path)
            if ((key >> bit) & ((1 << n) - 1)) != (node.path & ((1 << n) - 1)):
                return None
            bit += n
            node = node.right if ((key >> bit) & 1) else node.left
        return None


# ---------------------------------------------------------------------------
# Verifier Functions
# ---------------------------------------------------------------------------


def verify_consistency(proof, old_root, new_root, batch, _=None):
    """
    Stack-machine verifier. Post-order proof format means S/L push results
    and N pops two children — no recursion, no stack overflow risk.
    """
    if not batch:
        return old_root == new_root

    sorted_batch = sorted(batch, key=lambda x: get_sort_key(x[0]))
    stack = []
    pi = 0  # proof index
    bi = 0  # batch index

    try:
        while pi < len(proof):
            tag = proof[pi]
            pi += 1

            if tag == "S":
                h = proof[pi]
                if h == None:
                    print("SNone", h)
                if h == b"\x00" * 32:
                    print("Szeros", h)
                # print("S", h.hex())
                pi += 1
                stack.append((h, h))

            elif tag == "L":
                k, v = sorted_batch[bi]
                bi += 1
                stack.append((None, hash_leaf(k, v)))

            elif tag == "N":
                depth = proof[pi]
                pi += 1
                rh0, rh1 = stack.pop()
                lh0, lh1 = stack.pop()

                if lh0 is None and rh0 is None:
                    h0 = None
                elif lh0 is None:
                    h0 = rh0
                elif rh0 is None:
                    h0 = lh0
                else:
                    h0 = hash_node(lh0, rh0, depth)

                stack.append((h0, hash_node(lh1, rh1, depth)))

            else:
                return False
    except (IndexError, ValueError):
        return False

    if pi != len(proof) or bi != len(sorted_batch) or len(stack) != 1:
        return False

    r0, r1 = stack[0]
    return r0 == old_root and r1 == new_root
