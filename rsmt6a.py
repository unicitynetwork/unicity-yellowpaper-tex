# ===========================================================================
# Radix Sparse Merkle Tree v6a (RSMT6a) - compact v6 consistency proofs
# ===========================================================================
#
# NOTE (relation to the Yellowpaper, Appendix "Radix Sparse Merkle Trees"):
# this prototype demonstrates the data structure and the proof rules, but is
# NOT binary-compatible with the specification. The spec uses the SDK's
# byte-order-preserving LSB-in-byte bit numbering; this file uses plain
# MSB-first order (keys as big-endian integers). The node/leaf hash layouts,
# opcode set, and every verifier rule are otherwise identical: the two
# conventions differ only by the fixed bijection on bit positions
# (and hence the traversal sort order and region packing).
#
# Hashes
# ------
#   H_leaf(key, value)     = SHA256(0x00 || key_32B || value)
#   H_node(d, p, lh, rh)   = SHA256(0x01 || d_1B || region_32B || lh || rh)
#
# where region p is the d-bit key prefix addressing the node (packed
# left-aligned into 32 bytes; injective together with d). A leaf's
# region is its full key. The region, like the depth, is an ABSOLUTE
# property of a node: splitting an edge above a node changes neither, so
# v3's insert-immutability of pre-existing hashes is preserved.
# Inclusion proofs do not change: the verifier derives each expected
# region from the queried key itself.
#
# Consistency proof format (flat post-order opcode stream)
# --------------------------------------------------------
#   'S',  hash                      : opaque preserved subtree. Only
#                                     admissible where the parent
#                                     junction is pre-existing.
#   'O',  depth, region, lh, rh    : preserved junction, opened one
#                                     level (hashed by the verifier, so
#                                     the annotations are collision-
#                                     bound to the digest).
#   'OL', key, value               : preserved leaf, opened.
#   'L'                            : new leaf; (key, value) is consumed
#                                     from the sorted batch.
#   'N',  depth                    : junction over the two preceding stack
#                                     entries. Its region is derived from
#                                     authenticated child advice.
#
# The verifier runs a stack machine over
#       (old_digest, new_digest, advice_depth, advice_region).
# At N(d), every child carrying advice yields the same parent region p and
# must extend p||side at a depth greater than d. At least one child must carry
# advice. If N is absent from the pre-state (one old child digest is None),
# both children must carry advice, preventing an opaque S from being attached
# through a new edge. Checking every available advised edge also makes v6's
# new/old stack flag redundant.

import hashlib

KEY_BYTES = 32
KEY_BITS = KEY_BYTES * 8  # 256; also the "depth" of a leaf

DEPTH_BYTES = [d.to_bytes(1, "big") for d in range(256)]


# ---------------------------------------------------------------------------
# Bit / prefix utilities (plain MSB-first order)
# ---------------------------------------------------------------------------


def key_bit(k, depth):
    """Bit of key k at position `depth`, counted from the MSB."""
    return (k >> (KEY_BITS - 1 - depth)) & 1


def prefix(k, d):
    """The d-bit region prefix of key k (as an integer with d bits)."""
    return k >> (KEY_BITS - d) if d > 0 else 0


def first_divergence(a, b):
    """First bit position (from MSB) where 256-bit integers a, b differ."""
    x = a ^ b
    return KEY_BITS - x.bit_length()  # x != 0 expected


# ---------------------------------------------------------------------------
# Hashers
# ---------------------------------------------------------------------------


def hash_leaf(key, value):
    return hashlib.sha256(b"\x00" + key.to_bytes(KEY_BYTES, "big") + value).digest()


def hash_node(depth, region, lh, rh):
    # Region packed left-aligned into 32 bytes; injective together with depth.
    packed = (region << (KEY_BITS - depth)).to_bytes(KEY_BYTES, "big")
    return hashlib.sha256(b"\x01" + DEPTH_BYTES[depth] + packed + lh + rh).digest()


# ---------------------------------------------------------------------------
# Node types (absolute depth and region stored per junction)
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
    __slots__ = ["depth", "region", "left", "right", "_hash"]

    def __init__(self, depth, region, left, right):
        self.depth = depth
        self.region = region
        self.left = left
        self.right = right
        self._hash = None

    def get_hash(self):
        if self._hash is None:
            self._hash = hash_node(
                self.depth, self.region, self.left.get_hash(), self.right.get_hash()
            )
        return self._hash


# ---------------------------------------------------------------------------
# Radix Sparse Merkle Tree with coherent consistency proofs
# ---------------------------------------------------------------------------


class SparseMerkleTree:
    def __init__(self, depth=KEY_BITS):
        if depth != KEY_BITS:
            raise ValueError("RSMT6 uses fixed 256-bit keys")
        self.root = None

    def get_root(self):
        return self.root.get_hash() if self.root else None

    # -- insertion with proof ------------------------------------------------

    def batch_insert(self, batch):
        """Insert new (key, value) pairs; keys already present are skipped
        (the honest dedup -- an adversarial re-record is REJECTED by the
        verifier, see Theorem 1). Returns (applied_items, proof_stream)."""
        new_items = {}
        for key, value in batch:
            if key in new_items or self._find_leaf(key) is not None:
                continue
            new_items[key] = value
        items = sorted(new_items.items())
        if not items:
            return [], []

        proof = []
        self.root = self._insert(self.root, items, 0, len(items), False, proof)
        return items, proof

    def _emit_preserved(self, node, parent_new, out):
        """A subtree untouched this round: opaque under an old junction,
        opened one level under a new one (the split edge)."""
        if not parent_new:
            out.extend(["S", node.get_hash()])
        elif isinstance(node, LeafBranch):
            out.extend(["OL", node.key, node.value])
        else:
            out.extend(
                ["O", node.depth, node.region,
                 node.left.get_hash(), node.right.get_hash()]
            )

    def _build(self, items, lo, hi, frozen, out):
        """Fresh subtree over sorted items; every junction is new. `frozen`
        maps a key to its pre-existing LeafBranch (leaf-merge case)."""
        if hi - lo == 1:
            k, v = items[lo]
            if k in frozen:
                out.extend(["OL", k, v])
                return frozen[k]
            out.append("L")
            return LeafBranch(k, v)
        split = first_divergence(items[lo][0], items[hi - 1][0])
        region = prefix(items[lo][0], split)
        mid = self._partition(items, lo, hi, split)
        ln = self._build(items, lo, mid, frozen, out)
        rn = self._build(items, mid, hi, frozen, out)
        out.extend(["N", split])
        return NodeBranch(split, region, ln, rn)

    def _partition(self, items, lo, hi, depth):
        while lo < hi:
            mid = (lo + hi) // 2
            if key_bit(items[mid][0], depth):
                hi = mid
            else:
                lo = mid + 1
        return lo

    def _insert(self, node, items, lo, hi, parent_new, out):
        if lo == hi:
            self._emit_preserved(node, parent_new, out)
            return node

        if node is None:
            return self._build(items, lo, hi, {}, out)

        if isinstance(node, LeafBranch):
            # Keys are pre-filtered distinct from node.key: merge and rebuild.
            merged = sorted(items[lo:hi] + [(node.key, node.value)])
            return self._build(merged, 0, len(merged), {node.key: node}, out)

        # Do the batch extremes diverge from this junction's region?
        d_div = node.depth
        for probe in (items[lo][0], items[hi - 1][0]):
            x = prefix(probe, node.depth) ^ node.region
            if x:
                d_div = min(d_div, node.depth - x.bit_length())
        if d_div < node.depth:
            return self._split_edge(node, items, lo, hi, d_div, out)

        mid = self._partition(items, lo, hi, node.depth)
        new_left = self._insert(node.left, items, lo, mid, False, out)
        new_right = self._insert(node.right, items, mid, hi, False, out)
        out.extend(["N", node.depth])
        node.left, node.right, node._hash = new_left, new_right, None
        return node

    def _split_edge(self, node, items, lo, hi, d_div, out):
        """New junction at depth d_div above `node` (canonical edge split)."""
        region = node.region >> (node.depth - d_div)
        node_side = (node.region >> (node.depth - d_div - 1)) & 1
        mid = self._partition(items, lo, hi, d_div)
        if node_side == 0:
            ln = self._insert(node, items, lo, mid, True, out)
            rn = self._build(items, mid, hi, {}, out)
        else:
            ln = self._build(items, lo, mid, {}, out)
            rn = self._insert(node, items, mid, hi, True, out)
        out.extend(["N", d_div])
        return NodeBranch(d_div, region, ln, rn)

    # -- queries ---------------------------------------------------------------

    def _find_leaf(self, key):
        node = self.root
        while node is not None:
            if isinstance(node, LeafBranch):
                return node if node.key == key else None
            if prefix(key, node.depth) != node.region:
                return None
            node = node.right if key_bit(key, node.depth) else node.left
        return None

    def inclusion_cert(self, key):
        """Root-to-leaf walk; bitmap of junction depths + sibling hashes.
        Regions are NOT included -- the verifier derives them from the key."""
        node = self.root
        bitmap = 0
        siblings = []
        while isinstance(node, NodeBranch):
            if prefix(key, node.depth) != node.region:
                return None
            bitmap |= 1 << node.depth
            if key_bit(key, node.depth):
                siblings.append(node.left.get_hash())
                node = node.right
            else:
                siblings.append(node.right.get_hash())
                node = node.left
        if not isinstance(node, LeafBranch) or node.key != key:
            return None
        return {"bitmap": bitmap, "siblings": siblings}

    def non_inclusion_witness(self, key):
        """Chain of openings along the key-directed descent, ending at the
        first node whose region is not a prefix of the key (or a leaf with
        a different key). None root is a witness for every key."""
        if self.root is None:
            return []
        chain = []
        node = self.root
        while True:
            if isinstance(node, LeafBranch):
                chain.append(("LEAF", node.key, node.value))
                return chain if node.key != key else None
            chain.append(
                ("NODE", node.depth, node.region,
                 node.left.get_hash(), node.right.get_hash())
            )
            if prefix(key, node.depth) != node.region:
                return chain  # divergence junction: terminal
            node = node.right if key_bit(key, node.depth) else node.left


# ---------------------------------------------------------------------------
# Verifiers
# ---------------------------------------------------------------------------


def verify_consistency(proof, old_root, new_root, batch, _=None):
    """Compact v6 stack machine.

    N carries only a depth. Its region is derived from authenticated child
    advice. Any accepting proof expands to an accepting v6 proof by inserting
    the derived region at each N, so v6's append-only and canonicality results
    apply unchanged.
    """
    if not batch:
        return old_root == new_root and not proof

    try:
        sorted_batch = sorted(batch)
    except TypeError:
        return False
    for i in range(1, len(sorted_batch)):  # strictly increasing keys
        if sorted_batch[i - 1][0] >= sorted_batch[i][0]:
            return False

    stack = []
    pi = 0
    bi = 0
    try:
        while pi < len(proof):
            tag = proof[pi]
            pi += 1

            if tag == "S":
                h = proof[pi]; pi += 1
                if not isinstance(h, bytes) or len(h) != 32:
                    return False
                stack.append((h, h, None, None))

            elif tag == "O":
                d, p, lh, rh = proof[pi:pi + 4]; pi += 4
                if not isinstance(d, int) or not 0 <= d < KEY_BITS:
                    return False
                if not isinstance(p, int) or not 0 <= p < (1 << d if d else 1):
                    return False
                if not isinstance(lh, bytes) or len(lh) != 32:
                    return False
                if not isinstance(rh, bytes) or len(rh) != 32:
                    return False
                h = hash_node(d, p, lh, rh)
                stack.append((h, h, d, p))

            elif tag == "OL":
                k, v = proof[pi:pi + 2]; pi += 2
                if not isinstance(k, int) or not 0 <= k < (1 << KEY_BITS):
                    return False
                if not isinstance(v, bytes):
                    return False
                h = hash_leaf(k, v)
                stack.append((h, h, KEY_BITS, k))

            elif tag == "L":
                k, v = sorted_batch[bi]; bi += 1
                if not isinstance(k, int) or not 0 <= k < (1 << KEY_BITS):
                    return False
                if not isinstance(v, bytes):
                    return False
                stack.append((None, hash_leaf(k, v), KEY_BITS, k))

            elif tag == "N":
                d = proof[pi]; pi += 1
                if not isinstance(d, int) or not 0 <= d < KEY_BITS:
                    return False
                rh0, rh1, rdelta, rrho = stack.pop()
                lh0, lh1, ldelta, lrho = stack.pop()

                # Derive p from every available child descriptor. Descriptors
                # must agree and each described edge must be coherent.
                p = None
                for delta, rho, side in (
                    (ldelta, lrho, 0),
                    (rdelta, rrho, 1),
                ):
                    if delta is None:
                        continue
                    if delta <= d:
                        return False
                    candidate = rho >> (delta - d)
                    if ((rho >> (delta - d - 1)) & 1) != side:
                        return False
                    if p is not None and p != candidate:
                        return False
                    p = candidate
                if p is None:
                    return False

                is_new = lh0 is None or rh0 is None
                if is_new and (ldelta is None or rdelta is None):
                    return False

                # four-way pre-state rule
                if lh0 is None and rh0 is None:
                    h0 = None
                elif lh0 is None:
                    h0 = rh0                    # pass-through
                elif rh0 is None:
                    h0 = lh0                    # pass-through
                else:
                    h0 = hash_node(d, p, lh0, rh0)

                h1 = hash_node(d, p, lh1, rh1)
                stack.append((h0, h1, d, p))

            else:
                return False
    except (IndexError, OverflowError, ValueError, TypeError):
        return False

    if pi != len(proof) or bi != len(sorted_batch) or len(stack) != 1:
        return False
    h0, h1 = stack[0][0], stack[0][1]
    return h0 == old_root and h1 == new_root


def verify_inclusion(cert, root_hash, key, value):
    """Regions recomputed from the key: prefix(key, d) at each junction."""
    bitmap = cert["bitmap"]
    siblings = list(cert["siblings"])

    h = hash_leaf(key, value)
    j = len(siblings)
    for d in range(KEY_BITS):          # deepest junction combines first
        dd = KEY_BITS - 1 - d
        if not (bitmap >> dd) & 1:
            continue
        j -= 1
        if j < 0:
            return False
        s = siblings[j]
        if key_bit(key, dd):
            h = hash_node(dd, prefix(key, dd), s, h)
        else:
            h = hash_node(dd, prefix(key, dd), h, s)
    return j == 0 and h == root_hash


def verify_non_inclusion(chain, root_hash, key):
    """Openings chain from the root along key-directed descent; terminal is
    a junction whose region is not a prefix of the key, or a foreign leaf.
    Empty chain is valid iff the tree is empty."""
    if root_hash is None:
        return chain == []
    if not chain:
        return False
    expected = root_hash
    last = len(chain) - 1
    for i, item in enumerate(chain):
        if item[0] == "LEAF":
            _, k, v = item
            return i == last and hash_leaf(k, v) == expected and k != key
        _, d, p, lh, rh = item
        if hash_node(d, p, lh, rh) != expected:
            return False
        if prefix(key, d) != p:
            return i == last          # divergence junction: valid terminal
        expected = rh if key_bit(key, d) else lh
    return False                       # chain ended without a terminal
