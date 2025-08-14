# Spathoulas Dimitris

# ### NOT YET IMPLEMENTED
# We adopt a self-balancing binary search tree
# (e.g. Red-Black Tree [GS78]) to dynamically maintain these upper bounds, with O(max{1, log(N/M )})
# search/update time.

from bisect import bisect_left, bisect_right, insort
from collections import deque
import math
import heapq
from typing import List, Tuple, Optional, Dict

class _Block:
    """Block storing up to ~M key,value pairs sorted by value (then key for determinism)."""
    __slots__ = ("items",)  # items is list of (key, value)

    def __init__(self, items: Optional[List[Tuple]] = None):
        # ensure items sorted by (value, key)
        if items:
            self.items = sorted(items, key=lambda kv: (kv[1], kv[0]))
        else:
            self.items = []

    def __len__(self):
        return len(self.items)

    def upper_bound(self):
        if not self.items:
            return None
        # max value in block
        return self.items[-1][1]

    def min_value(self):
        if not self.items:
            return None
        return self.items[0][1]

    def insert(self, key, val):
        """Insert (key,val) maintaining sorted order by (value, key)."""
        # use bisect on (value, key)
        pair = (key, val)
        lo, hi = 0, len(self.items)
        # binary search to find position by (val, key)
        while lo < hi:
            mid = (lo + hi) // 2
            if (self.items[mid][1], self.items[mid][0]) < (val, key):
                lo = mid + 1
            else:
                hi = mid
        self.items.insert(lo, pair)

    def delete_key(self, key) -> Optional[Tuple]:
        """Delete key if present, return (key,val) or None."""
        for i, (k, v) in enumerate(self.items):
            if k == key:
                return self.items.pop(i)
        return None

    def pop_first_k(self, k):
        """Pop and return first k items (smallest values)."""
        taken = self.items[:k]
        self.items = self.items[k:]
        return taken

    def split_median(self):
        """Split at true median by value. Return (left_block, right_block).
           If block empty or size 1, right may be empty.
        """
        n = len(self.items)
        if n <= 1:
            left = _Block(self.items[:])
            right = _Block([])
            return left, right
        # find median index by value using select-like approach: we use sort since items are already sorted
        mid = n // 2
        left_items = self.items[:mid]
        right_items = self.items[mid:]
        return _Block(left_items), _Block(right_items)

    def contains_key(self, key):
        for k, v in self.items:
            if k == key:
                return True
        return False

    def find_value(self, key):
        for k, v in self.items:
            if k == key:
                return v
        return None

    def to_list(self):
        return list(self.items)


class Lemma33:
    """
    Faithful implementation of Lemma 3.3 (block-based structure).
    Public methods:
      - insert(key, value)
      - batch_prepend(list_of_pairs)  # pairs are (key,value), and values must be < any existing value
      - pull() -> (list_of_keys, x)    # returns up to M keys and separator x
    """
    def __init__(self, M: int, B: float):
        assert M >= 1
        self.M = M
        self.B = B
        # D0: deque of _Block objects (batch-prepends) - leftmost has smallest values
        self.D0: deque[_Block] = deque()
        # D1: deque of _Block objects (inserts) - leftmost has smallest upper bound
        self.D1: deque[_Block] = deque()
        # maintain parallel sorted list of bounds for D1 blocks to locate block by value
        self._d1_bounds: List[float] = []
        # mapping bound -> block (multiple blocks may share same bound; store list)
        self._bound_to_block: Dict[float, List[_Block]] = {}
        # mapping key -> (value, block_reference, is_in_D0)
        self.key_map: Dict = {}
        # initialize D1 with one empty block with bound B (as in proof)
        self._append_d1_block(_Block([]), self.B)

    # ---- Internal helpers for D1 bounds (bisect list emulating BST) ----
    def _append_d1_block(self, block: _Block, bound: float):
        """Append block to the right of D1 with given bound. Maintain bounds structures."""
        self.D1.append(block)
        # insert bound in sorted list
        ins_pos = bisect_right(self._d1_bounds, bound)
        self._d1_bounds.insert(ins_pos, bound)
        self._bound_to_block.setdefault(bound, []).append(block)

    def _remove_d1_block(self, block: _Block, bound: float):
        """Remove a D1 block and its bound entry (one occurrence)."""
        # remove block from deque (first occurrence)
        try:
            self.D1.remove(block)
        except ValueError:
            pass
        # remove one occurrence of bound and one mapping in dict
        if bound in self._bound_to_block:
            lst = self._bound_to_block[bound]
            if block in lst:
                lst.remove(block)
            if not lst:
                del self._bound_to_block[bound]
                # remove bound from _d1_bounds list (first occurrence)
                idx = bisect_left(self._d1_bounds, bound)
                # find exact match
                while idx < len(self._d1_bounds) and self._d1_bounds[idx] == bound:
                    self._d1_bounds.pop(idx)
                    break

    def _update_d1_bound(self, old_bound: float, block: _Block, new_bound: float):
        """Replace old bound mapping for this block with new_bound."""
        # remove old mapping occurrence
        if old_bound in self._bound_to_block and block in self._bound_to_block[old_bound]:
            self._bound_to_block[old_bound].remove(block)
            if not self._bound_to_block[old_bound]:
                del self._bound_to_block[old_bound]
                # remove bound from _d1_bounds
                idx = bisect_left(self._d1_bounds, old_bound)
                while idx < len(self._d1_bounds) and self._d1_bounds[idx] == old_bound:
                    self._d1_bounds.pop(idx)
                    break
        # insert new mapping
        ins_pos = bisect_right(self._d1_bounds, new_bound)
        self._d1_bounds.insert(ins_pos, new_bound)
        self._bound_to_block.setdefault(new_bound, []).append(block)

    def _find_d1_block_for_value(self, val) -> _Block:
        """Return the block in D1 whose upper_bound >= val with smallest such bound.
           If none exists, return the rightmost block (shouldn't happen often since last bound <= B).
        """
        if not self._d1_bounds:
            # shouldn't happen, fallback to leftmost block or create one
            if not self.D1:
                self._append_d1_block(_Block([]), self.B)
            return self.D1[0]
        idx = bisect_left(self._d1_bounds, val)
        if idx >= len(self._d1_bounds):
            # take last bound
            bound = self._d1_bounds[-1]
        else:
            bound = self._d1_bounds[idx]
        # get one available block for that bound
        blocks = self._bound_to_block.get(bound)
        if not blocks:
            # fallback: return leftmost block
            return self.D1[0]
        # return first block in list
        return blocks[0]

    # ---- Public operations ----
    def insert(self, key, value):
        """Insert or update a key/value pair into D1 as described in the lemma."""
        # if key exists, only proceed if value < old_value
        if key in self.key_map:
            old_value, block_ref, in_d0 = self.key_map[key]
            if value >= old_value:
                return  # nothing to do
            # delete old key first
            self._delete_key_from_block(key, old_value, block_ref, in_d0)
        # find block in D1 to insert: smallest upper_bound >= value
        block = self._find_d1_block_for_value(value)
        old_bound = block.upper_bound() if len(block) > 0 else None
        block.insert(key, value)
        # register mapping
        self.key_map[key] = (value, block, False)
        # update bound if increases
        new_bound = block.upper_bound() if len(block) > 0 else None
        if old_bound != new_bound:
            # if old_bound is None block was empty and wasn't in mapping; we append mapping
            if old_bound is None:
                # remove any existing mapping for None? we don't store None
                self._append_d1_block(block, new_bound)
            else:
                self._update_d1_bound(old_bound, block, new_bound)
        # if block too large, split at median
        if len(block) > self.M:
            left, right = block.split_median()
            # need to find and replace block in D1 bounds
            ob = old_bound if old_bound is not None else new_bound
            # remove old and insert left and right with their bounds
            self._remove_d1_block(block, ob)
            self._append_d1_block(left, left.upper_bound() if len(left) > 0 else self.B)
            self._append_d1_block(right, right.upper_bound() if len(right) > 0 else self.B)
            # update key_map references for items in left and right
            for (k, v) in left.items:
                self.key_map[k] = (v, left, False)
            for (k, v) in right.items:
                self.key_map[k] = (v, right, False)

    def _delete_key_from_block(self, key, old_value, block_ref: _Block, in_d0: bool):
        """Helper to remove key from the block it was stored in."""
        removed = block_ref.delete_key(key)
        # remove mapping entry handled by caller
        # if block_ref is in D1 and becomes empty, remove its bound
        if (not in_d0) and len(block_ref) == 0:
            # find its bound
            # naive method: scan bound_to_block to find block_ref
            found_bound = None
            for bnd, blks in list(self._bound_to_block.items()):
                if block_ref in blks:
                    found_bound = bnd
                    break
            if found_bound is not None:
                self._remove_d1_block(block_ref, found_bound)

    def delete(self, key):
        """Public delete(key) if present."""
        if key not in self.key_map:
            return False
        old_value, block_ref, in_d0 = self.key_map.pop(key)
        self._delete_key_from_block(key, old_value, block_ref, in_d0)
        return True

    def batch_prepend(self, pairs: List[Tuple]):
        """Insert L pairs where each value is smaller than any value currently in the structure.
           We must keep only the smallest value per key among pairs.
        """
        if not pairs:
            return
        # Keep smallest value per key in the batch
        best = {}
        for k, v in pairs:
            if k not in best or v < best[k]:
                best[k] = v
        items = [(k, best[k]) for k in best]
        # Sort by (value,key)
        items.sort(key=lambda kv: (kv[1], kv[0]))
        L = len(items)
        if L <= self.M:
            block = _Block(items)
            # prepend to D0
            self.D0.appendleft(block)
            for k, v in items:
                self.key_map[k] = (v, block, True)
            return
        # If L > M, create O(L/M) blocks each of size <= ceil(M/2) using recursive median splits.
        target = max(1, math.ceil(self.M / 2))
        # We'll partition items into chunks of size <= target preserving sorted order.
        # The proof suggests using medians repeatedly to achieve balanced blocks; here,
        # since items are sorted, slicing into chunks of size target yields blocks with desired sizes
        blocks = []
        for i in range(0, L, target):
            chunk = items[i:i+target]
            blocks.append(_Block(chunk))
        # prepend blocks in order (smallest values leftmost)
        for b in reversed(blocks):
            self.D0.appendleft(b)
        # update key_map for these
        for bi, b in enumerate(self.D0):
            for (k, v) in b.items:
                self.key_map[k] = (v, b, True)

    def pull(self):
        """
        Return S' (list of keys) with |S'| <= M of smallest values and separator x.
        Steps:
          - collect prefix blocks from D0 and D1 until >= M elements or blocks exhausted
          - select exactly M smallest among collected (or all if collected <= M)
          - remove them from their blocks and from key_map
          - compute x: B if no remaining elements, otherwise smallest remaining value
            and ensure max(S') < x <= min(D_remaining)
        """
        # collect prefix blocks from D0 and D1
        collected = []  # list of (key, value, block_ref, in_d0)
        count = 0
        d0_prefix = []
        for b in self.D0:
            if count >= self.M:
                break
            d0_prefix.append(b)
            count += len(b)
        d1_prefix = []
        for b in self.D1:
            if count >= self.M:
                break
            d1_prefix.append(b)
            count += len(b)
        # gather items (maintaining source block ref)
        for b in d0_prefix:
            for (k, v) in b.items:
                collected.append((k, v, b, True))
        for b in d1_prefix:
            for (k, v) in b.items:
                collected.append((k, v, b, False))
        if not collected:
            return [], self.B
        # if collected <= M, all collected are candidates and are the smallest overall
        if len(collected) <= self.M:
            # remove collected items from their blocks and key_map
            keys_out = []
            for k, v, bref, in_d0 in collected:
                # delete from block
                bref.delete_key(k)
                self.key_map.pop(k, None)
                keys_out.append(k)
            # remove empty D1 blocks and their bounds
            # scan bound_to_block to find empty blocks and remove them
            for bound, blks in list(self._bound_to_block.items()):
                for blk in list(blks):
                    if len(blk) == 0:
                        self._remove_d1_block(blk, bound)
            # compute x: smallest remaining value or B if none
            rem_min = None
            for b in self.D0:
                mv = b.min_value()
                if mv is not None and (rem_min is None or mv < rem_min):
                    rem_min = mv
            for b in self.D1:
                mv = b.min_value()
                if mv is not None and (rem_min is None or mv < rem_min):
                    rem_min = mv
            x = rem_min if rem_min is not None else self.B
            return keys_out, x
        # otherwise, we must pick exactly M smallest among collected
        # Use heapq.nsmallest on (value,key) to select exact M smallest
        smallest = heapq.nsmallest(self.M, collected, key=lambda t: (t[1], t[0]))
        keys_out = []
        # remove selected items from blocks and key_map
        for k, v, bref, in_d0 in smallest:
            # delete key from block (block may contain duplicates? No, we maintain unique keys)
            bref.delete_key(k)
            self.key_map.pop(k, None)
            keys_out.append(k)
        # clean up empty D1 blocks
        for bound, blks in list(self._bound_to_block.items()):
            for blk in list(blks):
                if len(blk) == 0:
                    self._remove_d1_block(blk, bound)
        # compute x: smallest remaining value in D0 or D1, or B if empty
        rem_min = None
        for b in self.D0:
            mv = b.min_value()
            if mv is not None and (rem_min is None or mv < rem_min):
                rem_min = mv
        for b in self.D1:
            mv = b.min_value()
            if mv is not None and (rem_min is None or mv < rem_min):
                rem_min = mv
        x = rem_min if rem_min is not None else self.B
        return keys_out, x

