"""Independent exact check of the Ma–Tang 14-point set for Erdős #757 (arXiv:2602.23282).

Set: 0 136 200 243 246 249 272 286 298 323 400 528 596 1056

Checks, by brute force with integer arithmetic only:
1. (4,5) property: every 4-subset B has |B - B| >= 11 (at least 5 distinct positive differences).
2. The largest Sidon subset has exactly 8 elements, so every admissible c satisfies 14c <= 8,
   i.e. c <= 4/7.
3. The 3-term progressions listed in Lab/Erdos757/FourSevenths.lean are all of them, and every
   9-subset contains one (the fact the Lean proof relies on).
"""
from itertools import combinations

A = [0, 136, 200, 243, 246, 249, 272, 286, 298, 323, 400, 528, 596, 1056]
AP_LEAN = [(0, 272, 136), (0, 400, 200), (0, 596, 298), (0, 1056, 528), (136, 1056, 596),
           (200, 286, 243), (200, 298, 249), (243, 249, 246), (246, 298, 272), (246, 400, 323),
           (249, 323, 286), (272, 528, 400)]


def is_sidon(S):
    sums = set()
    for i, a in enumerate(S):
        for b in S[i:]:
            if a + b in sums:
                return False
            sums.add(a + b)
    return True


assert len(set(A)) == 14
assert all(len({x - y for x in B for y in B}) >= 11 for B in combinations(A, 4))
assert any(is_sidon(S) for S in combinations(A, 8))
assert not any(is_sidon(S) for S in combinations(A, 9))
aps = [(a, b, c) for a in A for b in A for c in A if a < c < b and a + b == 2 * c]
assert sorted(aps) == sorted(AP_LEAN)
assert all(any(set(t) <= set(B) for t in AP_LEAN) for B in combinations(A, 9))
print("OK: (4,5)-set, largest Sidon subset 8, so c <= 8/14 = 4/7")
