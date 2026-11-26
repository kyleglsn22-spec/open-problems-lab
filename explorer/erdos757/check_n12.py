"""Independent exact check of the published n = 12 set for Erdős #757.

Set: 0 92 95 107 119 184 188 190 238 261 284 384
(from Suresh Kannan's certificates, c5b-erdos757-small-n/certificates/n12.txt).

Checks, by brute force over all subsets, with integer arithmetic only:
1. (4,5) property: every 4-subset B has at least 5 distinct positive differences,
   equivalently |B - B| >= 11 (B - B includes 0 and both signs), as in formal-conjectures.
2. Sidon (a + b = c + d with a <= b, c <= d forces {a,b} = {c,d}): the largest Sidon
   subset has exactly 7 elements, so every admissible c satisfies 12c <= 7.

Written from the definitions, without reading the original verify.py.
"""
from itertools import combinations

A = [0, 92, 95, 107, 119, 184, 188, 190, 238, 261, 284, 384]

def diff_set(B):
    return {x - y for x in B for y in B}

def is_sidon(S):
    seen = set()
    for i, a in enumerate(S):
        for b in S[i:]:          # includes a + a
            s = a + b
            if s in seen:
                return False
            seen.add(s)
    return True

assert len(set(A)) == 12
bad = [B for B in combinations(A, 4) if len(diff_set(B)) < 11]
assert not bad, bad
print("(4,5) property: all", len(list(combinations(A, 4))), "four-element subsets pass")

best = max(k for k in range(13) if any(is_sidon(list(S)) for S in combinations(A, k)))
assert best == 7, best
assert not any(is_sidon(list(S)) for S in combinations(A, 8))
print("largest Sidon subset:", best, "| no 8-element Sidon subset among",
      len(list(combinations(A, 8))))
print("so sup{admissible c} <= 7/12 =", 7 / 12, "< 3/5")
