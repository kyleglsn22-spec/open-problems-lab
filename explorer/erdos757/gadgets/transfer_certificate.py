r"""All-K Sidon-subset bound for a self-similar chain S_K = O ∪ φ(O) ∪ ... ∪ φ^K(O)  (Erdős #757).

Setting: O is a (4,5)-set, a = min O, b = max O, p, q ∈ O interior, and φ is the affine map with
φ(a) = p, φ(b) = q, so copy k+1 meets copy k exactly in the pair φ^k(p), φ^k(q).
No geometric assumption is needed for the upper bound: the trace of a Sidon subset of S_K on every
copy is Sidon, and |I| <= |J_0| + sum_k |J_k minus the shared pair| (union bound). The geometric half
(|S_K| = 11 + 9K, S_K a (4,5)-set) is needed only to turn this into c <= 5/9.

Certificate: a potential π on the four states of a pair (neither / only second / only first / both)
and constants G, C with
  (per copy)   |J \ {a,b}| ≤ G + π(state of J on (p,q)) − π(state of J on (a,b))
  (first copy) |J|         ≤ C + π(state of J on (p,q))
for every Sidon subset J of O.  Summing over the copies telescopes:
  h(S_K) ≤ C + G·K + max π.
Pure Python, exact integers, brute force over all subsets of O.
"""
from itertools import combinations

def three_aps(A):
    S = set(A)
    return [frozenset((x, (x + z) // 2, z)) for x, z in combinations(sorted(A), 2)
            if (x + z) % 2 == 0 and (x + z) // 2 in S]

def check(O, p, q, pi, G, C):
    a, b = min(O), max(O)
    E = three_aps(O)
    st = lambda J, u, v: 2 * (u in J) + (v in J)
    worst_copy = worst_first = None
    for r in range(len(O) + 1):
        for J in combinations(O, r):
            J = set(J)
            if any(e <= J for e in E):
                continue  # not Sidon (in a (4,5)-set, Sidon = contains no 3-AP)
            lhs = len(J - {a, b}); rhs = G + pi[st(J, p, q)] - pi[st(J, a, b)]
            if lhs > rhs:
                return False, ("per-copy", sorted(J))
            if len(J) > C + pi[st(J, p, q)]:
                return False, ("first-copy", sorted(J))
    return True, None

if __name__ == "__main__":
    # Reader's family (erdosproblemaday.com 7bkzb8): ports 101, 119
    O = [0, 49, 75, 83, 98, 101, 117, 119, 121, 159, 269]
    ok, bad = check(O, 101, 119, pi=[0, 1, 1, 1], G=5, C=6)
    print("5/9 family certificate:", ok, bad or "")
    print("=> h(S_K) <= 6 + 5K + 1 = 7 + 5K, |S_K| = 11 + 9K  (ratio -> 5/9)")
