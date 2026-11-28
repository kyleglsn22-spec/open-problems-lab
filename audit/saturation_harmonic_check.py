"""Independent brute-force check of Gupta's Theorem 1 (arXiv:2606.15761): for the friendship
graph F_k, the minimum maximal matching has size k and H(F_k) = 2k/(k+1) + k/2 (exact)."""
from itertools import combinations
from fractions import Fraction

def F(k):
    V = ['z'] + [(i, b) for i in range(k) for b in (0, 1)]
    E = [frozenset(('z', (i, b))) for i in range(k) for b in (0, 1)] + \
        [frozenset(((i, 0), (i, 1))) for i in range(k)]
    return V, E

def min_maximal_matching(E):
    for size in range(len(E) + 1):
        for M in combinations(E, size):
            used = [v for e in M for v in e]
            if len(used) != len(set(used)):
                continue
            if all(e & set(used) for e in E):
                return size

for k in range(1, 7):
    V, E = F(k)
    deg = {v: sum(v in e for e in E) for v in V}
    H = sum(Fraction(2, sum(deg[v] for v in e)) for e in E)
    mu = min_maximal_matching(E)
    assert mu == k and H == Fraction(2 * k, k + 1) + Fraction(k, 2)
    print(f"k={k}: n={len(V)} mu*={mu} H={H} {'COUNTEREXAMPLE' if mu > H else 'ok'}")
    assert (mu > H) == (k >= 4)
print("all checks passed")
