"""Independent brute-force check of Wang's H_{t,r} (arXiv:2608.19455) against the
Henning-Yeo bound tau_D <= (D(D-1)n + 2m)/(D^2+1). Exact integers only."""
from itertools import combinations
from fractions import Fraction

def H(t, r):
    V = ['a', 'b'] + [f'x{i}' for i in range(t)] + [f'c{j}' for j in range(r)] + [f'd{j}' for j in range(r)]
    E = set()
    for i in range(t):
        E |= {frozenset(('a', f'x{i}')), frozenset(('b', f'x{i}'))}
    for j in range(r):
        E |= {frozenset(('a', f'c{j}')), frozenset((f'c{j}', f'd{j}')), frozenset((f'd{j}', 'b'))}
    for i, j in combinations(range(r), 2):
        E.add(frozenset((f'd{i}', f'd{j}')))
    return V, E

def is_idcover(E, T):
    traces = [e & T for e in E]
    return all(traces) and len(set(traces)) == len(traces)

def tau_D(V, E):
    for k in range(len(V) + 1):
        for T in combinations(V, k):
            if is_idcover(E, frozenset(T)):
                return k

for t in range(2, 6):
    for r in range(2, 6):
        V, E = H(t, r)
        n, m = len(V), len(E)
        deg = {v: sum(v in e for e in E) for v in V}
        D = max(deg.values())
        tau = tau_D(V, E)
        bound = Fraction(D * (D - 1) * n + 2 * m, D * D + 1)
        assert D == t + r and tau == n - 1 and 2 * m == 4 * t + 5 * r + r * r
        assert D * (D - 1) * n + 2 * m - (D * D + 1) * tau == -(t - 1) * (r - 1)
        assert tau > bound
        print(f"t={t} r={r}: n={n} m={m} Delta={D} tau_D={tau} bound={bound} (violated)")
print("all checks passed")
