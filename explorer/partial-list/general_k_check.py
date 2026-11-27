"""Cross-check for PLC-3: Noel's construction generalised to every k >= 3, l = k - 1.

Graph G_k (m = k - 1):
  * m terminals t_0..t_{m-1}, pairwise non-adjacent;
  * for every tuple f in [m]^m a clique K_k, vertices (f, 0..k-1); vertices 0 and 1 of each
    clique ("non-private") are joined to every terminal.
Bad m-lists: L(t_i) = {(i, a) : a < m};  every vertex of clique f gets {(i, f_i) : i < m}.

1. CP-SAT: the maximum partial colouring is exactly m^k + m - 1 (< n m / k).
2. Random k-list assignments (small colour universe) are all colourable.
"""
import itertools
import random
from ortools.sat.python import cp_model


def build(k):
    m = k - 1
    tuples = list(itertools.product(range(m), repeat=m))
    V = [("t", i) for i in range(m)] + [("c", f, j) for f in tuples for j in range(k)]
    E = []
    for f in tuples:
        for a in range(k):
            for b in range(a + 1, k):
                E.append((("c", f, a), ("c", f, b)))
        for j in (0, 1):
            for i in range(m):
                E.append((("t", i), ("c", f, j)))
    bad = {}
    for v in V:
        if v[0] == "t":
            bad[v] = [(v[1], a) for a in range(m)]
        else:
            bad[v] = [(i, v[1][i]) for i in range(m)]
    return V, E, bad


def solve(V, E, lists, maximise, limit=300):
    md = cp_model.CpModel()
    x = {(v, c): md.NewBoolVar("") for v in V for c in lists[v]}
    for v in V:
        s = sum(x[v, c] for c in lists[v])
        md.Add(s <= 1) if maximise else md.Add(s == 1)
    for a, b in E:
        for c in set(lists[a]) & set(lists[b]):
            md.Add(x[a, c] + x[b, c] <= 1)
    if maximise:
        md.Maximize(sum(x.values()))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = limit
    s.parameters.num_workers = 8
    st = s.Solve(md)
    if maximise:
        assert st == cp_model.OPTIMAL, st
        return int(s.ObjectiveValue())
    return st in (cp_model.OPTIMAL, cp_model.FEASIBLE)


if __name__ == "__main__":
    rng = random.Random(7)
    for k in (3, 4, 5):
        m = k - 1
        V, E, bad = build(k)
        n = len(V)
        best = solve(V, E, bad, True)
        print(f"k={k}: n={n}, max colourable={best}, formula={m**k + m - 1}, promised={n*m/k:.3f}")
        assert best == m ** k + m - 1 and best * k < n * m
        trials = {3: 3000, 4: 1000, 5: 100}[k]
        for _ in range(trials):
            U = rng.choice([k + 1, k + 2, 2 * k])
            L = {v: rng.sample(range(U), k) for v in V}
            assert solve(V, E, L, False, 60), (k, L)
        print(f"k={k}: {trials} random {k}-list assignments all colourable")
