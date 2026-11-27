"""Cross-check for PLC-2 (connected chain of t copies of Noel's graph).

Vertices (j, v), j < t, v < 14, numbered as in Lab/PartialList/Counterexample.lean.
Inside each copy: Noel's graph. Between copies: (j, 2) -- (j + 1, 3).

1. Exact maximum partial colouring from Noel's lists (CP-SAT): expect 9 t.
2. Random 3-list assignments (small colour universe, so lists overlap a lot) are all
   colourable: a sanity check of the 3-choosability that Lean proves for all lists.

Run: python3 connected_check.py   (needs ortools)
"""
import random
from ortools.sat.python import cp_model


def noel_adj(u, v):
    if u == v:
        return False
    if u < 2:
        return v >= 2 and (v - 2) % 3 != 0
    if v < 2:
        return (u - 2) % 3 != 0
    return (u - 2) // 3 == (v - 2) // 3


def chain_edges(t):
    E = [((j, u), (j, v)) for j in range(t) for u in range(14) for v in range(u + 1, 14)
         if noel_adj(u, v)]
    E += [((j, 2), (j + 1, 3)) for j in range(t - 1)]
    return E


def noel_list(v):
    if v == 0:
        return [1, 2]
    if v == 1:
        return [3, 4]
    i = (v - 2) // 3
    return [1 + i // 2, 3 + i % 2]


def solve(t, lists, maximise):
    m = cp_model.CpModel()
    V = [(j, v) for j in range(t) for v in range(14)]
    x = {(a, c): m.NewBoolVar("") for a in V for c in lists[a]}
    for a in V:
        m.Add(sum(x[a, c] for c in lists[a]) <= 1 if maximise else
              sum(x[a, c] for c in lists[a]) == 1)
    for a, b in chain_edges(t):
        for c in set(lists[a]) & set(lists[b]):
            m.Add(x[a, c] + x[b, c] <= 1)
    if maximise:
        m.Maximize(sum(x.values()))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = 120
    st = s.Solve(m)
    if maximise:
        assert st == cp_model.OPTIMAL
        return int(s.ObjectiveValue())
    return st in (cp_model.OPTIMAL, cp_model.FEASIBLE)


if __name__ == "__main__":
    for t in range(1, 6):
        L = {(j, v): noel_list(v) for j in range(t) for v in range(14)}
        best = solve(t, L, True)
        print(f"t={t}: n={14*t}, max colourable={best}, promised={28*t/3:.2f}, gap={28*t/3-best:.2f}")
        assert best == 9 * t
    rng = random.Random(1)
    for t in (2, 3):
        for trial in range(3000):
            U = rng.choice([4, 5, 6, 7])
            L = {(j, v): rng.sample(range(U), 3) for j in range(t) for v in range(14)}
            assert solve(t, L, False), (t, L)
        print(f"t={t}: 3000 random 3-list assignments all colourable")
