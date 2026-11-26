"""Independent check (not using the paper's argument) that the GGWZ sequence is zero-sumfree.

A sub-multiset is a count c_g <= multiplicity(g) for each distinct element g. We ask CP-SAT for
counts, not all zero, with sum_g c_g * g = 0 (mod n) in every coordinate. INFEASIBLE means the
sequence is zero-sumfree. Controls: adding one more copy of several elements must make it feasible.

Usage: python3 check_cpsat.py K   (K odd >= 3, n = 2K, rank 5K)
"""
import collections
import sys

from ortools.sat.python import cp_model

from build import build


def has_zero_sum(n, R, S):
    cnt = collections.Counter(S)
    G = list(cnt)
    m = cp_model.CpModel()
    c = {g: m.NewIntVar(0, cnt[g], "") for g in G}
    for j in range(R):
        q = m.NewIntVar(-10**6, 10**6, "")
        m.Add(sum(c[g] * g[j] for g in G) == n * q)
    m.Add(sum(c.values()) >= 1)
    s = cp_model.CpSolver()
    s.parameters.num_workers = 4
    return s.StatusName(s.Solve(m))


if __name__ == "__main__":
    k = int(sys.argv[1])
    n, R, S = build(k)
    print(f"n={n} rank={R} length={len(S)} (conjecture bound R(n-1) = {R*(n-1)})")
    print("zero-sum subsequence exists?", has_zero_sum(n, R, S), "(INFEASIBLE = zero-sumfree)")
    for g in [S[0], S[1], S[-1], S[-3]]:
        print("control, one extra copy of", g, "->", has_zero_sum(n, R, S + [g]))
