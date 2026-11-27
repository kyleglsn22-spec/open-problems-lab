"""1-sum gadgets for Chappell-Pelsmajer: glue m copies of a triangulation J at vertex v.
g(t) = max # interior vertices (excluding v) in an induced forest with v in S, forest max degree <= d
       and v's forest-degree <= t.   p0 = max interior forest with v out (degree<=d).
f_d(m-fold sum) = max(m*p0, 1 + max_{t_1+..+t_m <= d} sum g(t_i)).
Report cases where f_d <= 2dn/(4d+1)."""
import sys, random
from fractions import Fraction
import networkx as nx
from ortools.sat.python import cp_model
from anneal_tri import random_triangulation, flip
from fd import find_cycle


def fd_v(G, d, v, vin, t=None):
    tri = [c for c in nx.enumerate_all_cliques(G) if len(c) == 3]
    cuts = []
    while True:
        m = cp_model.CpModel()
        x = {u: m.NewBoolVar("") for u in G}
        for c in tri:
            m.Add(sum(x[u] for u in c) <= 2)
        for c in cuts:
            m.Add(sum(x[u] for u in c) <= len(c) - 1)
        for u in G:
            nb = list(G[u])
            if len(nb) > d:
                m.Add(sum(x[w] for w in nb) <= d).OnlyEnforceIf(x[u])
        m.Add(x[v] == int(vin))
        if vin and t is not None:
            m.Add(sum(x[w] for w in G[v]) <= t)
        m.Maximize(sum(x.values()))
        s = cp_model.CpSolver(); s.parameters.num_workers = 1
        r = s.Solve(m)
        if r == cp_model.INFEASIBLE:
            return None
        S = [u for u in G if s.Value(x[u])]
        if find_cycle(G, S) is None:
            return len(S) - int(vin)
        cuts += nx.cycle_basis(G.subgraph(S))


def best_sum(g, d, m):
    # knapsack: m copies, each picks t in 0..d, total <= d
    best = {0: 0}
    for _ in range(m):
        nb = {}
        for used, val in best.items():
            for t in range(0, d - used + 1):
                if g[t] is None:
                    continue
                nv = val + g[t]
                if nb.get(used + t, -1) < nv:
                    nb[used + t] = nv
        best = nb
    return max(best.values())


def main():
    nmin, nmax, iters, seed = map(int, sys.argv[1:5])
    rng = random.Random(seed)
    seen = set()
    bestr = {d: None for d in range(2, 7)}
    for it in range(iters):
        n = rng.randint(nmin, nmax)
        J = random_triangulation(n, rng)
        for _ in range(rng.randint(3, 50)):
            J = flip(J, rng)
        key = nx.weisfeiler_lehman_graph_hash(J, iterations=4)
        if key in seen:
            continue
        seen.add(key)
        done = set()
        for v in J:
            sig = (J.degree(v), tuple(sorted(J.degree(u) for u in J[v])))
            if sig in done:
                continue
            done.add(sig)
            for d in range(2, 7):
                p0 = fd_v(J, d, v, False)
                g = [fd_v(J, d, v, True, t) for t in range(d + 1)]
                for mm in range(1, 3 * d + 3):
                    N = 1 + mm * (n - 1)
                    f = max(mm * p0, 1 + best_sum(g, d, mm))
                    r = Fraction(f * (4 * d + 1), 2 * d * N)  # <=1 means counterexample
                    if bestr[d] is None or r < bestr[d][0]:
                        bestr[d] = (r, n, mm, N, f, p0, g, nx.to_graph6_bytes(J, header=False).decode().strip(), v)
                        print("d", d, "score", float(r), bestr[d], flush=True)
    print(bestr)


if __name__ == '__main__':
    main()
