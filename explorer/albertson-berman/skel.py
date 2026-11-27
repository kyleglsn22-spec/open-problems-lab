"""Skeleton + edge-gadget ILP.
Skeleton H planar on h vertices. On each edge e we glue m_e copies of R (15 interior
vertices; interior forest value 8, minus 1 if S touches e) and q_e copies of Q (12 interior;
value 6, minus 1 if both ends of e in S).  a(G) = 8M + 6Q' + max_S(|S| - sum m_e t_e - sum q_e b_e)
over induced forests S of H.  n = h + 15M + 12Q'.
Find integer m,q with a(G) <= (num/den) n.
usage: skel.py num den hmax"""
import sys, itertools, random
import networkx as nx
from ortools.sat.python import cp_model

sys.setrecursionlimit(10000)


def induced_forests(H):
    V = list(H)
    idx = {v: i for i, v in enumerate(V)}
    res = []
    for mask in range(1 << len(V)):
        S = [V[i] for i in range(len(V)) if mask >> i & 1]
        sub = H.subgraph(S)
        if sub.number_of_edges() <= len(S) - 1 and nx.is_forest(sub) if S else True:
            res.append(set(S))
    return res


def solve(H, num, den, cap=12, tl=20):
    h = H.number_of_nodes()
    E = list(H.edges())
    F = induced_forests(H)
    m = cp_model.CpModel()
    r = {e: m.NewIntVar(0, cap, f"r{e}") for e in E}
    q = {e: m.NewIntVar(0, cap, f"q{e}") for e in E}
    # per-gadget slack coefficients: R: den*8 - num*15 ; Q: den*6 - num*12
    cR = den * 8 - num * 15
    cQ = den * 6 - num * 12
    for S in F:
        expr = den * len(S)
        terms = []
        for e in E:
            t = (e[0] in S) or (e[1] in S)
            b = (e[0] in S) and (e[1] in S)
            terms.append(r[e] * (cR - den * t))
            terms.append(q[e] * (cQ - den * b))
        m.Add(expr + sum(terms) <= num * h)
    m.Minimize(sum(r.values()) + sum(q.values()))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = tl
    s.parameters.num_workers = 4
    st = s.Solve(m)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return {e: (s.Value(r[e]), s.Value(q[e])) for e in E}
    return None


if __name__ == '__main__':
    num, den, hmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    from anneal_tri import random_triangulation, flip
    rng = random.Random(1)
    for h in range(4, hmax + 1):
        seen = set()
        G = random_triangulation(h, rng)
        tries = 0
        for it in range(4000):
            G = flip(G, rng)
            if it % 300 == 0:
                G = random_triangulation(h, rng)
            key = nx.weisfeiler_lehman_graph_hash(G, iterations=4)
            if key in seen:
                continue
            seen.add(key)
            sol = solve(G, num, den)
            tries += 1
            if sol:
                M = sum(a for a, b in sol.values()); Qc = sum(b for a, b in sol.values())
                print("FOUND h", h, nx.to_graph6_bytes(G, header=False).decode().strip(),
                      {e: v for e, v in sol.items() if v != (0, 0)}, "n=", h + 15 * M + 12 * Qc, flush=True)
        print("h", h, "graphs", tries, flush=True)
