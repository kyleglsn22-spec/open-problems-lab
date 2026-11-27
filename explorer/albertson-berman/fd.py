"""Max induced forest with max degree <= d (f_d) via CP-SAT + lazy cycle cuts.
d=None means no degree bound (a(G))."""
import networkx as nx
from ortools.sat.python import cp_model


def find_cycle(G, S):
    H = G.subgraph(S)
    try:
        c = nx.find_cycle(H)
        return [u for u, v in c]
    except nx.NetworkXNoCycle:
        return None


def fd(G, d=None, fixed=None, cuts=None, time_limit=60):
    """Return (value, set). fixed: dict v->0/1. cuts: list of cycles (shared, grows)."""
    if cuts is None:
        cuts = [list(t) for t in nx.cycle_basis(G)] if False else []
    # always add all triangles
    tri = [c for c in nx.enumerate_all_cliques(G) if len(c) == 3]
    while True:
        m = cp_model.CpModel()
        x = {v: m.NewBoolVar(str(v)) for v in G}
        for c in tri:
            m.Add(sum(x[v] for v in c) <= 2)
        for c in cuts:
            m.Add(sum(x[v] for v in c) <= len(c) - 1)
        if d is not None:
            for v in G:
                nb = list(G[v])
                if len(nb) > d:
                    m.Add(sum(x[u] for u in nb) <= d).OnlyEnforceIf(x[v])
        if fixed:
            for v, b in fixed.items():
                m.Add(x[v] == b)
        m.Maximize(sum(x.values()))
        s = cp_model.CpSolver()
        s.parameters.max_time_in_seconds = time_limit
        import os; s.parameters.num_workers = int(os.environ.get("FD_W","4"))
        r = s.Solve(m)
        if r not in (cp_model.OPTIMAL,):
            if r == cp_model.INFEASIBLE:
                return None, None
            raise RuntimeError("not optimal")
        S = [v for v in G if s.Value(x[v])]
        c = find_cycle(G, S)
        if c is None:
            return len(S), S
        # add all cycles in a cycle basis of induced subgraph for speed
        for cyc in nx.cycle_basis(G.subgraph(S)):
            cuts.append(cyc)


def icosahedron():
    return nx.icosahedral_graph()


if __name__ == "__main__":
    G = icosahedron()
    for d in [2, 3, 4, None]:
        print(d, fd(G, d)[0])
