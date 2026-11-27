"""Generalised skeleton ILP with a library of edge gadgets (k, p0, pb, pc, pbc  [interior values p'])
and vertex gadgets (k, p0, p1). Target ratio num/den. Feasible => planar graph with a(G) <= num/den * n.
"""
import sys, random
import networkx as nx
from ortools.sat.python import cp_model
from skel import induced_forests

R = (15, 8, 7, 7, 7)
Q = (12, 6, 6, 6, 5)


def solve(H, num, den, EG, VG, cap=8, tl=30, workers=4):
    h = H.number_of_nodes()
    E = list(H.edges())
    F = induced_forests(H)
    m = cp_model.CpModel()
    ev = {}
    for e in E:
        for gi, g in enumerate(EG):
            for o in (0, 1):
                if o == 1 and g[2] == g[3]:
                    continue
                ev[e, gi, o] = m.NewIntVar(0, cap, "")
    vv = {}
    for v in H:
        for gi, g in enumerate(VG):
            vv[v, gi] = m.NewIntVar(0, cap, "")
    for S in F:
        terms = [den * len(S) - num * h]
        for (e, gi, o), x in ev.items():
            k, p0, pb, pc, pbc = EG[gi]
            u, w = e if o == 0 else (e[1], e[0])
            iu, iw = u in S, w in S
            p = pbc if (iu and iw) else pb if iu else pc if iw else p0
            terms.append(x * (den * p - num * k))
        for (v, gi), x in vv.items():
            k, p0, p1 = VG[gi]
            p = p1 if v in S else p0
            terms.append(x * (den * p - num * k))
        m.Add(sum(terms) <= 0)
    m.Minimize(sum(ev.values()) + sum(vv.values()))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = tl
    s.parameters.num_workers = workers
    st = s.Solve(m)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol = {key: s.Value(x) for key, x in list(ev.items()) + list(vv.items()) if s.Value(x)}
        return sol
    return None
