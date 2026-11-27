"""Cross-check for LTC-2: Noel's List Total Colouring counterexample generalised to every d >= 3.

G_d: blocks B_0..B_d, each a copy of K_{d-1,d}: private vertices A_i (d-1 of them) and terminals
v_{i,j} (j != i). One cross edge v_{i,j} -- v_{j,i} for each pair i < j. G_d is d-regular,
n = (d+1)(2d-1).

1. An explicit total colouring with d+1 colours (private vertices and cross edges get colour d;
   terminal v_{i,j} gets M[i][j] = (rank of j among indices != i) + i mod d, so each block's terminals are
   a permutation of Z_d and M[i][j] - M[j][i] = -1 or 1; the edge v_{i,j} a_m gets M[i][j] + m + 1 mod d).
   Verified. Same colouring as `colT` in Lab/ListTotal/General.lean.
2. Bad (d+1)-lists from {0..d+1}: everything in block i gets {0..d+1} minus {i}; cross edge {j,k} gets
   {0..d+1} minus om(j,k), where every colour t is omitted by some edge not touching block t
   (same lists as `L` in Lab/ListTotal/General.lean).
   CP-SAT confirms there is no total colouring from these lists for d = 3, 4, 5 (d = 6 does not finish in
   10 minutes; the Lean proof covers every d).
"""
import itertools
import sys
from ortools.sat.python import cp_model


def build(d):
    n = d + 1
    V = []
    for i in range(n):
        V += [("a", i, m) for m in range(d - 1)] + [("v", i, j) for j in range(n) if j != i]
    E = []
    for i in range(n):
        for m in range(d - 1):
            for j in range(n):
                if j != i:
                    E.append((("a", i, m), ("v", i, j)))
    for i, j in itertools.combinations(range(n), 2):
        E.append((("v", i, j), ("v", j, i)))
    return V, E


def term_matrix(d):
    """Same as `Mc` in Lab/ListTotal/General.lean: M[i][j] = (rk(i, j) + i) mod d,
    where rk(i, j) is the position of j among the indices != i."""
    n = d + 1
    M = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j:
                rk = j if j < i else j - 1
                M[i][j] = (rk + i) % d
    return M


def explicit_colouring(d):
    n = d + 1
    V, E = build(d)
    M = term_matrix(d)
    col = {}
    for x in V:
        col[x] = d if x[0] == "a" else M[x[1]][x[2]]
    for (u, w) in E:
        if u[0] == "a":
            m = u[2]
            col[(u, w)] = (M[w[1]][w[2]] + m + 1) % d
        else:
            col[(u, w)] = d
    return V, E, col


def check_total(V, E, col):
    inc = {x: [] for x in V}
    for e in E:
        u, w = e
        if col[u] == col[w] or col[e] in (col[u], col[w]):
            return False
        inc[u].append(e)
        inc[w].append(e)
    for x in V:
        cs = [col[e] for e in inc[x]]
        if len(set(cs)) != len(cs):
            return False
    return True


def om(d, a, b):
    """Same as `om` in Lab/ListTotal/General.lean (with d = n + 3)."""
    p, q = min(a, b), max(a, b)
    if 1 <= p and q == p + 1:
        return p - 1
    if p == 0 and q == d:
        return d - 1
    if p == 0 and q == 1:
        return d
    return d + 1


def omit_map(d):
    """{t+1, t+2} omits t (t <= d-2), {0, d} omits d-1, {0, 1} omits d, all others omit d+1."""
    return {(j, k): om(d, j, k) for j, k in itertools.combinations(range(d + 1), 2)}


def bad_lists_colourable(d):
    n = d + 1
    V, E = build(d)
    om = omit_map(d)
    pal = set(range(d + 2))
    L = {}
    for x in V:
        L[x] = pal - {x[1]}
    for e in E:
        u, w = e
        if u[0] == "v" and w[0] == "v":
            L[e] = pal - {om[tuple(sorted((u[1], w[1])))]}
        else:
            L[e] = pal - {u[1]}
    md = cp_model.CpModel()
    X = {(z, c): md.NewBoolVar("") for z in L for c in L[z]}
    for z in L:
        md.AddExactlyOne(X[z, c] for c in L[z])
    inc = {x: [] for x in V}
    for e in E:
        u, w = e
        inc[u].append(e); inc[w].append(e)
        for c in pal:
            for a, b in ((u, w), (u, e), (w, e)):
                if c in L[a] and c in L[b]:
                    md.AddBoolOr([X[a, c].Not(), X[b, c].Not()])
    for x in V:
        for c in pal:
            lits = [X[e, c] for e in inc[x] if c in L[e]]
            if len(lits) > 1:
                md.AddAtMostOne(lits)
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = 600
    s.parameters.num_workers = 8
    st = s.Solve(md)
    return st, s.StatusName(st)


if __name__ == "__main__":
    for d in range(3, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 6):
        V, E, col = explicit_colouring(d)
        ok = check_total(V, E, col)
        st, name = bad_lists_colourable(d)
        print(f"d={d}: n={len(V)}, explicit {d+1}-total-colouring valid={ok}, bad lists solver: {name}")
        assert ok and name == "INFEASIBLE"
