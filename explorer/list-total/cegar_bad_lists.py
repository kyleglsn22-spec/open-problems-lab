"""Search for a bad list assignment for total colouring (CEGAR with two SAT solvers).

Given a graph G, a list size k and a palette {0..P-1}, look for lists L(x) = palette minus (P-k) colours,
one per vertex and edge, such that G has no total colouring from L.

Outer solver: variables o[x][c] ("c is omitted from L(x)"), exactly P-k omitted per element.
Inner solver: total colourings. Each time the inner solver finds a colouring col for the current
lists, the outer solver learns the clause OR_x o[x][col(x)] ("some element must lose its colour").
Outer UNSAT = every such list assignment is colourable (for this palette size).
Outer SAT with inner UNSAT = a bad list assignment, which is then printed.
"""
import itertools
import sys
import time
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool


def elements(V, E):
    return [("v", v) for v in V] + [("e", e) for e in E]


def conflicts(V, E):
    """Pairs of elements that must get different colours."""
    out = []
    for e in E:
        u, w = e[0], e[1]
        if (("v", u), ("v", w)) not in out:
            out.append((("v", u), ("v", w)))
        out.append((("v", u), ("e", e)))
        out.append((("v", w), ("e", e)))
    for e, f in itertools.combinations(E, 2):
        if set(e[:2]) & set(f[:2]):
            out.append((("e", e), ("e", f)))
    return out


def search(V, E, k, P, max_iter=10**7, sym=True, verbose=True):
    X = elements(V, E)
    C = conflicts(V, E)
    pool = IDPool()
    o = {(x, c): pool.id(("o", x, c)) for x in X for c in range(P)}
    y = {(x, c): pool.id(("y", x, c)) for x in X for c in range(P)}
    outer = Cadical153()
    inner = Cadical153()
    for x in X:
        enc = CardEnc.equals([o[x, c] for c in range(P)], bound=P - k, vpool=pool, encoding=EncType.seqcounter)
        outer.append_formula(enc.clauses)
        inner.add_clause([y[x, c] for c in range(P)])
    for (a, b) in C:
        for c in range(P):
            inner.add_clause([-y[a, c], -y[b, c]])
    if sym and P - k == 1:
        # colour symmetry: the omitted colour of the first element is 0
        outer.add_clause([o[X[0], 0]])
    it = 0
    t0 = time.time()
    while it < max_iter:
        it += 1
        if not outer.solve():
            if verbose:
                print(f"  all list assignments colourable (iterations {it}, {time.time()-t0:.1f}s)")
            return None
        m = set(l for l in outer.get_model() if l > 0)
        omit = {x: [c for c in range(P) if o[x, c] in m] for x in X}
        assum = [-y[x, c] for x in X for c in omit[x]]
        if not inner.solve(assumptions=assum):
            if verbose:
                print(f"  BAD LISTS found after {it} iterations, {time.time()-t0:.1f}s")
            return omit
        mi = set(l for l in inner.get_model() if l > 0)
        col = {x: next(c for c in range(P) if y[x, c] in mi and c not in omit[x]) for x in X}
        outer.add_clause([o[x, col[x]] for x in X])
        if verbose and it % 20000 == 0:
            print(f"  ... {it} iterations, {time.time()-t0:.1f}s", flush=True)
    return "timeout"


def noel():
    # four K_{2,3}; vertices (i, 'a'|'b'|k)
    V, E = [], []
    for i in range(4):
        V += [(i, "a"), (i, "b")] + [(i, j) for j in range(4) if j != i]
        for j in range(4):
            if j != i:
                E += [((i, "a"), (i, j)), ((i, "b"), (i, j))]
    for i, j in itertools.combinations(range(4), 2):
        E.append(((i, j), (j, i)))
    return V, E


def complete(n):
    V = list(range(n))
    return V, list(itertools.combinations(V, 2))


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "noel"
    if which == "noel":
        V, E = noel()
        print("Noel graph, k=4, P=5 (sanity check, expect BAD LISTS):")
        print(search(V, E, 4, 5) is not None)
    elif which.startswith("K"):
        n = int(which[1:])
        k = int(sys.argv[2]); P = int(sys.argv[3])
        V, E = complete(n)
        print(f"K_{n}, k={k}, P={P}:")
        r = search(V, E, k, P)
        print(r)


def complement_of_cycles(sizes):
    V, cyc, s = [], set(), 0
    for m in sizes:
        vs = list(range(s, s + m)); V += vs; s += m
        for i in range(m):
            cyc.add(frozenset((vs[i], vs[(i + 1) % m])))
    E = [(u, w) for u, w in itertools.combinations(V, 2) if frozenset((u, w)) not in cyc]
    return V, E


def chromatic_total(V, E, P):
    """Is G totally P-colourable? (plain colouring, all lists = palette)"""
    X = elements(V, E); C = conflicts(V, E)
    s = Cadical153(); pool = IDPool()
    y = {(x, c): pool.id((x, c)) for x in X for c in range(P)}
    for x in X:
        s.add_clause([y[x, c] for c in range(P)])
    for a, b in C:
        for c in range(P):
            s.add_clause([-y[a, c], -y[b, c]])
    return s.solve()


def fat_triangle(a, b, c):
    """Multigraph on {0,1,2} with a, b, c parallel edges on 01, 12, 02 (edges are (u, w, index))."""
    E = [(0, 1, i) for i in range(a)] + [(1, 2, i) for i in range(b)] + [(0, 2, i) for i in range(c)]
    return [0, 1, 2], E
