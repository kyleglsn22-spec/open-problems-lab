"""Search connected block graphs for a large ratio chi_=(G) / L(G).

Lauri (arXiv 2608.14517) asks whether chi_=(G) <= C * L(G) for some constant C on connected block graphs;
his G_{2,7} shows C >= 9/7. Random block graphs: start from a clique, repeatedly attach a new clique of random
size at a random vertex. chi_= by SAT (pysat, cardinality constraints), L exactly (alpha(G, v) by SAT too).
"""
import itertools
import math
import random
import sys
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool


def random_block_graph(rng, nblocks, maxsize):
    sizes = [rng.randint(2, maxsize) for _ in range(nblocks)]
    n = sizes[0]
    blocks = [list(range(n))]
    for s in sizes[1:]:
        at = rng.randrange(n)
        new = list(range(n, n + s - 1))
        n += s - 1
        blocks.append([at] + new)
    return n, blocks


def adjacency(n, blocks):
    adj = [set() for _ in range(n)]
    for B in blocks:
        for a, b in itertools.combinations(B, 2):
            adj[a].add(b); adj[b].add(a)
    return adj


def alpha_at(n, adj, v):
    # block graphs are chordal; use SAT maximisation by binary search for simplicity
    best = 1
    lo, hi = 1, n
    while lo < hi:
        mid = (lo + hi + 1) // 2
        pool = IDPool(start_from=n + 1)
        s = Cadical153()
        s.add_clause([v + 1])
        for a in range(n):
            for b in adj[a]:
                if a < b:
                    s.add_clause([-(a + 1), -(b + 1)])
        enc = CardEnc.atleast(list(range(1, n + 1)), bound=mid, vpool=pool, encoding=EncType.seqcounter)
        s.append_formula(enc.clauses)
        if s.solve():
            lo = mid
        else:
            hi = mid - 1
    return lo


def L_of(n, adj, blocks):
    omega = max(len(B) for B in blocks)
    amin = min(alpha_at(n, adj, v) for v in range(n))
    return max(omega, -(-(n + 1) // (amin + 1))), omega, amin


def equitable(n, adj, q):
    lo, hi = n // q, -(-n // q)
    pool = IDPool()
    x = {(v, c): pool.id((v, c)) for v in range(n) for c in range(q)}
    s = Cadical153()
    for v in range(n):
        s.add_clause([x[v, c] for c in range(q)])
        for c1, c2 in itertools.combinations(range(q), 2):
            s.add_clause([-x[v, c1], -x[v, c2]])
        for w in adj[v]:
            if v < w:
                for c in range(q):
                    s.add_clause([-x[v, c], -x[w, c]])
    s.add_clause([x[0, 0]])  # symmetry
    for c in range(q):
        lits = [x[v, c] for v in range(n)]
        s.append_formula(CardEnc.atleast(lits, bound=lo, vpool=pool, encoding=EncType.seqcounter).clauses)
        s.append_formula(CardEnc.atmost(lits, bound=hi, vpool=pool, encoding=EncType.seqcounter).clauses)
    return s.solve()


def chi_eq(n, adj, start):
    q = start
    while not equitable(n, adj, q):
        q += 1
    return q


if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    rng = random.Random(seed)
    best = (0, None)
    for t in range(trials):
        nb = rng.randint(2, 9)
        ms = rng.randint(2, 7)
        n, blocks = random_block_graph(rng, nb, ms)
        if n > 40:
            continue
        adj = adjacency(n, blocks)
        L, om, am = L_of(n, adj, blocks)
        chi = chi_eq(n, adj, L)
        r = chi / L
        if r > best[0] or (chi - L >= 2) or r > 1.5:
            best = max(best, (r, None))
            print(f"trial {t}: n={n} L={L} (omega={om}, amin={am}) chi_=={chi} ratio={r:.4f} blocks={blocks}", flush=True)
