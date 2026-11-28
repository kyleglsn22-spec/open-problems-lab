"""Search for connected, non-bipartite, vertex-determining, ASYMMETRIC graphs with a two-fold automorphism
(alpha != beta) and no odd k with both C_k and C_2k as (not necessarily induced) subgraph cycles."""
import sys, random, itertools, networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
seed, nmin, nmax, iters = map(int, sys.argv[1:5])
rng = random.Random(seed)

def rand_perm(n, kind):
    p = list(range(n))
    if kind == 'inv':
        k = rng.randint(1, n // 2); pts = rng.sample(range(n), 2 * k)
        for i in range(k): a, b = pts[2*i], pts[2*i+1]; p[a], p[b] = b, a
    else:
        rng.shuffle(p)
    return p

def orbits(n, al, be):
    seen = set(); orbs = []
    for u in range(n):
        for v in range(n):
            if (u, v) in seen: continue
            orb = set(); st = [(u, v)]
            while st:
                x = st.pop()
                if x in orb: continue
                orb.add(x); st.append((al[x[0]], be[x[1]])); st.append((x[1], x[0]))
            seen |= orb
            if any(a == b for a, b in orb): continue
            orbs.append(orb)
    return orbs

def asymmetric(G):
    gm = GraphMatcher(G, G)
    c = 0
    for _ in gm.isomorphisms_iter():
        c += 1
        if c > 1: return False
    return True

def cycle_lengths(G, maxlen):
    L = set()
    for c in nx.simple_cycles(G, length_bound=maxlen):
        L.add(len(c))
    return L

def tf_ok(G, al, be, n):
    return all((G.has_edge(u, v) == G.has_edge(al[u], be[v])) for u in range(n) for v in range(n))

tested = 0
asym = 0
for it in range(iters):
    n = rng.randint(nmin, nmax)
    al = rand_perm(n, rng.choice(['inv','perm'])); be = rand_perm(n, rng.choice(['inv','perm']))
    if al == be: continue
    orbs = orbits(n, al, be)
    p = rng.uniform(0.1, 0.6)
    E = set()
    for o in orbs:
        if rng.random() < p:
            for a, b in o: E.add((min(a, b), max(a, b)))
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E)
    if G.number_of_edges() > 4 * n or not nx.is_connected(G) or nx.is_bipartite(G): continue
    nb = [frozenset(G[v]) for v in range(n)]
    if len(set(nb)) < n: continue
    tested += 1
    if tested % 2000 == 0: print('it', it, 'tested', tested, 'asym', asym, flush=True)
    if not asymmetric(G): continue
    asym += 1
    L = cycle_lengths(G, n)
    if any(k in L and 2 * k in L for k in range(3, n + 1, 2)): continue
    assert tf_ok(G, al, be, n)
    print('FOUND n', n, 'edges', sorted(E), 'alpha', al, 'beta', be, 'cycles', sorted(L), flush=True)
    if tested % 1000 == 0: pass
print('done tested', tested, 'asym', asym, flush=True)
