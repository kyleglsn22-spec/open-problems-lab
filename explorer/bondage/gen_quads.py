"""Certificate generator for Lab/Bondage (Teschner's conjecture, Yavari arXiv:2609.04257).

1. Enumerates the 297 minimum dominating sets (size 6) of Yavari's graph.
2. Greedily picks 57 of them so that every multiset of 4 edge indices a <= b <= c <= d leaves
   one of them dominating (no bundle B(D, x) inside {a, b, c, d}).
3. Prints the `Ls` literal used in Lab/Bondage/Quads.lean.
The checks are split into Lab/Bondage/QPart*.lean, one theorem `checkQab a b` per pair a <= b,
grouped at most ~1500 quadruples per file and chained by imports (kernel memory).
"""
from itertools import combinations, combinations_with_replacement
V = range(18)
E = [(0,6),(0,10),(0,16),(1,8),(1,11),(1,12),(2,4),(2,5),(2,13),(3,4),(3,5),(3,9),(4,16),(5,11),
     (6,7),(6,13),(7,8),(7,14),(8,13),(9,10),(9,14),(10,15),(11,15),(12,15),(12,17),(14,17),(16,17)]
N = {v: {v} for v in V}
for u, w in E:
    N[u].add(w); N[w].add(u)
doms = [frozenset(D) for D in combinations(V, 6) if set().union(*(N[v] for v in D)) == set(V)]
assert len(doms) == 297
def bundles(D):
    return {x: [i for i, (u, w) in enumerate(E) if (u == x and w in D) or (w == x and u in D)]
            for x in V if x not in D}
B = {D: bundles(D) for D in doms}
def surv(D, F):
    return all(any(i not in F for i in b) for b in B[D].values())
quads = [set(q) for q in combinations_with_replacement(range(27), 4)]
rem, L = list(range(len(quads))), []
while rem:
    best = max(doms, key=lambda D: sum(surv(D, quads[j]) for j in rem))
    L.append(best)
    rem = [j for j in rem if not surv(best, quads[j])]
print(len(L), "sets")
for D in L:
    print(f"  ({sorted(D)}, [" + ", ".join(f"({x}, {b})" for x, b in B[D].items()) + "]),")
