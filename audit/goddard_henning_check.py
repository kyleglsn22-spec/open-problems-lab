"""Independent check of Kwon-Park-Sano (arXiv:2611.00572, Theorem 1.2, n = 36): the triangulation B
glued from three copies of G14 has no partner colouring, i.e. no partition into two total
dominating sets that both induce bipartite subgraphs. Builds B from the paper's G14 edge list,
then (1) checks the edge list in Lab/TotalDomination/Basic.lean is B up to the same labelling,
(2) checks 3n - 6 edges, (3) enumerates all proper 4-colourings and counts partner colourings
(every vertex has a neighbour of its partner colour; pairs {0,1}, {2,3}). By the paper's Prop. 2.3
this is the same as the partition form. G14's edge list is copied from the paper's TikZ source."""
import re, itertools
G14 = [(0,1),(0,2),(0,7),(0,3),(0,4),(0,5),(0,6),(1,2),(1,7),(1,8),(1,9),(2,3),(2,8),(2,10),(2,11),
       (3,4),(3,11),(4,5),(4,11),(4,12),(5,6),(5,12),(6,7),(6,10),(6,12),(6,13),(7,9),(7,13),(8,9),
       (8,10),(8,13),(9,13),(10,11),(10,12),(10,13),(11,12)]
glue = {(1,0):'a',(2,1):'a',(3,0):'a',(1,1):'b',(2,0):'b',(3,2):'b',(1,2):'z2',(2,2):'z2',(2,7):'z3',(3,1):'z3'}
V = {}
def vid(i, j):
    k = glue.get((i, j), (i, j))
    return V.setdefault(k, len(V))
E = set()
for i in (1, 2, 3):
    for j in range(14): vid(i, j)
for i in (1, 2, 3):
    gone = {0, 1} if i < 3 else {0, 2}
    for x, y in G14:
        if {x, y} != gone: E.add(frozenset((vid(i, x), vid(i, y))))
E.add(frozenset((V['a'], V['b'])))
n = len(V)
src = open('Lab/TotalDomination/Basic.lean').read()
lean_edges = {frozenset(map(int, p)) for p in re.findall(r'\((\d+), (\d+)\)', src.split('def edges')[1].split(':=')[1].split(']')[0])}
print("n =", n, "edges =", len(E), "3n-6 =", 3 * n - 6, "matches Lean list:", lean_edges == E)
adj = {v: set() for v in range(n)}
for e in E:
    u, v = tuple(e); adj[u].add(v); adj[v].add(u)
order = [0]
while len(order) < n:
    order.append(max((v for v in range(n) if v not in order), key=lambda v: len(adj[v] & set(order))))
c = {}; proper = partner = 0
def go(k):
    global proper, partner
    if k == n:
        proper += 1
        # side = colour // 2, partner colour = colour ^ 1
        if all(any(c[u] == c[v] ^ 1 for u in adj[v]) for v in range(n)): partner += 1
        return
    v = order[k]
    for col in range(4):
        if all(c.get(u) != col for u in adj[v]):
            c[v] = col; go(k + 1); del c[v]
go(0)
print("proper 4-colourings:", proper, "partner colourings:", partner)
assert len(E) == 3 * n - 6 and lean_edges == E and partner == 0
print("OK")
