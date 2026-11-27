"""Independent cross-check of Noel's Partial List Colouring counterexample (arXiv:2609.23291).

Same vertex numbering as Lab/PartialList/Counterexample.lean: 0, 1 are the terminals s1, s2;
triangle i (i = 0..3) is {3i+2 (private), 3i+3, 3i+4}. Checks, by brute force over all
3^14 partial colourings (each vertex: uncoloured or one of its two colours), that the largest
properly coloured set has exactly 9 vertices, and that 9 * 3 < 14 * 2.
"""
import itertools

n = 14
edges = set()
for i in range(4):
    p, u, w = 3 * i + 2, 3 * i + 3, 3 * i + 4
    edges |= {(p, u), (p, w), (u, w)}
    for s in (0, 1):
        edges |= {(s, u), (s, w)}
adj = [[False] * n for _ in range(n)]
for a, b in edges:
    adj[a][b] = adj[b][a] = True
assert len(edges) == 28

tri_lists = [(1, 3), (1, 4), (2, 3), (2, 4)]
L = [(1, 2), (3, 4)] + [tri_lists[(v - 2) // 3] for v in range(2, n)]

# Brute force, vertex by vertex, with pruning on conflicts (exact, exhaustive).
best = 0
def search(v, col, count):
    global best
    if count + (n - v) <= best:
        return
    if v == n:
        best = max(best, count)
        return
    for c in L[v]:
        if all(not (adj[v][x] and col[x] == c) for x in range(v)):
            col[v] = c
            search(v + 1, col, count + 1)
    col[v] = None
    search(v + 1, col, count)

search(0, [None] * n, 0)
print("largest properly L-colourable set:", best)
assert best == 9
assert 9 * 3 < 14 * 2

# The graph has a triangle, so it is not 2-choosable; 3-choosability over colours {1..6}:
# every assignment of 3-subsets of a 6-colour palette is too many to enumerate (20^14), so
# we only spot-check random assignments here; the Lean file has the full proof.
import random
random.seed(0)
pal = range(1, 7)
def colourable(lists):
    col = [None] * n
    def go(v):
        if v == n:
            return True
        for c in lists[v]:
            if all(not (adj[v][x] and col[x] == c) for x in range(v)):
                col[v] = c
                if go(v + 1):
                    return True
        col[v] = None
        return False
    return go(0)
for _ in range(20000):
    lists = [random.sample(pal, 3) for _ in range(n)]
    assert colourable(lists)
print("20000 random 3-list assignments from 6 colours: all colourable")
print("OK")
