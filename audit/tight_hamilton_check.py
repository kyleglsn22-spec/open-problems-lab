"""Independent brute-force check of Ferudun's Theorem 1.2(a) (Zenodo 10.5281/zenodo.23006717):
the k-graph H_k on W = {1..6} plus k-2 apexes (edges: k-sets meeting W in != 3 points, or in a
face of the hemi-icosahedron) has minimum codegree 3 = floor(7/2) and no tight Hamiltonian cycle,
for k = 3, 4, 5. Uses the paper's 1-based face list directly."""
from itertools import combinations, permutations

FACES = {frozenset(map(int, t)) for t in
         "123 124 135 146 156 236 245 256 345 346".split()}
W = set(range(1, 7))

def edges(k):
    V = list(range(1, 7)) + [f"a{j}" for j in range(k - 2)]
    E = set()
    for e in combinations(V, k):
        w = frozenset(x for x in e if x in W)
        if len(w) != 3 or w in FACES:
            E.add(frozenset(e))
    return V, E

def check(k):
    V, E = edges(k)
    n = len(V)
    mincod = min(sum(1 for e in E if set(S) <= e) for S in combinations(V, k - 1))
    # cyclic orders: fix V[0] at position 0 (rotation), enumerate the rest
    cycles = 0
    for rest in permutations(V[1:]):
        order = (V[0],) + rest
        if all(frozenset(order[(i + t) % n] for t in range(k)) in E for i in range(n)):
            cycles += 1
    return n, len(E), mincod, (n - k + 3) // 2, cycles

for k in (3, 4, 5):
    n, m, c, bound, cyc = check(k)
    print(f"k={k}: n={n}, edges={m}, min codegree={c}, bound={bound}, tight Ham cycles={cyc}")
    assert c >= bound and cyc == 0
print("OK")
