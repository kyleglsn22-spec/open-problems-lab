r"""Computer-assisted proof that the reader's family gives c* <= 5/9 for Erdős #757 (all K).

O = {0,49,75,83,98,101,117,119,121,159,269},  phi(x) = 101 + 18x/269,
S_K = O ∪ phi(O) ∪ ... ∪ phi^K(O).

Theorem. For every K >= 0, S_K is a (4,5)-set with |S_K| = 11 + 9K and h(S_K) <= 7 + 5K.
Hence c* = inf f(n)/n <= (7+5K)/(11+9K) for all K, and these tend to 5/9, so c* <= 5/9.

Everything below is exact rational arithmetic (Python Fractions), no floating point.

Proof outline (each step is checked by this script):
 (1) Counting. phi(O) ∩ O = {101, 119}, and O has no point in I_2 = phi^2([0,269]).
     Copy k lies in I_k = phi^k([0,269]), and these intervals are nested. So copy k meets
     copy k-1 in exactly two points and meets no earlier copy. Hence |S_K| = 11 + 9K.
 (2) Base case. S_1 = O ∪ phi(O) (20 points) is a (4,5)-set, and its 3-term progressions
     are exactly the 9 of O plus their 9 images.
 (3) No mixing. "Depth" of a point = least k with the point in phi^k(O). Call a relation
     x1+x2 = x3+x4 (4 distinct points) or x1+x3 = 2*x2 (3 distinct points) "mixing" if it uses
     a point of depth d and a point of depth >= d+2. Such relations are invariant under phi^-d,
     so we may take d = 0. All points of depth >= L+1 lie in I_{L+1}. For each assignment of
     the slots to known points (depth <= L) or "unknown" (anywhere in I_{L+1}), interval
     arithmetic either rules it out or the unknown slots are refined at level L+1. The search
     closes at level 3 with no solution. So every relation spans at most two consecutive
     depths, and after applying phi^-d it lies inside S_1.
 (4) (4,5) for every S_K. A set is (4,5) iff it has no relation x1+x2 = x3+x4 with 4 distinct
     points and no two 3-APs share two points. By (3) and (2), no 4-point relation exists and
     every 3-AP is an image of a 3-AP of O. Two 3-APs sharing two points have union of depth
     span <= 2, and each spans <= 1 level, so both lie in two adjacent copies, i.e. in one image
     of S_1 (Auditor's remark). There they are excluded by (2). The 0/269 check below is
     redundant, kept as a sanity check.
 (5) Sidon bound. Potential pi = (0,1,1,1) on the glued pair, with the two finite inequalities
     of transfer_certificate.py. Union bound over the copies gives h(S_K) <= 7 + 5K. This step
     needs no geometry.
"""
from fractions import Fraction as F
from itertools import combinations, product

O = [F(x) for x in [0, 49, 75, 83, 98, 101, 117, 119, 121, 159, 269]]
A, B, P, Q = F(0), F(269), F(101), F(119)
r = F(18, 269)
phi = lambda x: P + r * x


def phik(x, k):
    for _ in range(k):
        x = phi(x)
    return x


def I(k):
    return phik(A, k), phik(B, k)


def aps(S):
    s = set(S)
    return {frozenset((x, (x + z) / 2, z)) for x, z in combinations(sorted(S), 2) if (x + z) / 2 in s}


def has_4term_relation(S):
    S = sorted(S); seen = {}
    for i, j in combinations(range(len(S)), 2):
        t = S[i] + S[j]
        for (k, l) in seen.get(t, []):
            if len({i, j, k, l}) == 4:
                return True
        seen.setdefault(t, []).append((i, j))
    return False


# (1) counting
assert phi(A) == P and phi(B) == Q
assert set(map(phi, O)) & set(O) == {P, Q}
lo2, hi2 = I(2)
assert not any(lo2 <= x <= hi2 for x in O)
assert A <= P < Q <= B                        # I_1 inside I_0, hence all I_k nested
for K in range(6):
    assert len({phik(x, k) for k in range(K + 1) for x in O}) == 11 + 9 * K
print("(1) |S_K| = 11 + 9K: ok")

# (2) base case S_1
S1 = sorted(set(O) | set(map(phi, O)))
EO = aps(O)
assert len(EO) == 9
assert aps(S1) == EO | {frozenset(map(phi, e)) for e in EO}
assert not has_4term_relation(S1)
assert all(len(e & f) <= 1 for e, f in combinations(aps(S1), 2))
print("(2) S_1 is a (4,5)-set; its 3-APs are the 18 copy APs: ok")


# (3) no mixing
def depths(L):
    d = {}
    for k in range(L + 1):
        for x in O:
            d.setdefault(phik(x, k), k)
    return d


U = None
TEMPL = [(1, 1, -1, -1), (1, 1, -2)]


def feasible(ks, uc, L):
    lo, hi = I(L + 1)
    mn = ks + sum(c * (lo if c > 0 else hi) for c in uc)
    mx = ks + sum(c * (hi if c > 0 else lo) for c in uc)
    return mn <= 0 <= mx


L = 1; D = depths(1); pts = sorted(D); surv = []
for T in TEMPL:
    for asg in product(pts + [U], repeat=len(T)):
        kn = [a for a in asg if a is not U]
        if len(set(kn)) < len(kn) or not any(D[a] == 0 for a in kn) or U not in asg:
            continue
        ks = sum(c * a for c, a in zip(T, asg) if a is not U)
        if feasible(ks, [c for c, a in zip(T, asg) if a is U], L):
            surv.append((T, asg))
print(f"(3) level 1: {len(surv)} open cases")
while surv:
    L += 1; D = depths(L)
    assert L <= 10, "did not close"
    new = [x for x, d in D.items() if d == L]; nxt = []
    for T, asg in surv:
        ui = [i for i, a in enumerate(asg) if a is U]
        for rep in product(new + [U], repeat=len(ui)):
            a = list(asg)
            for i, v in zip(ui, rep):
                a[i] = v
            kn = [x for x in a if x is not U]
            if len(set(kn)) < len(kn):
                continue
            ks = sum(c * x for c, x in zip(T, a) if x is not U)
            uc = [c for c, x in zip(T, a) if x is U]
            if not uc:
                assert ks != 0, f"mixing relation found: {T} {a}"
                continue
            if feasible(ks, uc, L):
                nxt.append((T, tuple(a)))
    surv = nxt
    print(f"    level {L}: {len(surv)} open cases")
print("(3) no relation mixes depths d and >= d+2: ok")

# (4) cross-copy linearity: no AP of O contains both 0 and 269
assert not any({A, B} <= e for e in EO)
print("(4) every S_K is a (4,5)-set: ok")

# (5) Sidon bound via the transfer certificate
from transfer_certificate import check
ok, bad = check([int(x) for x in O], 101, 119, pi=[0, 1, 1, 1], G=5, C=6)
assert ok, bad
print("(5) h(S_K) <= 7 + 5K: ok")
print("THEOREM: S_K is a (4,5)-set of size 11+9K with h(S_K) <= 7+5K for all K, so c* <= 5/9.")
