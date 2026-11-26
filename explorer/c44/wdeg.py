"""Weighted-degree block compositions.
Find Boolean G on N variables, variable i having weight w_i, such that every Fourier
monomial S of G has sum_{i in S} w_i <= d, and G depends on every variable.
Substituting disjoint extremal degree-w_i functions (R_1..R_4 = 1,4,10,22) for the
weight-w_i variables gives a degree-d Boolean function with V = sum R_{w_i} relevant vars."""
import itertools, sys, time
from ortools.sat.python import cp_model

RV = {1:1, 2:4, 3:10, 4:22, 5:46}

def minimal_heavy(weights, d):
    N = len(weights); out = []
    for k in range(1, N+1):
        for T in itertools.combinations(range(N), k):
            if sum(weights[i] for i in T) > d and all(sum(weights[i] for i in T if i != j) <= d for j in T):
                out.append(T)
    return out

def build(weights, d):
    N = len(weights); P = 1 << N
    M = cp_model.CpModel()
    g = [M.NewBoolVar(f"g{x}") for x in range(P)]   # G(x) = 2g-1
    for T in minimal_heavy(weights, d):
        rest = [i for i in range(N) if i not in T]
        for wb in range(1 << len(rest)):
            base = sum(1 << rest[k] for k in range(len(rest)) if wb >> k & 1)
            terms = []
            for zb in range(1 << len(T)):
                x = base; s = 1
                for k, i in enumerate(T):
                    if zb >> k & 1: x |= 1 << i; s = -s
                terms.append(s * g[x])
            # sum s*(2g-1) = 0 ; sum s = 0 since |T|>=1, so sum s*g = 0
            M.Add(sum(terms) == 0)
    for i in range(N):
        diffs = []
        for x in range(P):
            if x >> i & 1: continue
            b = M.NewBoolVar("")
            M.Add(g[x] != g[x | 1 << i]).OnlyEnforceIf(b)
            M.Add(g[x] == g[x | 1 << i]).OnlyEnforceIf(b.Not())
            diffs.append(b)
        M.AddBoolOr(diffs)
    M.Add(g[0] == 1)  # G -> -G symmetry
    return M, g

def solve(weights, d, tl=600, workers=4):
    M, g = build(weights, d)
    S = cp_model.CpSolver(); S.parameters.max_time_in_seconds = tl; S.parameters.num_workers = workers
    st = S.Solve(M)
    sol = [S.Value(v) for v in g] if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None
    return S.StatusName(st), sol, S.WallTime()

def weight_vectors(d, target, Nmax, wmax=None):
    wmax = wmax or d - 1
    out = []
    def rec(cur, mx):
        V = sum(RV[w] for w in cur)
        if V >= target and cur: out.append(tuple(cur)); 
        if len(cur) >= Nmax: return
        for w in range(min(mx, wmax), 0, -1):
            nxt = cur + [w]
            if sum(x * 2**x for x in nxt) > d * 2**d: continue
            rec(nxt, w)
    rec([], wmax)
    return out

if __name__ == "__main__":
    d, target, Nmax = map(int, sys.argv[1:4]); tl = float(sys.argv[4]) if len(sys.argv) > 4 else 600
    vecs = sorted(weight_vectors(d, target, Nmax), key=lambda v: (len(v), v))
    print(f"d={d} target>={target} Nmax={Nmax}: {len(vecs)} weight vectors", flush=True)
    for w in vecs:
        st, sol, t = solve(list(w), d, tl)
        print(f"w={w} V={sum(RV[x] for x in w)}: {st} ({t:.1f}s)", flush=True)
        if sol: print("  SOLUTION", ''.join(map(str, sol)), flush=True)
