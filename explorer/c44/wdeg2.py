"""Faster, equivalent form of wdeg.py when heavy variables never share a monomial.
Heavy vars (weight w with 2w > d... precisely: no two heavy vars fit together, w_i + w_j > d)
enter G linearly and never together, so G(z,u) = A(z) + sum_j u_j B_j(z) with z the light vars.
G is Boolean for all u iff for every z exactly one of A(z), B_1(z), ..., B_m(z) is +-1 and the rest 0.
Constraints: A has weighted degree <= d, B_j has weighted degree <= d - w_j (on light vars);
every light var is relevant (some piece changes when it flips); every B_j is not identically 0."""
import itertools, sys, ast
from ortools.sat.python import cp_model

RV = {1:1, 2:4, 3:10, 4:22, 5:46}

def min_heavy_sets(lw, cap):
    n = len(lw); out = []
    for k in range(1, n+1):
        for T in itertools.combinations(range(n), k):
            s = sum(lw[i] for i in T)
            if s > cap and all(s - lw[j] <= cap for j in T):
                out.append(T)
    return out

def solve(weights, d, tl=600, workers=4):
    heavy = [w for w in weights if 2*w > d]
    light = [w for w in weights if 2*w <= d]
    assert all(a + b > d for a, b in itertools.combinations(heavy, 2))
    n = len(light); Z = 1 << n; m = len(heavy)
    caps = [d - w for w in heavy] + [d]      # pieces B_1..B_m, then A
    M = cp_model.CpModel()
    P = [[M.NewBoolVar("") for _ in range(Z)] for _ in caps]
    Q = [[M.NewBoolVar("") for _ in range(Z)] for _ in caps]
    for z in range(Z):
        M.AddExactlyOne([P[j][z] for j in range(m+1)] + [Q[j][z] for j in range(m+1)])
    for j, cap in enumerate(caps):
        for T in min_heavy_sets(light, cap):
            rest = [i for i in range(n) if i not in T]
            for wb in range(1 << len(rest)):
                base = sum(1 << rest[k] for k in range(len(rest)) if wb >> k & 1)
                terms = []
                for zb in range(1 << len(T)):
                    z = base; s = 1
                    for k, i in enumerate(T):
                        if zb >> k & 1: z |= 1 << i; s = -s
                    terms.append(s * (P[j][z] - Q[j][z]))
                M.Add(sum(terms) == 0)
    for j in range(m):
        M.AddBoolOr(P[j] + Q[j])
    for i in range(n):
        lits = []
        for z in range(Z):
            if z >> i & 1: continue
            y = z | 1 << i
            for j in range(m+1):
                b = M.NewBoolVar("")
                M.Add(P[j][z] - Q[j][z] != P[j][y] - Q[j][y]).OnlyEnforceIf(b)
                lits.append(b)
        M.AddBoolOr(lits)
    # G -> -G symmetry: piece value at z=0 is +1
    M.Add(sum(Q[j][0] for j in range(m+1)) == 0)
    S = cp_model.CpSolver(); S.parameters.max_time_in_seconds = tl; S.parameters.num_workers = workers
    st = S.Solve(M)
    sol = None
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol = [[S.Value(P[j][z]) - S.Value(Q[j][z]) for z in range(Z)] for j in range(m+1)]
    return S.StatusName(st), sol, S.WallTime()

if __name__ == "__main__":
    d = int(sys.argv[1]); tl = float(sys.argv[2])
    for line in sys.stdin:
        if not line.startswith("w="): continue
        w = ast.literal_eval(line[2:line.index(")")+1])
        st, sol, t = solve(list(w), d, tl)
        print(f"w={w} V={sum(RV[x] for x in w)}: {st} ({t:.1f}s)", flush=True)
        if sol: print("  SOLUTION", sol, flush=True)
