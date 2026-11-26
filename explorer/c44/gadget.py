"""Search for 'signed-partition gadgets' G(x;u) = s0(x) + sum_j s_j(x) u_j.
Substituting disjoint extremal degree-(d-a_j) functions for u_j gives a degree-d
Boolean function with Phi = r + sum_j R_{d-a_j} relevant variables."""
import itertools, sys
from ortools.sat.python import cp_model

R = {0:0, 1:1, 2:4, 3:10, 4:22, 5:46}  # R_k exact for k<=4; 46 = CHS lower bound for 5

def solve(r, degs, d, allow_s0=True, time_limit=600, workers=4):
    N = 1 << r
    m = len(degs)
    M = cp_model.CpModel()
    P = [[M.NewBoolVar(f"p{j}_{x}") for x in range(N)] for j in range(m+1)]
    Q = [[M.NewBoolVar(f"q{j}_{x}") for x in range(N)] for j in range(m+1)]
    caps = list(degs) + [d]
    for x in range(N):
        M.AddExactlyOne([P[j][x] for j in range(m+1)] + [Q[j][x] for j in range(m+1)])
    if not allow_s0:
        for x in range(N):
            M.Add(P[m][x] == 0); M.Add(Q[m][x] == 0)
    # degree constraints: for every T with |T| = cap+1 and every w on complement, sum chi_T * s = 0
    for j, a in enumerate(caps):
        if a >= r: continue
        for T in itertools.combinations(range(r), a+1):
            tmask = sum(1 << i for i in T)
            rest = [i for i in range(r) if i not in T]
            for wbits in range(1 << len(rest)):
                base = sum(1 << rest[k] for k in range(len(rest)) if wbits >> k & 1)
                terms = []
                for zb in range(1 << (a+1)):
                    x = base; sgn = 1
                    for k, i in enumerate(T):
                        if zb >> k & 1: x |= 1 << i; sgn = -sgn
                    terms.append((sgn, x))
                M.Add(sum(s*(P[j][x] - Q[j][x]) for s, x in terms) == 0)
    # each non-constant piece nonempty
    for j in range(m):
        M.AddBoolOr([P[j][x] for x in range(N)] + [Q[j][x] for x in range(N)])
    # every x-variable relevant: some piece value changes when flipping bit i
    for i in range(r):
        lits = []
        for x in range(N):
            y = x ^ (1 << i)
            if y < x: continue
            for j in range(m+1):
                # s_j(x) != s_j(y)
                b = M.NewBoolVar("")
                M.Add(P[j][x] - Q[j][x] != P[j][y] - Q[j][y]).OnlyEnforceIf(b)
                lits.append(b)
        M.AddBoolOr(lits)
    # symmetry breaking: point 0 has value +1 in piece 0 or s0 (weak)
    S = cp_model.CpSolver()
    S.parameters.max_time_in_seconds = time_limit
    S.parameters.num_workers = workers
    st = S.Solve(M)
    sol = None
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol = [[S.Value(P[j][x]) - S.Value(Q[j][x]) for x in range(N)] for j in range(m+1)]
    return S.StatusName(st), sol, S.WallTime()

def multisets(d, rmax, target):
    out = []
    contrib = {a: R[d-a] for a in range(1, d)}
    def rec(start, cur, kraft):
        phi0 = sum(contrib[a] for a in cur)
        if cur:
            rmin = max(1, target - phi0)
            for r in range(rmin, rmax+1):
                out.append((r, tuple(cur), r + phi0))
        for a in range(start, d):
            if kraft + 2**-a <= 1 + 1e-12:
                rec(a, cur + [a], kraft + 2**-a)
    rec(1, [], 0.0)
    return out

if __name__ == "__main__":
    d = int(sys.argv[1]); rmax = int(sys.argv[2]); target = int(sys.argv[3])
    tl = float(sys.argv[4]) if len(sys.argv) > 4 else 600
    cases = sorted(multisets(d, rmax, target), key=lambda c: (c[0], c[1]))
    print(f"d={d} rmax={rmax} target>={target}: {len(cases)} cases", flush=True)
    for r, degs, phi in cases:
        st, sol, t = solve(r, degs, d, time_limit=tl)
        print(f"r={r} degs={degs} Phi={phi}: {st} ({t:.1f}s)", flush=True)
        if sol: print("  SOLUTION", sol, flush=True)
