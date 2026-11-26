"""Independent cross-check of wdeg.py verdicts with a different encoding and solver.
Encoding: G(x) = 2 g_x - 1; for EVERY subset S of weight > d, the full Fourier sum
sum_x (-1)^{|x & S|} G(x) = 0 (not the local derivative form used in wdeg.py).
Relevance of variable i: some x with g_x != g_{x xor e_i}, linearised with t_{x,i} >= |g_x - g_y|.
Solver: SCIP (MIP), not CP-SAT. Written separately from wdeg.py (shares no code)."""
import sys, ast
from ortools.linear_solver import pywraplp

def check(weights, d, tl=600):
    N = len(weights); P = 1 << N
    s = pywraplp.Solver.CreateSolver("SCIP")
    s.SetTimeLimit(int(tl * 1000))
    g = [s.BoolVar(f"g{x}") for x in range(P)]
    for S in range(1, P):
        if sum(weights[i] for i in range(N) if S >> i & 1) > d:
            # sum (-1)^{|x&S|} (2g-1) = 0  <=>  sum (-1)^{|x&S|} g = 0  (since S != 0)
            s.Add(sum((1 if bin(x & S).count("1") % 2 == 0 else -1) * g[x] for x in range(P)) == 0)
    for i in range(N):
        ts = []
        for x in range(P):
            if x >> i & 1: continue
            y = x | (1 << i)
            t = s.BoolVar("")
            # t = 1 only if g_x != g_y : t <= g_x + g_y, t <= 2 - g_x - g_y
            s.Add(t <= g[x] + g[y]); s.Add(t <= 2 - g[x] - g[y])
            ts.append(t)
        s.Add(sum(ts) >= 1)
    s.Add(g[0] == 1)
    st = s.Solve()
    names = {pywraplp.Solver.OPTIMAL: "FEASIBLE", pywraplp.Solver.FEASIBLE: "FEASIBLE",
             pywraplp.Solver.INFEASIBLE: "INFEASIBLE"}
    return names.get(st, f"UNDECIDED({st})")

if __name__ == "__main__":
    d = int(sys.argv[1]); log = sys.argv[2]; tl = float(sys.argv[3]) if len(sys.argv) > 3 else 600
    for line in open(log):
        if line.startswith("w=") and "INFEASIBLE" in line:
            w = ast.literal_eval(line[2:line.index(")")+1])
            print(w, check(list(w), d, tl), flush=True)
