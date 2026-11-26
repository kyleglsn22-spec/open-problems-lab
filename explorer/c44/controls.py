from wdeg import solve, RV
import itertools
# Positive controls: CHS-type shapes reaching exactly R_d must be FEASIBLE
for w, d in [((4,4,1,1),5), ((4,3,3,1,1,1,1),5), ((3,3,3,3,1,1,1,1,1,1),5), ((3,3,1,1),4), ((2,2,2,2,1,1,1,1),4), ((4,2,2,2,2,1,1,1,1,1,1),5)]:
    st, sol, t = solve(list(w), d, 300, workers=1)
    print(w, d, "V=", sum(RV[x] for x in w), st, f"{t:.1f}s", flush=True)
