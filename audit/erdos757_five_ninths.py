# Auditor's independent check of the reader's 5/9 family (erdosproblemaday 7bkzb8) for Erdős #757.
# Literal definitions: (4,5) by |B-B| >= 11 on every 4-subset (integers after scaling), Sidon by
# the sum form; largest Sidon subset via HiGHS MILP (scipy), a different solver from PR 10's CP-SAT.
import sys
from fractions import Fraction as F
from itertools import combinations
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
O=[0,49,75,83,98,101,117,119,121,159,269]
def S(K):
    pts=set(F(x) for x in O); cur=[F(x) for x in O]
    for _ in range(K):
        cur=[101+F(18,269)*x for x in cur]; pts|=set(cur)
    return sorted(pts)
for K in range(int(sys.argv[1]),int(sys.argv[2])+1):
    A=S(K); n=len(A)
    D=269**K; Z=[int(a*D) for a in A]; assert all(F(z,D)==a for z,a in zip(Z,A))
    # literal (4,5) on all 4-subsets, via sorted 4-tuples
    bad=0
    for B in combinations(Z,4):
        if len({B[j]-B[i] for i in range(4) for j in range(i+1,4)})<5: bad+=1; break
    # all sum collisions a+b=c+d (a<=b, c<=d, {a,b}!={c,d})
    from collections import defaultdict
    sums=defaultdict(list)
    for i in range(n):
        for j in range(i,n): sums[Z[i]+Z[j]].append((i,j))
    coll=[v for v in sums.values() if len(v)>1]
    # each collision class: a Sidon subset must not contain two of its pairs entirely
    rows=[]
    for v in coll:
        for p,q in combinations(v,2):
            sup=set(p)|set(q); r=np.zeros(n)
            for t in sup: r[t]=1
            rows.append((r,len(sup)-1))
    Aub=np.array([r for r,_ in rows]); ub=np.array([u for _,u in rows])
    res=milp(c=-np.ones(n),constraints=LinearConstraint(Aub,-np.inf,ub),integrality=np.ones(n),bounds=Bounds(0,1))
    h=round(-res.fun)
    sel=[Z[i] for i in range(n) if res.x[i]>0.5]
    # verify the found set is Sidon (sum form)
    ss=[a+b for i,a in enumerate(sel) for b in sel[i:]]; assert len(ss)==len(set(ss))
    print(f"K={K} n={n} (4,5):{'ok' if not bad else 'FAIL'} collisions={len(coll)} h={h} status={res.status} ratio={F(h,n)} ={h/n:.5f} {'<4/7' if F(h,n)<F(4,7) else ''}",flush=True)
