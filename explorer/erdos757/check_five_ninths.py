"""Recheck of the 5/9 family for Erdős #757 (reader submission 7bkzb8 on
erdosproblemaday.com, 19 Oct 2026; not our construction).

O = {0,49,75,83,98,101,117,119,121,159,269}, phi(x) = 101 + 18x/269,
S_K = O ∪ phi(O) ∪ ... ∪ phi^K(O).  For each K up to argv[1] this checks, in exact
rational arithmetic, that S_K is a (4,5)-set (weak Sidon + linear 3-AP hypergraph,
plus the literal |B-B| >= 11 test on every 4-subset for K <= 6), and computes the
largest Sidon subset as the largest 3-AP-free subset with OR-tools CP-SAT (requires
`pip install ortools`).  Expected: |S_K| = 11+9K, h = 7+5K, below 4/7 from K = 6.
Usage: python3 check_five_ninths.py 8
"""
from fractions import Fraction as F
from itertools import combinations
from ortools.sat.python import cp_model
import sys
O=[0,49,75,83,98,101,117,119,121,159,269]
phi=lambda x: 101+F(18,269)*x
def S(K):
    pts=set(F(x) for x in O); cur=[F(x) for x in O]
    for _ in range(K):
        cur=[phi(x) for x in cur]; pts|=set(cur)
    return sorted(pts)
for K in range(0,int(sys.argv[1])+1):
    A=S(K); n=len(A)
    # (4,5): weak Sidon + linear AP hypergraph (equivalent), but also do literal check for small K
    sums={}
    ok=True
    for i,j in combinations(range(n),2):
        s=A[i]+A[j]
        if s in sums: ok=False
        sums[s]=(i,j)
    idx={a:i for i,a in enumerate(A)}
    aps=[]
    for i,k in combinations(range(n),2):
        m=(A[i]+A[k])/2
        if m in idx: aps.append((i,idx[m],k))
    for e,f in combinations(aps,2):
        if len(set(e)&set(f))>=2: ok=False
    if K<=6:
        for B in combinations(A,4):
            if len({abs(x-y) for x,y in combinations(B,2)})<5: ok=False;break
    m=cp_model.CpModel(); x=[m.NewBoolVar('') for _ in A]
    for (i,j,k) in aps: m.Add(x[i]+x[j]+x[k]<=2)
    m.Maximize(sum(x)); s=cp_model.CpSolver(); s.parameters.max_time_in_seconds=120; s.parameters.num_workers=8
    r=s.Solve(m)
    h=int(s.ObjectiveValue())
    print(K,n,len(aps),'(4,5)ok' if ok else 'FAIL', 'h=',h,'optimal' if r==cp_model.OPTIMAL else 'NOT-OPT', 'ratio',F(h,n), float(F(h,n)), '<4/7' if F(h,n)<F(4,7) else '')
