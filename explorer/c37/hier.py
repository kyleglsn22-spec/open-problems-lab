# Level-k hierarchy: per-subset orbit coefficient sums T_l(A) = sum_{S ⊇ A, |S|=l} c_S, |A|<=k.
import itertools, sys, time
from math import comb
from ortools.sat.python import cp_model
def build(n,d,k,extra=None):
    M=cp_model.CpModel(); T={}
    subsets=[A for s in range(k+1) for A in itertools.combinations(range(n),s)]
    for A in subsets:
        for l in range(len(A),d+1):
            if l==0: T[A,l]=0
            elif l==1: T[A,l]= n if len(A)==0 else 1
            else: T[A,l]=M.NewIntVar(-10**6,10**6,f"T{A}_{l}")
    def Tv(A,l):
        if l>d or l<len(A): return 0
        return T[A,l]
    # consistency
    for B in subsets:
        if len(B)<k:
            for l in range(max(len(B)+1,2),d+1):
                M.Add(sum(Tv(tuple(sorted(B+(j,))),l) for j in range(n) if j not in B)==(l-len(B))*Tv(B,l))
    # Young model for each top-level A
    m=n-k
    for A in itertools.combinations(range(n),k):
        D={}
        for r in range(k+1):
            for B in itertools.combinations(A,r):
                for l0 in range(0,d-r+1):
                    l=l0+r; e=0
                    rest=[a for a in A if a not in B]
                    for s in range(len(rest)+1):
                        for E in itertools.combinations(rest,s):
                            e+= (-1)**s * Tv(tuple(sorted(B+E)),l)
                    D[l0,B]=e
        for r in range(k+1):
            for X in itertools.combinations(A,r):
                for w0 in range(m+1):
                    expr=0
                    for rb in range(r+1):
                        for B in itertools.combinations(X,rb):
                            for l0 in range(0,min(w0,d-rb)+1):
                                expr+=D[l0,B]*comb(m-l0,w0-l0)
                    cap=comb(m,w0)
                    if isinstance(expr,int):
                        if not 0<=expr<=cap: M.Add(0==1)
                    else:
                        M.Add(expr>=0); M.Add(expr<=cap)
    return M,T
def run(n,d,k,tl=120,workers=4):
    M,T=build(n,d,k)
    S=cp_model.CpSolver(); S.parameters.max_time_in_seconds=tl; S.parameters.num_workers=workers
    t=time.time(); r=S.StatusName(S.Solve(M))
    return r,round(time.time()-t,1)
if __name__=='__main__':
    n,d,k,tl=map(int,sys.argv[1:])
    print((n,d,k),run(n,d,k,tl),flush=True)
