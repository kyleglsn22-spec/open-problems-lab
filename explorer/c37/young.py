import sys, itertools, time
from math import comb, prod
from ortools.sat.python import cp_model
def solve(parts, d=5, tl=60):
    m=len(parts)
    ls=[l for l in itertools.product(*[range(min(a,d)+1) for a in parts]) if sum(l)<=d]
    M=cp_model.CpModel(); C={}
    for l in ls:
        s=sum(l)
        if s==0: C[l]=0
        elif s==1: C[l]=parts[l.index(1)]
        else: C[l]=M.NewIntVar(-10**7,10**7,str(l))
    for w in itertools.product(*[range(a+1) for a in parts]):
        expr=sum(C[l]*prod(comb(parts[t]-l[t],w[t]-l[t]) for t in range(m)) for l in ls if all(l[t]<=w[t] for t in range(m)))
        cap=prod(comb(parts[t],w[t]) for t in range(m))
        if isinstance(expr,int):
            if not 0<=expr<=cap: return 'INFEASIBLE(trivial)'
            continue
        M.Add(expr>=0); M.Add(expr<=cap)
    S=cp_model.CpSolver(); S.parameters.max_time_in_seconds=tl; S.parameters.num_workers=4
    r=S.Solve(M)
    return S.StatusName(r)
if __name__=='__main__':
    # usage: python3 young.py DEGREE PART PART ...   e.g. python3 young.py 4 8 2
    d=int(sys.argv[1]); parts=tuple(int(x) for x in sys.argv[2:])
    t=time.time(); print(parts, 'd =',d, solve(parts,d), round(time.time()-t,1))
