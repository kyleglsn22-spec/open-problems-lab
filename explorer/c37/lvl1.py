import itertools, sys
from math import comb
from ortools.sat.python import cp_model
from fractions import Fraction as F
def profiles(n,d):
    # all integer C (C_0=0,C_1=n) with 0<=N(k)<=binom(n,k)
    M=cp_model.CpModel(); C=[0,n]+[M.NewIntVar(-10**6,10**6,f"C{l}") for l in range(2,d+1)]
    for k in range(n+1):
        e=sum(C[l]*comb(n-l,k-l) for l in range(min(k,d)+1))
        if not isinstance(e,int): M.Add(e>=0); M.Add(e<=comb(n,k))
    S=cp_model.CpSolver(); S.parameters.enumerate_all_solutions=True; S.parameters.num_workers=1
    out=[]
    class CB(cp_model.CpSolverSolutionCallback):
        def on_solution_callback(s): out.append([0,n]+[s.Value(c) for c in C[2:]])
    S.Solve(M,CB()); return out
def split_types(n,d,C):
    # T_l = sum_{S∋j,|S|=l} c_S ; outside coefficient U_l = C_l - T_l ; parts (n-1,1)
    m=n-1
    M=cp_model.CpModel(); T=[0,1]+[M.NewIntVar(-10**6,10**6,f"T{l}") for l in range(2,d+1)]
    # pattern (l0,0): U_{l0}; pattern (l0,1): T_{l0+1}
    def U(l): return (C[l]-T[l]) if l<=d else 0
    def Tt(l): return T[l] if l<=d else 0
    for w0 in range(m+1):
        e0=sum(U(l0)*comb(m-l0,w0-l0) for l0 in range(min(w0,d)+1))
        e1=e0+sum(Tt(l0+1)*comb(m-l0,w0-l0) for l0 in range(min(w0,d-1)+1))
        for e in (e0,e1):
            if isinstance(e,int):
                if not 0<=e<=comb(m,w0): return []
            else: M.Add(e>=0); M.Add(e<=comb(m,w0))
    S=cp_model.CpSolver(); S.parameters.enumerate_all_solutions=True; S.parameters.num_workers=1
    out=[]
    class CB(cp_model.CpSolverSolutionCallback):
        def on_solution_callback(s): out.append(tuple(s.Value(t) for t in T[2:]))
    S.Solve(M,CB()); return out
def multiplicity_ok(n,d,C,types,tl=30):
    if not types: return 'INFEASIBLE'
    M=cp_model.CpModel(); c=[M.NewIntVar(0,n,f"c{i}") for i in range(len(types))]
    M.Add(sum(c)==n)
    for li,l in enumerate(range(2,d+1)):
        M.Add(sum(c[i]*types[i][li] for i in range(len(types)))==l*C[l])
    S=cp_model.CpSolver(); S.parameters.max_time_in_seconds=tl; S.parameters.num_workers=4
    return S.StatusName(S.Solve(M))
if __name__=='__main__':
    n,d=map(int,sys.argv[1:])
    P=profiles(n,d); print(len(P),'profiles')
    surv=0
    for C in P:
        ty=split_types(n,d,C); r=multiplicity_ok(n,d,C,ty)
        if r!='INFEASIBLE': surv+=1
        if n<=15: print(C,len(ty),r)
    print('level-1 survivors',surv)
