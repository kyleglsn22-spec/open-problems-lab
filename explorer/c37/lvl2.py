# Level-2 type enumeration: singleton types, pair types, aggregated edge counting + local vertex configurations.
import sys, itertools, time
from math import comb
from ortools.sat.python import cp_model
from lvl1 import profiles, split_types
def enum_all(M, vars_):
    S=cp_model.CpSolver(); S.parameters.enumerate_all_solutions=True; S.parameters.num_workers=1
    S.parameters.max_time_in_seconds=60
    out=[]
    class CB(cp_model.CpSolverSolutionCallback):
        def on_solution_callback(s): out.append(tuple(s.Value(v) for v in vars_))
    st=S.Solve(M,CB())
    assert S.StatusName(st) in ('OPTIMAL','INFEASIBLE'), S.StatusName(st)
    return out
def pair_types(n,d,C,t1,t2):
    # parts (n-2,1,1). Pattern (l0,b1,b2): sum c_S with |S\{i,j}|=l0, i∈S iff b1, j∈S iff b2.
    # Known: T_l(∅)=C_l, T_l(i)=t1, T_l(j)=t2 ; unknown P_l = T_l(ij) for l=2..d (P_2 = c_ij).
    M=cp_model.CpModel()
    P={l:M.NewIntVar(-10**5,10**5,f"P{l}") for l in range(2,d+1)}
    def Cl(l): return C[l] if 0<=l<=d else 0
    def T1(l): return (1 if l==1 else (t1[l-2] if 2<=l<=d else 0))
    def T2(l): return (1 if l==1 else (t2[l-2] if 2<=l<=d else 0))
    def Pl(l): return P[l] if 2<=l<=d else 0
    def D(l0,b1,b2):
        l=l0+b1+b2
        if b1 and b2: return Pl(l)
        if b1: return T1(l)-Pl(l)
        if b2: return T2(l)-Pl(l)
        return Cl(l)-T1(l)-T2(l)+Pl(l)
    m=n-2
    for x1 in (0,1):
        for x2 in (0,1):
            for w0 in range(m+1):
                e=0
                for b1 in range(x1+1):
                    for b2 in range(x2+1):
                        for l0 in range(0,min(w0,d-b1-b2)+1):
                            e+=D(l0,b1,b2)*comb(m-l0,w0-l0)
                cap=comb(m,w0)
                if isinstance(e,int):
                    if not 0<=e<=cap: return []
                else: M.Add(e>=0); M.Add(e<=cap)
    return enum_all(M,[P[l] for l in range(2,d+1)])
def level1_solutions(n,d,C,types):
    M=cp_model.CpModel(); c=[M.NewIntVar(0,n,f"c{i}") for i in range(len(types))]
    M.Add(sum(c)==n)
    for li,l in enumerate(range(2,d+1)):
        M.Add(sum(c[i]*types[i][li] for i in range(len(types)))==l*C[l])
    return enum_all(M,c)
def check_level2(n,d,C,types,mult,PT,tl=60):
    idx=[i for i in range(len(types)) if mult[i]>0]
    M=cp_model.CpModel(); x={}
    for a in idx:
        for b in idx:
            for P in PT[a,b]:
                ub=mult[a]*(mult[b]-(a==b))
                if ub>0: x[a,b,P]=M.NewIntVar(0,ub,"")
    for a in idx:
        for b in idx:
            ub=mult[a]*(mult[b]-(a==b))
            M.Add(sum(x[a,b,P] for P in PT[a,b] if (a,b,P) in x)==ub)
            # symmetry: ordered pair (a,b,P) and (b,a,P) count the same unordered pairs
        for li,l in enumerate(range(2,d+1)):
            M.Add(sum(x[a,b,P]*P[li] for b in idx for P in PT[a,b] if (a,b,P) in x)==mult[a]*(l-1)*types[a][li])
    for (a,b,P),v in list(x.items()):
        if a<b: M.Add(v==x.get((b,a,P),0))
        if (b,a,P) not in x: M.Add(v==0)
    # local configuration for one vertex of each type
    for a in idx:
        y={}
        for b in idx:
            for P in PT[a,b]:
                ub=mult[b]-(a==b)
                if ub>0: y[b,P]=M.NewIntVar(0,ub,"")
        for b in idx:
            M.Add(sum(y[b,P] for P in PT[a,b] if (b,P) in y)==mult[b]-(a==b))
        for li,l in enumerate(range(2,d+1)):
            M.Add(sum(y[k]*k[1][li] for k in y)==(l-1)*types[a][li])
    S=cp_model.CpSolver(); S.parameters.max_time_in_seconds=tl; S.parameters.num_workers=4
    return S.StatusName(S.Solve(M))
def run_profile(n,d,C,verbose=False):
    types=split_types(n,d,C)
    if not types: return 'INFEASIBLE',0
    sols=level1_solutions(n,d,C,types)
    if not sols: return 'INFEASIBLE',0
    PT={}
    for a in range(len(types)):
        for b in range(len(types)):
            PT[a,b]=pair_types(n,d,C,types[a],types[b])
    res=[]
    for mult in sols:
        r=check_level2(n,d,C,types,mult,PT)
        res.append(r)
        if r!='INFEASIBLE': return r,len(sols)
    return 'INFEASIBLE',len(sols)
if __name__=='__main__':
    n,d=map(int,sys.argv[1:3])
    P=profiles(n,d); tally={}
    for C in P:
        t=time.time(); r,k=run_profile(n,d,C); tally[r]=tally.get(r,0)+1
        print(C,r,k,round(time.time()-t,1),flush=True)
    print(tally)
