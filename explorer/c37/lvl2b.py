# Level 2 with the singleton-type multiplicities as variables (no enumeration).
import sys, time
from ortools.sat.python import cp_model
from lvl1 import profiles, split_types
from lvl2 import pair_types
def check(n,d,C,tl=120):
    types=split_types(n,d,C)
    if not types: return 'INFEASIBLE(no types)'
    K=len(types)
    PT={}
    for a in range(K):
        for b in range(a,K):
            PT[a,b]=pair_types(n,d,C,types[a],types[b]); PT[b,a]=PT[a,b]
    M=cp_model.CpModel()
    m=[M.NewIntVar(0,n,f"m{a}") for a in range(K)]
    M.Add(sum(m)==n)
    for li,l in enumerate(range(2,d+1)):
        M.Add(sum(m[a]*types[a][li] for a in range(K))==l*C[l])
    pos=[M.NewBoolVar(f"pos{a}") for a in range(K)]
    for a in range(K):
        M.Add(m[a]>=1).OnlyEnforceIf(pos[a]); M.Add(m[a]==0).OnlyEnforceIf(pos[a].Not())
    x={}
    for a in range(K):
        for b in range(K):
            tot=M.NewIntVar(0,n*n,"")
            if a==b:
                sq=M.NewIntVar(0,n*n,""); M.AddMultiplicationEquality(sq,[m[a],m[a]]); M.Add(tot==sq-m[a])
            else:
                M.AddMultiplicationEquality(tot,[m[a],m[b]])
            for P in PT[a,b]: x[a,b,P]=M.NewIntVar(0,n*n,"")
            M.Add(sum(x[a,b,P] for P in PT[a,b])==tot)
        for li,l in enumerate(range(2,d+1)):
            rhs=M.NewIntVar(-10**7,10**7,""); M.Add(rhs==m[a]*((l-1)*types[a][li]))
            M.Add(sum(x[a,b,P]*P[li] for b in range(K) for P in PT[a,b])==rhs)
        # local configuration for a vertex of type a (if present)
        y={}
        for b in range(K):
            for P in PT[a,b]: y[b,P]=M.NewIntVar(0,n,"")
        for b in range(K):
            M.Add(sum(y[b,P] for P in PT[a,b])==m[b]-(1 if a==b else 0)).OnlyEnforceIf(pos[a])
        for li,l in enumerate(range(2,d+1)):
            M.Add(sum(y[k]*k[1][li] for k in y)==(l-1)*types[a][li]).OnlyEnforceIf(pos[a])
    for (a,b,P),v in list(x.items()):
        if a<b: M.Add(v==x.get((b,a,P),0))
    S=cp_model.CpSolver(); S.parameters.max_time_in_seconds=tl; S.parameters.num_workers=int(__import__('os').environ.get('W','4'))
    return S.StatusName(S.Solve(M))
if __name__=='__main__':
    n,d=map(int,sys.argv[1:3]); tl=int(sys.argv[3]) if len(sys.argv)>3 else 120
    tally={}
    shard=int(__import__('os').environ.get('SHARD','0')); nsh=int(__import__('os').environ.get('NSH','1'))
    done=set(__import__('os').environ.get('DONE','').split(';'))
    for i,C in enumerate(profiles(n,d)):
        if i%nsh!=shard or str(C) in done: continue
        t=time.time(); r=check(n,d,C,tl); tally[r]=tally.get(r,0)+1
        print(C,r,round(time.time()-t,1),flush=True)
    print(tally)
