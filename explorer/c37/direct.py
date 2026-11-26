# Direct CP-SAT search for q on 14 bits, deg<=5, with the surviving profile C*, optional per-coordinate type.
import itertools, sys, time, os
from ortools.sat.python import cp_model
n,d=14,5
Cstar=[0,14,-91,224,-231,84]
def run(types_per_coord=None, tl=600, workers=2, B=60):
    M=cp_model.CpModel(); c={}
    subs=[S for k in range(d+1) for S in itertools.combinations(range(n),k)]
    for S in subs:
        k=len(S)
        if k==0: c[S]=0
        elif k==1: c[S]=1
        elif k==2: c[S]=-1
        elif k==3: c[S]=M.NewBoolVar(str(S))
        else: c[S]=M.NewIntVar(-B,B,str(S))
    for l in range(3,d+1):
        M.Add(sum(c[S] for S in subs if len(S)==l)==Cstar[l])
    if types_per_coord:
        for i,t in enumerate(types_per_coord):
            for l in range(3,d+1):
                M.Add(sum(c[S] for S in subs if len(S)==l and i in S)==t[l-2])
    M.Add(c[(0,1,2)]==1)
    idx={S:i for i,S in enumerate(subs)}
    for x in range(1<<n):
        bits=[i for i in range(n) if x>>i&1]
        if len(bits)<=2: continue
        e=sum(c[S] for k in range(3,min(d,len(bits))+1) for S in itertools.combinations(bits,k))
        base=len(bits)-len(bits)*(len(bits)-1)//2
        M.Add(e+base>=0); M.Add(e+base<=1)
    print('model built',flush=True)
    S=cp_model.CpSolver(); S.parameters.max_time_in_seconds=tl; S.parameters.num_workers=workers
    S.parameters.log_search_progress=False
    st=S.StatusName(S.Solve(M)); print('status',st,flush=True)
    if st in('OPTIMAL','FEASIBLE'):
        with open('FOUND_q14.txt','w') as f:
            for Sx in subs:
                v=c[Sx] if isinstance(c[Sx],int) else S.Value(c[Sx])
                if v: f.write(f"{Sx} {v}\n")
    return st
if __name__=='__main__':
    mode=sys.argv[1]; tl=int(sys.argv[2])
    T3=(-13,48,-66,30)
    run([T3]*n if mode=='alltype3' else None, tl=tl, workers=int(os.environ.get('W','2')))
