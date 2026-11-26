import itertools, sys, numpy as np
from ortools.sat.python import cp_model
from sig import reach, W, n
def missing(seq,r):
    R=reach(seq,r); return [tuple(int((i//n**j)%n) for j in range(r)) for i in np.nonzero(~R)[0]]
MW=missing(W,4)
def run(nW, caps, L, tl=300, ucoef=None):
    m=cp_model.CpModel()
    r=4*nW+len(caps)
    y=[[m.NewIntVar(0,5,"") for j in range(r)] for i in range(L)]
    def negsum(I,j):
        t=m.NewIntVar(0,5,""); q=m.NewIntVar(0,L,""); m.Add(sum(y[i][j] for i in I)+t==6*q); return t
    for s in range(6,L+1,6):
        for I in itertools.combinations(range(L),s):
            ors=[]
            for b in range(nW):
                t=[negsum(I,4*b+j) for j in range(4)]
                bb=m.NewBoolVar(""); m.AddAllowedAssignments(t,MW).OnlyEnforceIf(bb); ors.append(bb)
            for c,cap in enumerate(caps):
                if cap>=5: continue
                t=negsum(I,4*nW+c); bb=m.NewBoolVar(""); m.Add(t>cap).OnlyEnforceIf(bb); ors.append(bb)
            m.AddBoolOr(ors)
    sv=cp_model.CpSolver(); sv.parameters.num_workers=int(__import__("os").environ.get("NW","4")); sv.parameters.max_time_in_seconds=tl
    st=sv.Solve(m); print("nW",nW,"caps",caps,"L",L,sv.StatusName(st),round(sv.WallTime(),1),flush=True)
    if st in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        sol=[[sv.Value(v) for v in row] for row in y]; print(sol,flush=True); return sol
if __name__=="__main__":
    nW=int(sys.argv[1]); L=int(sys.argv[2]); caps=list(map(int,sys.argv[3].split(","))) if len(sys.argv)>3 and sys.argv[3] else []
    run(nW,caps,L,int(sys.argv[4]) if len(sys.argv)>4 else 300)
