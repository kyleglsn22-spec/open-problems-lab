import itertools, sys
from ortools.sat.python import cp_model
# lower part: m_j copies of e_j (j<8), leaves (y_i, u=1). zero-sumfree iff for all I with |I|%6==0, |I|>0:
# exists j with (-sum_I y_ij mod 6) > m_j.
def run(L, caps, tl=300):
    r=len(caps); m=cp_model.CpModel()
    y=[[m.NewIntVar(0,5,"") for j in range(r)] for i in range(L)]
    for s in range(6,L+1,6):
        for I in itertools.combinations(range(L),s):
            ors=[]
            for j in range(r):
                if caps[j]>=5: continue
                t=m.NewIntVar(0,5,""); q=m.NewIntVar(0,L,"")
                m.Add(sum(y[i][j] for i in I)+t==6*q)
                b=m.NewBoolVar(""); m.Add(t>caps[j]).OnlyEnforceIf(b); ors.append(b)
            m.AddBoolOr(ors)
    sv=cp_model.CpSolver(); sv.parameters.num_workers=4; sv.parameters.max_time_in_seconds=tl
    st=sv.Solve(m); print(L,caps,sv.StatusName(st),round(sv.WallTime(),1),flush=True)
    if st in (cp_model.OPTIMAL,cp_model.FEASIBLE): print([[sv.Value(v) for v in row] for row in y])
for L in [8,9,10]:
    d=L-6
    # distribute deficit d over 8 coords in all partitions
    seen=set()
    for p in itertools.combinations_with_replacement(range(8),d):
        caps=[5]*8
        for j in p: caps[j]-=1
        key=tuple(sorted(caps))
        if key in seen or min(caps)<0: continue
        seen.add(key); run(L,caps,120)
