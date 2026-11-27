import numpy as np, math
from ortools.sat.python import cp_model
from ev import score

def solve_shape(d,m,k,l,tlimit=20.0,workers=1):
    nJ,nH=d.shape; bg=d[0,0]
    Y=range(1,nJ); Z=range(1,nH)
    rare=(d!=bg)
    M=cp_model.CpModel()
    r={(y,i):M.NewBoolVar('') for y in Y for i in range(m)}
    c={(z,i):M.NewBoolVar('') for z in Z for i in range(m)}
    ch_y={y:sum(r[y,i] for i in range(m)) for y in Y}
    ch_z={z:sum(c[z,i] for i in range(m)) for z in Z}
    for y in Y: M.Add(ch_y[y]<=1)
    for z in Z: M.Add(ch_z[z]<=1)
    for i in range(m):
        M.Add(sum(r[y,i] for y in Y)==k); M.Add(sum(c[z,i] for z in Z)==l)
    labcells={}
    for y in Y:
        for z in Z:
            if rare[y,z]:
                for i in range(m):
                    M.Add(r[y,i]+ch_z[z]-c[z,i]<=1)
                labcells.setdefault(int(d[y,z]),[]).append((y,z))
            else:
                for i in range(m):
                    M.Add(r[y,i]+c[z,i]<=1)
    for lab,cells in labcells.items():
        if len(cells)>1:
            # at most one cell with both chosen
            acts=[]
            for (y,z) in cells:
                a=M.NewBoolVar(''); M.Add(a>=ch_y[y]+ch_z[z]-1); acts.append(a)
            M.Add(sum(acts)<=1)
    # symmetry: block i's smallest row index < block i+1's -- use weighted ordering
    for i in range(m-1):
        M.Add(sum(y*r[y,i] for y in Y) < sum(y*r[y,i+1] for y in Y))
    S=cp_model.CpSolver(); S.parameters.max_time_in_seconds=tlimit; S.parameters.num_workers=workers
    st=S.Solve(M)
    if st in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        rows=np.zeros(nJ,bool); cols=np.zeros(nH,bool)
        for (y,i),v in r.items():
            if S.Value(v): rows[y]=True
        for (z,i),v in c.items():
            if S.Value(v): cols[z]=True
        return 'SAT',rows,cols
    return S.StatusName(st),None,None

def exact(d,w,lc,rc,rows,cols):
    nJ,nH=d.shape
    best=None
    for e in (0,1):
        rr=rows.copy(); cc=cols.copy()
        if e: rr[0]=cc[0]=True
        sc=score(rr,cc,d,w,lc,rc,nJ,nH,len(w),lc.max()+1,rc.max()+1)
        if best is None or sc[0]>best[0]: best=(sc[0],e,sc[1:])
    return best
