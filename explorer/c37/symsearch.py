# Search for f:{0,1}^n->{0,1}, deg<=d, f(0)=0, f(e_i)=1, invariant under a permutation group G.
import itertools, sys, time
from ortools.sat.python import cp_model
def closure(gens,n):
    G={tuple(range(n))}; frontier=list(G)
    while frontier:
        new=[]
        for g in frontier:
            for h in gens:
                p=tuple(h[g[i]] for i in range(n))
                if p not in G: G.add(p); new.append(p)
        frontier=new
    return G
def orbit_rep(mask,G,n):
    best=None
    for g in G:
        m=0
        for i in range(n):
            if mask>>i&1: m|=1<<g[i]
        if best is None or m<best: best=m
    return best
def search(n,d,gens,tl=300,workers=4,verbose=True):
    G=closure(gens,n)
    if verbose: print('|G|=',len(G),flush=True)
    rep={}
    for mask in range(1<<n): pass
    # orbits of small subsets (|S|<=d)
    small=[m for m in range(1<<n) if bin(m).count('1')<=d]
    srep={m:orbit_rep(m,G,n) for m in small}
    M=cp_model.CpModel(); var={}
    for r in set(srep.values()):
        k=bin(r).count('1')
        if k==0: var[r]=0
        elif k==1: var[r]=1
        else: var[r]=M.NewIntVar(-10**4,10**4,f"c{r}")
    # point orbits
    seen=set(); npts=0
    for x in range(1<<n):
        rx=orbit_rep(x,G,n) if len(G)>1 else x
        if rx in seen: continue
        seen.add(rx); npts+=1
        # sum over S subset of rx, |S|<=d
        bits=[i for i in range(n) if rx>>i&1]
        cnt={}
        for k in range(0,min(d,len(bits))+1):
            for S in itertools.combinations(bits,k):
                m=sum(1<<i for i in S); r=srep[m]; cnt[r]=cnt.get(r,0)+1
        e=sum(var[r]*c for r,c in cnt.items())
        if isinstance(e,int):
            if e not in (0,1): return 'INFEASIBLE(trivial)',None
        else:
            M.Add(e>=0); M.Add(e<=1)
    if verbose: print('vars',len(var),'point orbits',npts,flush=True)
    S=cp_model.CpSolver(); S.parameters.max_time_in_seconds=tl; S.parameters.num_workers=workers
    st=S.Solve(M); name=S.StatusName(st)
    sol=None
    if name in('OPTIMAL','FEASIBLE'):
        sol={r:(S.Value(v) if not isinstance(v,int) else v) for r,v in var.items()}
    return name,sol
def cyc(n,shift=1): return [ (i+shift)%n for i in range(n)]
if __name__=='__main__':
    # controls
    # PSL(2,5) on P^1(F5): points 0..4, inf=5
    def mob(a,b,c,dd,q):
        out=[]
        for x in range(q+1):
            if x==q: y= q if c==0 else (a*pow(c,-1,q))%q
            else:
                num=(a*x+b)%q; den=(c*x+dd)%q
                y= q if den==0 else num*pow(den,-1,q)%q
            out.append(y)
        return out
    print('Kushilevitz control', search(6,3,[mob(1,1,0,1,5),mob(4,0,0,1,5),mob(0,-1%5,1,0,5)])[0])
    # S3 wr S3 on 9
    g1=[1,0,2,3,4,5,6,7,8]; g2=[1,2,0,3,4,5,6,7,8]; g3=[3,4,5,0,1,2,6,7,8]; g4=[3,4,5,6,7,8,0,1,2]
    print('NAE∘NAE control', search(9,4,[g1,g2,g3,g4])[0])
    print('n=10 d=4 with C10 (should be infeasible)', search(10,4,[cyc(10)],tl=60)[0])
