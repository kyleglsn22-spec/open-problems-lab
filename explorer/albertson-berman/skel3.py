import sys, random, itertools, networkx as nx
from ortools.sat.python import cp_model
from skel import induced_forests
from gad3 import faces, SUBS
from anneal_tri import random_triangulation, flip
R=(15,8,7,7,7); Q=(12,6,6,6,5)
def solve(H,num,den,EG,FG,VG,cap=6,tl=60):
    h=H.number_of_nodes(); E=list(H.edges()); Fc=faces(H); F=induced_forests(H)
    m=cp_model.CpModel(); terms_by=[]
    ev={}
    for e in E:
        for gi,g in enumerate(EG):
            for o in (0,1):
                if o and g[2]==g[3]: continue
                ev[('e',e,gi,o)]=m.NewIntVar(0,cap,"")
    for f in Fc:
        for gi,(k,p) in enumerate(FG):
            seenp=set()
            for perm in itertools.permutations(range(3)):
                q=tuple(p[SUBS.index(tuple(sorted(perm[i] for i in X)))] for X in SUBS)
                if q in seenp: continue
                seenp.add(q)
                ev[('f',f,gi,q)]=m.NewIntVar(0,cap,"")
    for v in H:
        for gi,g in enumerate(VG): ev[('v',v,gi,0)]=m.NewIntVar(0,cap,"")
    for S in F:
        t=[den*len(S)-num*h]
        for key,x in ev.items():
            if key[0]=='e':
                _,e,gi,o=key; k,p0,pb,pc,pbc=EG[gi]; u,w=e if o==0 else (e[1],e[0])
                iu,iw=u in S,w in S; p=pbc if iu and iw else pb if iu else pc if iw else p0
            elif key[0]=='f':
                _,f,gi,q=key; k=FG[gi][0]; X=tuple(i for i in range(3) if f[i] in S)
                if len(X)==3: continue  # impossible (triangle)
                p=q[SUBS.index(X)]
            else:
                _,v,gi,_=key; k,p0,p1=VG[gi]; p=p1 if v in S else p0
            t.append(x*(den*p-num*k))
        m.Add(sum(t)<=0)
    m.Minimize(sum(ev.values()))
    s=cp_model.CpSolver(); s.parameters.max_time_in_seconds=tl; s.parameters.num_workers=4
    st=s.Solve(m)
    if st in (cp_model.OPTIMAL,cp_model.FEASIBLE): return {k:s.Value(x) for k,x in ev.items() if s.Value(x)}
    return None
