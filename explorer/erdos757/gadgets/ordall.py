import sys, time, json
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
import ord as OR
n,num,den=map(int,sys.argv[1:4]); PM=4
O=OR.Ordered(n)
seen=set(); P2=[]
for p in range(1,n-1):
    for q in range(1,n-1):
        if p==q or (n-1-q,n-1-p) in seen: continue
        seen.add((p,q)); P2.append((p,q))
t0=time.time(); cl=list(O.base); sel={}
for (p,q) in P2:
    y=O.pool.id(('port',p,q)); sel[(p,q)]=y
    for c in O.growth_clauses(p,q,num,den,PM): cl.append(c+[-y])
cl+=CardEnc.atleast(list(sel.values()),1,vpool=O.pool,encoding=EncType.pairwise).clauses
print('clauses',len(cl),round(time.time()-t0,1),flush=True)
S=Cadical153(bootstrap_with=cl); db=[]; it=0
while True:
    it+=1
    if not S.solve(): print('UNSAT all ports, iters',it,'conflicts',len(db),round(time.time()-t0,1),flush=True); break
    m=set(l for l in S.get_model() if l>0)
    E=[e for e,x in O.ev.items() if x in m]; ports=[pq for pq,y in sel.items() if y in m]
    conf,yv=OR.conflict(n,E)
    if conf is None:
        print('FOUND',json.dumps(dict(n=n,G=[num,den],ports=ports,edges=E,y=[int(v) for v in yv])),flush=True); break
    pat=OR.relpattern(conf); db.append(pat)
    for c in O.lifted(pat): S.add_clause(c)
    if it%20==0: print(it,len(db),round(time.time()-t0,1),flush=True)
