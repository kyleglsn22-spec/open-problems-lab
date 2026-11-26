import itertools, sys, time
from pysat.solvers import Cadical153
from pysat.card import CardEnc
class Enc:
    def __init__(s): s.n=0; s.cl=[]
    def v(s): s.n+=1; return s.n
def build(comps, m, fix0=True, domains=None):
    # comps: list of (rank, targets) ; targets list of tuples of length rank
    E=Enc(); coords=[]
    for j,(b,A) in enumerate(comps):
        for c in range(b): coords.append((j,c))
    C=len(coords)
    X=[[[E.v() for v in range(6)] for c in range(C)] for i in range(m)]
    for i in range(m):
        for c in range(C):
            E.cl.append(X[i][c][:])
            for a,b in itertools.combinations(X[i][c],2): E.cl.append([-a,-b])
            if fix0 and i==0: E.cl.append([X[i][c][0]])
            if domains and domains[c] is not None and not (fix0 and i==0):
                for v in range(6):
                    if v not in domains[c]: E.cl.append([-X[i][c][v]])
    S={}
    def getS(P):
        if P in S: return S[P]
        if len(P)==1: S[P]=X[P[0]]; return S[P]
        prev=getS(P[:-1]); i=P[-1]; cur=[]
        for c in range(C):
            sv=[E.v() for w in range(6)]
            for a,b in itertools.combinations(sv,2): E.cl.append([-a,-b])
            for x in range(6):
                for val in range(6):
                    E.cl.append([-prev[c][x],-X[i][c][val],sv[(x+val)%6]])
            cur.append(sv)
        S[P]=cur; return cur
    for T in itertools.combinations(range(m),6):
        ST=getS(T); zs=[]; off=0
        for j,(b,A) in enumerate(comps):
            z=E.v(); zs.append(z)
            ys=[]
            for vec in A:
                if b==1: ys.append(ST[off][vec[0]])
                else:
                    y=E.v(); ys.append(y)
                    for c in range(b): E.cl.append([-y,ST[off+c][vec[c]]])
            E.cl.append([-z]+ys)
            off+=b
        E.cl.append(zs)
    return E,X,coords
def run(comps,m,timeout=None,**kw):
    E,X,coords=build(comps,m,**kw)
    sol=Cadical153(bootstrap_with=E.cl)
    t0=time.time(); ok=sol.solve(); dt=time.time()-t0
    res=None
    if ok:
        mdl=set(l for l in sol.get_model() if l>0)
        res=[[next(v for v in range(6) if X[i][c][v] in mdl) for c in range(len(coords))] for i in range(m)]
    return ok,res,dt,E.n,len(E.cl)
if __name__=="__main__":
    from lib import *
    A4=targets(ggwz4(),4)
    ok,res,dt,nv,nc=run([(4,A4)]*3+[(1,[(1,)])]*2,11)
    print(ok,dt,nv,nc); 
    if res:
        for row in res: print(row)
