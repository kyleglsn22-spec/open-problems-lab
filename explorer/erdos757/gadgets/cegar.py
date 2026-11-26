import sys, itertools, random, time, json
from itertools import combinations
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from gad import nullspace, realize

def violation(n, edges, y):
    """return a relation (as coefficient dict) violated identically, or None"""
    if len(set(y))<n:
        for i,k in combinations(range(n),2):
            if y[i]==y[k]: return {i:1,k:-1}
    sums={}
    for i in range(n):
        for k in range(i+1,n):
            s=y[i]+y[k]
            for (a,b) in sums.get(s,[]):
                if len({a,b,i,k})==4: return {i:1,k:1,a:-1,b:-1}
            sums.setdefault(s,[]).append((i,k))
    E=set((min(i,k),j,max(i,k)) for i,j,k in edges)
    for j in range(n):
        for (i,k) in sums.get(2*y[j],[]):
            if j in (i,k): continue
            if (i,j,k) not in E: return {i:1,k:1,j:-2}
    return None
def holds(n, edges, rel, tries=2):
    for _ in range(tries):
        y=realize(n,edges)
        if sum(c*y[v] for v,c in rel.items())!=0: return False
    return True
def minimal_conflict(n, edges, rel):
    cur=list(edges)
    for e in list(cur):
        t=[x for x in cur if x!=e]
        if holds(n,t,rel): cur=t
    return cur

def solve(n, G, pi, seed=0, maxit=20000, verbose=True):
    a,b,p,q=0,1,2,3
    pool=IDPool(); V=range(n)
    ev={}
    for j in V:
        for i,k in combinations([v for v in V if v!=j],2):
            ev[(i,j,k)]=pool.id(('e',i,j,k))
    cl=[]
    # each vertex middle at most once
    for j in V:
        lits=[ev[(i,j,k)] for i,k in combinations([v for v in V if v!=j],2)]
        cl+=CardEnc.atmost(lits,1,vpool=pool,encoding=EncType.seqcounter).clauses
    # linearity: each pair in at most one edge
    pe={pr:[] for pr in combinations(V,2)}
    for (i,j,k),x in ev.items():
        for pr in combinations(sorted((i,j,k)),2): pe[pr].append(x)
    for pr,l in pe.items():
        cl+=CardEnc.atmost(l,1,vpool=pool,encoding=EncType.seqcounter).clauses
    mid=lambda j:[ev[(i,j,k)] for i,k in combinations([v for v in V if v!=j],2)]
    # chain compat: a and p not both middles, b and q not both
    for u,w in ((a,p),(b,q)):
        for x in mid(u):
            for z in mid(w): cl.append([-x,-z])
    # {a,b} edge and {p,q} edge not both
    for x in pe[(a,b)]:
        for z in pe[(p,q)]: cl.append([-x,-z])
    # growth constraints W[s][t] <= G + pi[t]-pi[s]
    R=[v for v in V if v not in (a,b)]
    byset={}
    for (i,j,k),x in ev.items(): byset.setdefault(frozenset((i,j,k)),[]).append(x)
    for s in range(4):
        Sab=[v for v,bit in ((a,s>>1),(b,s&1)) if bit]
        for t in range(4):
            U=G+pi[t]-pi[s]
            tp,tq=t>>1,t&1
            forced=[v for v,bit in ((p,tp),(q,tq)) if bit]
            others=[v for v in R if v not in (p,q)]
            need=U+1-len(forced)
            if need<0: return 'UNSAT-trivial',None
            if need>len(others): continue
            for X in combinations(others,need):
                Y=set(X)|set(forced)|set(Sab)
                lits=[x for tr,xs in byset.items() if tr<=Y for x in xs]
                if not lits: return 'UNSAT-trivial',None
                cl.append(lits)
    S=Cadical153(bootstrap_with=cl)
    it=0; nconf=0
    while True:
        it+=1
        if not S.solve(): return 'UNSAT',it
        mdl=set(l for l in S.get_model() if l>0)
        E=[e for e,x in ev.items() if x in mdl]
        y=realize(n,E)
        rel=violation(n,E,y)
        if rel is None:
            return 'SAT',dict(edges=E,y=y)
        conf=minimal_conflict(n,E,rel)
        S.add_clause([-ev[e] for e in conf]); nconf+=1
        if verbose and it%200==0: print('  it',it,'conf size',len(conf),flush=True)
        if it>maxit: return 'TIMEOUT',it

if __name__=="__main__":
    n=int(sys.argv[1]); G=int(sys.argv[2])
    pis=set()
    for pi in itertools.product(range(3),repeat=4):
        m=min(pi); pis.add(tuple(x-m for x in pi))
    for pi in sorted(pis):
        t=time.time()
        r,info=solve(n,G,pi)
        print(pi,r,info if r!='SAT' else json.dumps(info),round(time.time()-t,1),flush=True)
        if r=='SAT': break
