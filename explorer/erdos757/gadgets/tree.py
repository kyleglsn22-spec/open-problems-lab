import numpy as np, itertools, sys, json
from gad import masks_indep
def tree_ratio(n, edges, a, b, ports_list, D=14):
    idx,sz=masks_indep(n,edges)
    bit=lambda v: ((idx>>v)&1)
    base=sz-bit(a)-bit(b); s=2*bit(a)+bit(b)
    ts=[2*bit(p)+bit(q) for (p,q) in ports_list]
    F=np.zeros(4)  # depth -1 : no subtree
    ncop=0; t=n-2
    for d in range(D+1):
        val=base.astype(float)+sum(F[tt] for tt in ts)
        Fn=np.full(4,-1e9)
        np.maximum.at(Fn,s,val)
        F=Fn; ncop=1+len(ports_list)*ncop
    # root: plus a,b themselves
    tot=max(F[st]+ (st>>1)+(st&1) for st in range(4))
    N=ncop*t+2
    return tot/N, tot, N
if __name__=="__main__":
    O=[0,49,75,83,98,101,117,119,121,159,269]; st=set(O); n=11
    E=[(O.index(a),O.index((a+c)//2),O.index(c)) for a,c in itertools.combinations(O,2) if (a+c)%2==0 and (a+c)//2 in st]
    print('chain', tree_ratio(n,E,0,10,[(5,7)],D=60))
    best=[]
    pairs=[(p,q) for p in range(1,10) for q in range(1,10) if p!=q]
    for P1,P2 in itertools.combinations(pairs,2):
        if len(set(P1)|set(P2))<4: continue
        r=tree_ratio(n,E,0,10,[P1,P2],D=14)
        best.append((r[0],P1,P2))
    best.sort(); print(best[:5])
