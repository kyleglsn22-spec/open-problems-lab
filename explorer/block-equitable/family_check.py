# Cross-check for Lab/BlockEquitable/Family.lean: builds G_{d,k} exactly as in the Lean file and checks
# the explicit (k+d)-colouring (proper, classes of size 3 or 4), alpha(G,x) >= 4 everywhere,
# alpha(G,v) = alpha(G,w) = 4, alpha(G-u, v) = alpha(G-u, w) = 3, and clique number k.
import itertools
def f(d,j,t):
    if j==0: return 1 if t==0 else (t+d if t<=3*d-3 else t+d+1)
    if j==1: return t+1 if t<d else (t+d if t<=3*d-3 else t+d+1)
    if j==2: return 0 if t==0 else (t+1 if t<=2*d-2 else t+d+1)
    return 0 if t==0 else (t+1 if t<=3*d-2 else (4*d-2 if t==3*d-1 else t+d+1))
def check(d,k):
    m=4*d-1; anc=lambda j: 0 if j<2 else 1
    V=[('q',i) for i in range(m)]+[('u',)]+[('p',j,t) for j in range(4) for t in range(k-1)]
    def adj(a,b):
        if a==b: return False
        if a[0]=='q' and b[0]=='q': return True
        if {a[0],b[0]}=={'q','u'}: return (a if a[0]=='q' else b)[1]==2
        if {a[0],b[0]}=={'q','p'}:
            x,y=(a,b) if a[0]=='q' else (b,a); return x[1]==anc(y[1])
        if a[0]=='p' and b[0]=='p': return a[1]==b[1]
        return False
    n=len(V); q=k+d; assert n==4*(k+d-1)
    col={a:(a[1] if a[0]=='q' else 0 if a[0]=='u' else f(d,a[1],a[2])) for a in V}
    assert all(0<=col[a]<q for a in V)
    assert all(col[a]!=col[b] for a in V for b in V if adj(a,b))
    sizes=[sum(col[a]==c for a in V) for c in range(q)]
    assert set(sizes)<={n//q,-(-n//q)}, sizes
    nbr={a:{b for b in V if adj(a,b)} for a in V}
    def alpha(x,banned=()):
        cand=[y for y in V if y!=x and y not in nbr[x] and y not in banned]; best=0
        def go(i,cur):
            nonlocal best; best=max(best,len(cur))
            for j in range(i,len(cand)):
                if all(cand[j] not in nbr[z] for z in cur): go(j+1,cur+[cand[j]])
        go(0,[]); return best+1
    v,w,u=('q',0),('q',1),('u',)
    assert alpha(v)==4 and alpha(w)==4 and alpha(v,(u,))==3 and alpha(w,(u,))==3
    assert all(alpha(x)>=4 for x in V)
    om=max(2+len(nbr[a]&nbr[b]) for a in V for b in nbr[a])
    assert om==k, om
for d in range(2,5):
    for k in range(4*d-1,4*d+3):
        check(d,k); print('ok d=%d k=%d'%(d,k))
