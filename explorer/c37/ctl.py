# Positive controls: the true profile of a known function must pass lvl1, lvl2b and lvl3t.
import itertools, sys
from math import comb
import lvl3t, lvl2b
def multilinear(f,n):
    c={}
    for S in range(1<<n):
        v=0; T=S
        while True:
            v+= (-1)**(bin(S).count('1')-bin(T).count('1'))*f(T)
            if T==0: break
            T=(T-1)&S
        c[S]=v
    return c
def profile(f,n,d):
    c=multilinear(f,n)
    assert all(v==0 for S,v in c.items() if bin(S).count('1')>d), 'degree too big'
    return [sum(v for S,v in c.items() if bin(S).count('1')==l) for l in range(d+1)]
def bit(x,i): return x>>i&1
def nae(a,b,c): return 0 if a==b==c else 1
def naenae(x): return nae(nae(bit(x,0),bit(x,1),bit(x,2)),nae(bit(x,3),bit(x,4),bit(x,5)),nae(bit(x,6),bit(x,7),bit(x,8)))
K=[(0,2,3),(0,1,4),(0,3,4),(1,2,3),(1,2,4),(0,1,5),(0,2,5),(1,3,5),(2,4,5),(3,4,5)]
def kush(x,off=0):
    z=[bit(x,off+i) for i in range(6)]
    return sum(z)-sum(z[i]*z[j] for i in range(6) for j in range(i+1,6))+sum(z[a]*z[b]*z[c] for a,b,c in K)
cases={
 '(10,5) OR(NAE∘NAE, x)': (10,5, lambda x: naenae(x)|bit(x,9)),
 '(9,5) OR(Kush, NAE)':   (9,5, lambda x: kush(x)|nae(bit(x,6),bit(x,7),bit(x,8))),
 '(9,5) XOR(Kush, NAE)':  (9,5, lambda x: kush(x)^nae(bit(x,6),bit(x,7),bit(x,8))),
 '(9,4) NAE∘NAE':         (9,4, naenae),
 '(6,3) Kushilevitz':     (6,3, kush),
}
for name,(n,d,f) in cases.items():
    assert f(0)==0 and all(f(1<<i)==1 for i in range(n))
    C=profile(f,n,d)
    lvl3t.setup(n,d,C)
    r2=lvl2b.check(n,d,C,120)
    r3=lvl3t.main(120)
    print(name,C,'level2:',r2,'level3:',r3,flush=True)
