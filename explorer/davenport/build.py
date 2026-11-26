# Builds the zero-sumfree sequence of Gao-Geroldinger-Wang-Zeng (arXiv:2611.24775 v3, proof of
# Theorem 1.1) over C_n^{5k}, n = 2k, k odd. Element order matches the Lean file for k = 3.
# Build the GGWZ v3 sequence S over C_n^{5k}, n=2k, k odd.
import itertools, sys
def build(k):
    n=2*k; R=5*k
    def vec(**kw): return [0]*R
    P=lambda i,j: 4*i+j          # block i coords 0..3 (e1,e2,e3,f)
    Fc=lambda i: 4*k+i           # i in 0..k-2
    U=5*k-1
    S=[]
    def add(v,m=1):
        for _ in range(m): S.append(tuple(x%n for x in v))
    s=(1-k)//2; v=(k+1)//2
    for i in range(k):
        e=[[0]*R for _ in range(3)]
        for j in range(3): e[j][P(i,j)]=1
        f=[0]*R; f[P(i,3)]=1
        z=[0]*R
        for j in range(3): z[P(i,j)]=1
        z[P(i,3)]=1-3*k
        add(z); add(f,n-3)
        for j in range(3):
            add(e[j],k-1); ej=e[j][:]; ej[P(i,3)]=1; add(ej,k)
    for i in range(k-1):
        F=[0]*R; F[Fc(i)]=1; add(F,n-2)
    def blk(i,e1,e2,e3,fc):
        w=[0]*R; w[P(i,0)]=e1; w[P(i,1)]=e2; w[P(i,2)]=e3; w[P(i,3)]=fc; return w
    center=[0]*R; center[U]=1
    for i in range(k): center[P(i,3)]+=s
    for i in range(k-1): center[Fc(i)]+=1-v
    add(center)
    for i in range(k):
        a=blk(i,-1,1,0,s); d=blk(i,0,-1,1,s)
        for base in (a,d):
            t=base[:]; t[U]+=1
            if i<k-1: t[Fc(i)]+=k
            add(t)
        if i<k-1:
            t=[0]*R; t[U]=1; t[Fc(i)]=v; add(t,2)
    return n,R,S
if __name__=="__main__":
    n,R,S=build(int(sys.argv[1]))
    print(n,R,len(S),R*(n-1)+1)
