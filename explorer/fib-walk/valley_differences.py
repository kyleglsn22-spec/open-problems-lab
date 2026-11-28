"""Differences D_l vs U_l for l in [L1, L2], computed from all members below LIM (numerical evidence only).
For each difference, report where its first windows start and the nearest "valley" f_t f_{t+1}
(see valleys.md) as (t, start - f_t f_{t+1}). Only windows ending below LIM/3 are reported.
Usage: python3 valley_differences.py LIM L1 L2"""
import numpy as np
def kinds(LIM):
    fib=[0,1]
    while fib[-1]<10*LIM: fib.append(fib[-1]+fib[-2])
    kind=np.full(LIM+1,-1,dtype=np.int8)
    for t in range(2,len(fib)-1):
        ft,f1=fib[t],fib[t-1]
        if ft+f1>LIM: break
        for a in range(1,ft+1):
            if a*(ft+f1)>LIM: break
            bmax=min(ft,(LIM-a*ft)//f1)
            if bmax<a: continue
            kind[a*ft+np.arange(a,bmax+1)*f1]=t%2
    return kind
import numpy as np,sys
LIM=int(sys.argv[1]); L1=int(sys.argv[2]); L2=int(sys.argv[3])
k=kinds(LIM)
D=np.nonzero(k==0)[0]; U=np.nonzero(k==1)[0]
fib=[0,1]
while len(fib)<40: fib.append(fib[-1]+fib[-2])
valleys=[fib[t]*fib[t+1] for t in range(4,30)]
def near(x):
    # nearest valley index t and relative offset
    best=min(range(4,30),key=lambda t:abs(np.log(x/(fib[t]*fib[t+1]))))
    return best, x-fib[best]*fib[best+1]
for l in range(L1,L2+1):
    gd=D[l:]-D[:-l]; gu=U[l:]-U[:-l]
    # only trust windows ending below LIM/3
    md=D[l:]<LIM//3; mu=U[l:]<LIM//3
    sd=set(np.unique(gd).tolist()); su=set(np.unique(gu).tolist())
    res=[]
    for g in sorted(set(np.unique(gd[md]).tolist())-su):
        i=np.nonzero(gd==g)[0]; res.append(('D',g,len(i))+tuple(near(int(D[j])) for j in i[:3]))
    for g in sorted(set(np.unique(gu[mu]).tolist())-sd):
        i=np.nonzero(gu==g)[0]; res.append(('U',g,len(i))+tuple(near(int(U[j])) for j in i[:3]))
    print(l,res,flush=True)
