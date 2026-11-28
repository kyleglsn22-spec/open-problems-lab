"""Certified differences D_l vs U_l: gap g realized (start < 105) in one type only, and
excluded for all windows with every position >= 105 by the constraint system (same-type shifts)."""
import sys, math
from fractions import Fraction
phi=(1+5**.5)/2
rho=(2+phi)/5; eta=(3-phi)/5
JS=[int(x) for x in sys.argv[3].split(',')] if len(sys.argv)>3 else [2,3,4,5,6]
fibs=[0,1,1,2,3,5,8,13,21,34]
th={j:(phi**(j-2)+1)/(5**.5*phi**(j-1)) for j in range(2,10)}
sdown={j:(-1)**j*fibs[j] for j in range(2,10)}
def feasible_D(D):
    """D: list of bools (positions 0..g). same-type (down) shifts only. returns True if some x works."""
    g=len(D)-1
    bps=sorted({0.0,1.0}|{(1-(j*phi)%1)%1 for j in range(g+1)})
    for lo,hi in zip(bps,bps[1:]):
        if hi-lo<1e-12: continue
        mid=(lo+hi)/2
        L,H=lo,hi
        ok=True
        c=[(j*phi)%1-(1 if (mid+(j*phi)%1)>=1 else 0) for j in range(g+1)]
        for j in range(g+1):
            if D[j]: H=min(H,rho-c[j])
            else: L=max(L,eta-c[j])
            if L>=H-1e-12: ok=False;break
        if not ok: continue
        for p in range(g+1):
            if not D[p]: continue
            for jj in JS:
                q=p+sdown[jj]
                if 0<=q<=g and not D[q]: H=min(H,th[jj]-c[p])
        if L<H-1e-12: return True
    return False
from functools import lru_cache
def excluded(l,g):
    # DFS over compositions of g into l parts in [1,5] (gap6 excluded separately); prune infeasible prefixes.
    stack=[((True,),0,0)]
    while stack:
        D,tot,k=stack.pop()
        if k==l:
            if tot==g: return False
            continue
        for s in range(1,6):
            if tot+s>g or tot+s+(l-k-1)>g or tot+s+5*(l-k-1)<g: continue
            D2=D+(False,)*(s-1)+(True,)
            if feasible_D(list(D2)): stack.append((D2,tot+s,k+1))
    return True
# small-n tables
LIM=4000
THR=int(sys.argv[4]) if len(sys.argv)>4 else 105
fib=[0,1]
while fib[-1]<10*LIM: fib.append(fib[-1]+fib[-2])
kind={}
for t in range(2,len(fib)-1):
    ft,f1=fib[t],fib[t-1]
    for a in range(1,ft+1):
        for b in range(a,ft+1):
            n=a*ft+b*f1
            if n<LIM: kind[n]=t%2
Dl=[n for n in range(2,LIM) if kind[n]==0]; Ul=[n for n in range(2,LIM) if kind[n]==1]
def small_gaps(S,l): return {S[i+l]-S[i] for i in range(len(S)-l) if S[i]<THR}
L1,L2=int(sys.argv[1]),int(sys.argv[2])
for l in range(L1,L2+1):
    sd,su=small_gaps(Dl,l),small_gaps(Ul,l)
    res=[]
    for g in sorted(sd^su):
        if excluded(l,g): res.append(('D' if g in sd else 'U', g))
    print(l,res,flush=True)
