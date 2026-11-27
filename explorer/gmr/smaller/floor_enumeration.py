# exhaustive: block designs with commuting free background, cost L*prod(k+1)(l+1) < 131072, ratio>1
from fractions import Fraction
LIM=131072
res=[]
def rec(blocks,HJ,minb):
    # evaluate
    if len(blocks)>=1:
        for e in (0,1):
            nb=len(blocks); bg=1 if (nb>1 or e) else 0
            P=sum(k*l for k,l in blocks); L=P+bg
            R4=sum(k*(l+bg) for k,l in blocks)+e; R1=sum(l*(k+bg) for k,l in blocks)+e
            r2=max(l for k,l in blocks)+bg; r3=max(k for k,l in blocks)+bg
            if L**3>R1*R4*r2*r3 and L*HJ<LIM:
                res.append((L*HJ,float(Fraction(L**3,R1*R4*r2*r3)),tuple(blocks),e))
    for k in range(1,200):
        for l in range(1,200):
            if (k,l)<minb: continue
            nHJ=HJ*(k+1)*(l+1)
            P=sum(a*b for a,b in blocks)+k*l
            if nHJ*(P+1)>=LIM: 
                if l==1 or (k+1)*(l+1)*HJ*(P+1)>=LIM: break
                continue
            rec(blocks+[(k,l)],nHJ,(k,l))
rec([],1,(0,0))
res.sort()
print(len(res))
for r in res[:12]: print(r)
