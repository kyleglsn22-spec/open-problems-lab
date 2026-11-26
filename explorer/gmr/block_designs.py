import math
res=[]
for a in range(1,5):
 for c in range(1,5):
  ra,rc=2**a-1,2**c-1
  for b1 in range(1,20):
   for b2 in range(1,20):
    for dr in range(1,b2+1):
     e=b1*dr
     if e%b2: continue
     dc=e//b2
     if dc>b1: continue
     I=e*ra*rc; t1=b1*ra; t2=b2*rc; d1=dr*rc; d2=dc*ra
     R=(1+I)**3/((1+t2+I)*(1+t1+I)*(1+d1)*(1+d2))
     if R>1:
      w=math.ceil(math.log2(I+1)); dims=a*b1+c*b2+w
      res.append((dims,R,a,c,b1,b2,dr,dc,I))
res.sort()
for r in res[:12]: print(r)
