# Cross-check for Lab/LocalAntimagic: the degrees a(r,i) = 4^(2^r - 2^(r-(i+1))) reproduce the paper's
# H_{2,1} = Cat(15,63) and H_{3,1} = Cat(255,4094,16383); the `Separated` inequalities hold; and random
# labellings of H_{2,1}, H_{2,2} and H_{3,1} have pairwise distinct vertex weights.
import random
def a(r,i): return 4**(2**r-2**(r-(i+1)))
def leaves(d):
    r=len(d); return [d[i]-1 if i in (0,r-1) else d[i]-2 for i in range(r)]
assert leaves([a(2,i) for i in range(2)])==[15,63]
assert leaves([a(3,i) for i in range(3)])==[255,4094,16383]
def separated(d):
    r=len(d); m=sum(d)+1-r
    return all(d[i]>=2 and 2*m<d[i]*(d[i]+1) for i in range(r)) and \
        all(2*d[i]*m+d[i]<d[i+1]*(d[i+1]+1)+d[i]*d[i] for i in range(r-1))
for r in range(2,6):
    for t in range(1,4):
        assert separated([t*a(r,i) for i in range(r)]), (r,t)
def random_check(d,trials):
    r=len(d); p=leaves(d)
    edges=[(('s',i),('s',i+1)) for i in range(r-1)]+[(('s',i),('l',i,j)) for i in range(r) for j in range(p[i])]
    m=len(edges); assert m==sum(d)+1-r
    for _ in range(trials):
        labels=random.sample(range(1,m+1),m); w={}
        for (u,v),x in zip(edges,labels):
            w[u]=w.get(u,0)+x; w[v]=w.get(v,0)+x
        assert len(set(w.values()))==len(w)
for d,tr in (([a(2,0),a(2,1)],2000),([2*a(2,0),2*a(2,1)],1000),([a(3,i) for i in range(3)],50)):
    random_check(d,tr)
# T_3 = Cat(8,7,25) from the paper is not "Separated" in our sense (equal adjacent degrees), as expected
assert not separated([9,9,26])
print('ok')
