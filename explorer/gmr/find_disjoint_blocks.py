import itertools,sys
W=int(sys.argv[1]); NB=int(sys.argv[2])
N=1<<W
sets=set()
for a,b,c,d in itertools.product(range(1,N),repeat=4):
    L=[a,b,a^b,c,d,c^d,a^c,b^d,a^b^c^d]
    if 0 in L or len(set(L))<9: continue
    m=0
    for l in L: m|=1<<l
    sets.add(m)
sets=sorted(sets); print(len(sets))
# find NB pairwise disjoint
def rec(start,used,k,chosen):
    if k==0: return chosen
    for i in range(start,len(sets)):
        s=sets[i]
        if s&used==0:
            r=rec(i+1,used|s,k-1,chosen+[s])
            if r: return r
    return None
r=rec(0,0,NB,[])
print(r and [[j for j in range(N) if s>>j&1] for s in r])
