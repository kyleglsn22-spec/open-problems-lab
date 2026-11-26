import itertools
# top items: (name, eps, block idx or None, which ('a'/'d'), Fpart tuple)
items=[('c',None,None,(5,5))]
for i in range(3):
    for w in 'ad':
        F=[0,0]
        if i<2: F[i]=3
        items.append((w+str(i),i,w,tuple(F)))
for i in range(2):
    for _ in range(2):
        F=[0,0]; F[i]=2; items.append(('t'+str(i),None,None,tuple(F)))
reqs=set()
for T in itertools.combinations(range(len(items)),6):
    F=[sum(items[j][3][m] for j in T)%6 for m in range(2)]
    if 1 in F: continue
    eps=1 if 0 in T else 0
    pats=[]
    for i in range(3):
        a=int(any(items[j][1]==i and items[j][2]=='a' for j in T))
        d=int(any(items[j][1]==i and items[j][2]=='d' for j in T))
        pats.append((eps,a,d))
    reqs.add(tuple(pats))
for r in sorted(reqs): print(r)
print(len(reqs))
