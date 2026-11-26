import itertools, random, sys
F7=[(0,1,2),(0,3,4),(0,5,6),(1,3,5),(2,4,6)]
def has_f7(E):
    Es=set(frozenset(e) for e in E)
    inc={}
    for e in E:
        for v in e: inc.setdefault(v,[]).append(e)
    for v,es in inc.items():
        if len(es)<3: continue
        for e1,e2,e3 in itertools.permutations(es,3):
            o1=[x for x in e1 if x!=v]; o2=[x for x in e2 if x!=v]; o3=[x for x in e3 if x!=v]
            for g1,g2 in (o1,o1[::-1]):
              for g3,g4 in (o2,o2[::-1]):
                for g5,g6 in (o3,o3[::-1]):
                  if frozenset((g1,g3,g5)) in Es and frozenset((g2,g4,g6)) in Es: return True
    return False
def tau(n,E):
    masks=[sum(1<<v for v in e) for e in E]
    for k in range(n+1):
        for S in itertools.combinations(range(n),k):
            s=sum(1<<v for v in S)
            if all(s&m for m in masks): return k
# sanity: AG(2,3) minus two points is F7 (contains F7 and has 5 edges on 7 pts)
pts=[(x,y) for x in range(3) for y in range(3)]
lines=set()
for p,q in itertools.combinations(pts,2):
    r=((-p[0]-q[0])%3,(-p[1]-q[1])%3); lines.add(frozenset((p,q,r)))
dele={pts[0],pts[1]}
rest=[l for l in lines if not (l&dele)]
idx={p:i for i,p in enumerate(sorted(set(pts)-dele))}
R=[tuple(idx[p] for p in l) for l in rest]
print("AG(2,3)-2pts edges:",len(R),"contains F7:",has_f7(R), "F7 contains F7:",has_f7(F7))
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 0)
worst=None; cnt=0
for trial in range(int(sys.argv[2]) if len(sys.argv)>2 else 2000):
    n=random.randint(9,14)
    T=list(itertools.combinations(range(n),3)); random.shuffle(T)
    E=[]; used=set()
    stop=random.random()
    for t in T:
        ps={frozenset(p) for p in itertools.combinations(t,2)}
        if ps&used: continue
        if has_f7(E+[t]): continue
        E.append(t); used|=ps
        # evaluate at random intermediate points too
        if random.random()<0.15:
            s=5*n+3*len(E)-17*tau(n,E); cnt+=1
            assert s>=0,(n,E)
            if worst is None or s<worst[0]: worst=(s,n,list(E))
    s=5*n+3*len(E)-17*tau(n,E); cnt+=1
    assert s>=0,(n,E)
    if worst is None or s<worst[0]: worst=(s,n,list(E))
print("checked",cnt,"min slack",worst[0],"n",worst[1],"m",len(worst[2]))
