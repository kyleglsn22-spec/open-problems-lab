import itertools, pickle
exec(open('req.py').read().split('for r in sorted')[0])
n=6
pats=[p for p in itertools.product((0,1),repeat=3) if p!=(0,0,0)]
def achievable(r,L):
    G=list(itertools.product(range(n),repeat=r)); idx={g:i for i,g in enumerate(G)}
    ad=lambda g,h: tuple((a+b)%n for a,b in zip(g,h))
    res=set()
    for W in itertools.combinations_with_replacement(G[1:],L):
        R={tuple([0]*r)}; bad=False
        for g in W:
            if tuple((-a)%n for a in g) in R: bad=True;break
            R|={ad(g,x) for x in R}
        if bad: continue
        Miss=[g for g in G if g not in R]
        for x in G:
          for y in G:
            for z in G:
              M=set()
              for (e,a,d) in pats:
                v=tuple((e*x[j]+a*y[j]+d*z[j])%n for j in range(r))
                if v not in R: M.add((e,a,d))
              res.add(frozenset(M))
    # keep maximal
    return [S for S in res if not any(S<o for o in res)]
A1=achievable(1,4); print("rank1 maximal M:",[sorted(S) for S in A1])
pickle.dump(A1,open('A1.pkl','wb'))
def ok(M): return all(any(T[i] in M[i] for i in range(3)) for T in reqs)
# what does block 2 need if blocks 0,1 are rank 1?
allS=[frozenset(c) for k in range(8) for c in itertools.combinations(pats,k)]
need=set()
for S0 in A1:
  for S1 in A1:
    for perm in itertools.permutations(range(3)):
      for S in allS:
        Ms=[None]*3; Ms[perm[0]]=S0; Ms[perm[1]]=S1; Ms[perm[2]]=S
        if ok(Ms): need.add(S)
mn=[S for S in need if not any(o<S for o in need)]
print("third block minimal needs:",[sorted(S) for S in mn])
