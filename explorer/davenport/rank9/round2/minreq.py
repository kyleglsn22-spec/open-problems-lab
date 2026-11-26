import itertools
exec(open('req.py').read().split('for r in sorted')[0])
pats=[p for p in itertools.product((0,1),repeat=3) if p!=(0,0,0)]
subsets=[frozenset(c) for k in range(8) for c in itertools.combinations(pats,k)]
def ok(M):
    return all(any(T[i] in M[i] for i in range(3)) for T in reqs)
# minimal single M (same for all blocks)
good=[S for S in subsets if ok((S,S,S))]
minimal=[S for S in good if not any(o<S for o in good)]
print("uniform minimal:",[sorted(S) for S in minimal])
# minimal by total size with different M per block
best=None
sols=[]
for A in subsets:
  for B in subsets:
    if len(A)+len(B)>8: continue
    for C in subsets:
      if len(A)+len(B)+len(C)>8: continue
      if ok((A,B,C)): sols.append((len(A)+len(B)+len(C),sorted(A),sorted(B),sorted(C)))
sols.sort(); print(len(sols)); 
for s_ in sols[:20]: print(s_)
