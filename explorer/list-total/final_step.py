import itertools
full={1,2,3,4,5}
Lc={(0,1):full-{3},(0,2):full-{5},(0,3):full-{2},(1,2):full-{4},(1,3):full-{5},(2,3):full-{1}}
bad=0
for s in itertools.product(range(6),repeat=4):
    if any(s[i]==i+1 or s[i]==0 for i in range(4)): continue
    if all(any(e in (i+1,s[i]) and e in (j+1,s[j]) for e in Lc[(i,j)]) for (i,j) in Lc): bad+=1;print(s)
print("satisfiable s:",bad)
