# Kostka numbers K(mu, alpha) for the shapes used in Lab/ClawFree/Shapes.lean, by the same backtracking.
from collections import Counter
def ssyt(w,k=4):
    pos=[(r,c) for r in range(len(w)) for c in range(w[r])]
    out=[];nodes=0
    def rec(T):
        nonlocal nodes; nodes+=1
        j=len(T)
        if j==len(pos): out.append(tuple(Counter(T).get(i,0) for i in range(k))); return
        for x in range(k):
            ok=True
            for i in range(j):
                if pos[i][0]==pos[j][0] and not T[i]<=x: ok=False
                if pos[i][1]==pos[j][1] and not T[i]<x: ok=False
            if ok: rec(T+[x])
    rec([]); return Counter(out),nodes
S=[(4,4,2,2),(4,3,3,2),(3,3,3,3),(5,3,2,2)]
for mu in S:
    C,n=ssyt(mu); print(mu,n,[C[a] for a in S])
