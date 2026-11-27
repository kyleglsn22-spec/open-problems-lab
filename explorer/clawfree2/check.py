"""Independent cross-check for CF-2 (second minimal claw-free Schur counterexample, graph6 K?`CR@`bAbRB).

Decodes the graph6 code, checks claw-freeness, counts proper 4-colourings by class sizes, computes
the Kostka numbers by enumerating semistandard tableaux row by row, and inverts: [s_3333] X_G = -40.
Run: python3 explorer/clawfree2/check.py
"""
import itertools
from collections import Counter
g6='K?`CR@`bAbRB'
def dec(s):
    d=[ord(c)-63 for c in s]; n=d[0]; bits=[]
    for x in d[1:]:
        bits+= [(x>>(5-i))&1 for i in range(6)]
    A=[[0]*n for _ in range(n)]; k=0
    for j in range(1,n):
        for i in range(j):
            A[i][j]=A[j][i]=bits[k]; k+=1
    return n,A
n,A=dec(g6)
E=[(i,j) for i in range(n) for j in range(i+1,n) if A[i][j]]
# claw-free
cf=all(not(A[v][a] and A[v][b] and A[v][c]) or A[a][b] or A[a][c] or A[b][c] for v in range(n) for a,b,c in itertools.combinations([u for u in range(n) if u!=v],3))
print('clawfree',cf)
# colourings
cnt=Counter(); 
def go(v,col):
    if v==n: cnt[tuple(col.count(i) for i in range(4))]+=1; return
    for c in range(4):
        if all(not A[u][v] or col[u]!=c for u in range(v)):
            col.append(c); go(v+1,col); col.pop()
go(0,[])
tot=sum(cnt.values()); print('proper 4-colourings',tot)
dec_=sorted({c for c in cnt if list(c)==sorted(c,reverse=True)},reverse=True)
print({c:cnt[c] for c in dec_})
dec_=sorted({c for c in cnt if list(c)==sorted(c,reverse=True)},reverse=True)
X={c:cnt[c] for c in dec_}; print("contents", X)
def rows(r,below_prev):
    # weakly increasing rows of length r, entries in 0..3, strictly greater than prev row entries
    for t in itertools.combinations_with_replacement(range(4),r):
        if below_prev is None or all(t[j]>below_prev[j] for j in range(r)): yield t
def kostka(sh,al):
    cnt=0
    def go(i,prev,content):
        nonlocal cnt
        if i==len(sh):
            cnt+= tuple(content)==al; return
        for t in rows(sh[i],prev):
            c=content[:]
            for x in t: c[x]+=1
            if all(c[k]<=al[k] for k in range(4)): go(i+1,t,c)
    go(0,None,[0,0,0,0]); return cnt
S=[(5,3,2,2),(4,4,2,2),(4,3,3,2),(3,3,3,3)]
K={(m,a):kostka(m,a) for m in S for a in S}
for m in S: print(m,[K[(m,a)] for a in S])
assert set(X)==set(S) and len(E)==21 and cf
c={}
for a in S:
    c[a]=X[a]-sum(c[m]*K[(m,a)] for m in c)
print("Schur coefficients", c)
assert c[(3,3,3,3)]==-40
print("OK")
