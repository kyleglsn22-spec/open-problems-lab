# zero-sumfree sequences of length 9 over C_6^2 with p,q,r in Miss (=G \ Sigma0) and r-p-q in 2G
import itertools
G=[(i,j) for i in range(6) for j in range(6)]
idx={g:k for k,g in enumerate(G)}
add=lambda x,y: ((x[0]+y[0])%6,(x[1]+y[1])%6)
nz=[g for g in G if g!=(0,0)]
found=[]; count=0
def dfs(seq, start, reach):  # reach: set of Sigma0 incl 0 as bitmask int
    global count
    if len(seq)==9:
        count+=1
        M=[g for g in G if not (reach>>idx[g])&1]
        for p in M:
            for q in M:
                for r in M:
                    s=((r[0]-p[0]-q[0])%6,(r[1]-p[1]-q[1])%6)
                    if s[0]%2==0 and s[1]%2==0:
                        found.append((tuple(seq),p,q,r)); return
        return
    for k in range(start,len(nz)):
        g=nz[k]
        # new reach = reach | shift(reach,g); zero-sumfree iff -g not in reach
        if (reach>>idx[((-g[0])%6,(-g[1])%6)])&1: continue
        sh=0
        r=reach
        while r:
            b=r&-r; i=b.bit_length()-1; sh|=1<<idx[add(G[i],g)]; r^=b
        dfs(seq+[g],k,reach|sh)
        if found and len(found)>3: return
dfs([],0,1)
print("zero-sumfree length-9 sequences visited:",count,"found",len(found))
for f in found[:4]: print(f)
