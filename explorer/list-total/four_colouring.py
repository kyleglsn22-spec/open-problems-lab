def term(i,j): return 5*i+2+(j if j<i else j-1)
T={(1,2):2,(1,3):3,(1,4):1,(2,1):1,(2,3):3,(2,4):2,(3,1):1,(3,2):2,(3,4):3,(4,1):2,(4,2):3,(4,3):1}
colV=[0]*20; colE=[[0]*20 for _ in range(20)]
E=[]
for i in range(4):
    colV[5*i]=4; colV[5*i+1]=4
    for j in range(4):
        if j==i: continue
        v=term(i,j); cv=T[(i+1,j+1)]; colV[v]=cv
        nxt=cv%3+1; prv=(cv-2)%3+1
        for (x,y,cc) in [(5*i,v,nxt),(5*i+1,v,prv)]:
            colE[x][y]=colE[y][x]=cc; E.append((x,y))
        if i<j:
            w=term(j,i); colE[v][w]=colE[w][v]=4; E.append((v,w))
adj=[[0]*20 for _ in range(20)]
for x,y in E: adj[x][y]=adj[y][x]=1
ok=True
for u in range(20):
    for v in range(20):
        if adj[u][v]:
            ok&=colV[u]!=colV[v]; ok&=colV[u]!=colE[u][v]
            for w in range(20):
                if adj[u][w] and w!=v: ok&=colE[u][v]!=colE[u][w]
print(ok)
print("colV", [c-1 for c in colV])
print("colE", [[max(c-1,0) for c in r] for r in colE])
