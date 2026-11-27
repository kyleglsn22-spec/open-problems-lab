# Data for Lab/BlockEquitable/Counterexample.lean: G_{2,7} of arXiv 2608.14517 (d=2, k=7, m=7, 32 vertices).
# Q = 0..6 (v=0, w=1, c=2), pendant u = 7, private blocks B1 = 8..13, B2 = 14..19 (at v), B3 = 20..25, B4 = 26..31 (at w).
import itertools
n=32
def blk(a): return 0 if a<7 else 5 if a==7 else (a-8)//6+1
def anchor(i): return 0 if i<=2 else 1 if i<=4 else 2
def adj(a,b):
    if a==b: return False
    if blk(a)==blk(b): return True
    for x,y in ((a,b),(b,a)):
        if blk(x)!=0 and y==anchor(blk(x)): return True
    return False
# paper's colouring with colours 1..9 (stored as 0..8)
col={0:1,1:2,2:3,3:4,4:5,5:6,6:7,7:1}
sets={1:sorted(set(range(1,10))-{1,7,3}),2:sorted(set(range(1,10))-{1,7,4}),3:sorted(set(range(1,10))-{2,5,6}),4:sorted(set(range(1,10))-{2,8,9})}
for i in range(1,5):
    for j,a in enumerate(range(8+6*(i-1),14+6*(i-1))): col[a]=sets[i][j]
c=[col[a]-1 for a in range(n)]
assert all(not adj(a,b) or c[a]!=c[b] for a in range(n) for b in range(n))
sizes=[c.count(i) for i in range(9)]; print('class sizes',sizes); assert set(sizes)<={3,4}
# witness independent sets of size 4 containing each vertex
def indep(s): return all(not adj(a,b) for a in s for b in s)
wit=[]
for x in range(n):
    for s in itertools.combinations([y for y in range(n) if y!=x and not adj(x,y)],3):
        if indep(s): wit.append(sorted((x,)+s)); break
    else: raise SystemExit('no witness for %d'%x)
print('c9 :=', '!['+', '.join(map(str,c))+']')
print('wit :=', '['+', '.join('['+', '.join(map(str,w))+']' for w in wit)+']')
# brute-force checks on alpha(G,x): exact max independent set through each vertex
import functools
def alpha_at(x, banned=()):
    best=0
    cand=[y for y in range(n) if y!=x and not adj(x,y) and y not in banned]
    def go(i,cur):
        nonlocal best
        best=max(best,len(cur))
        for j in range(i,len(cand)):
            if all(not adj(cand[j],z) for z in cur): go(j+1,cur+[cand[j]])
    go(0,[]); return best+1
al=[alpha_at(x) for x in range(n)]; print('alpha(G,x):',al, 'min',min(al))
print('alpha(G-u,v), alpha(G-u,w):',alpha_at(0,(7,)),alpha_at(1,(7,)))
# clique number
print('max |N(a)&N(b)| over edges:',max(sum(adj(a,z) and adj(b,z) for z in range(n)) for a in range(n) for b in range(n) if adj(a,b)))
