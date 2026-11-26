# class-two group G = V1 x V2 x W, V1=V2=F_2^6, W=F_2^5
# (c,b,w)(c',b',w') = (c+c', b+b', w+w'+omega(b,c'))
import itertools
blocks=[[2,3,4,5,7,8,9,10,12],[6,11,15,17,19,21,23,24,26],[1,13,14,16,18,28,29,30,31]]
# need M_i = (a,b,c,d) realizing each label set; find them
def find(Ls):
    for a,b,c,d in itertools.product(range(1,32),repeat=4):
        L=[a,b,a^b,c,d,c^d,a^c,b^d,a^b^c^d]
        if sorted(L)==sorted(Ls): return (a,b,c,d)
Ms=[find(L) for L in blocks]; print(Ms)
# omega on basis: y index 2i+u, z index 2j+v
om=[[0]*6 for _ in range(6)]
for i,(a,b,c,d) in enumerate(Ms):
    om[2*i][2*i]=a; om[2*i][2*i+1]=b; om[2*i+1][2*i]=c; om[2*i+1][2*i+1]=d
def omega(y,z):
    v=0
    for i in range(6):
        if y>>i&1:
            for j in range(6):
                if z>>j&1: v^=om[i][j]
    return v
OM=[[omega(y,z) for z in range(64)] for y in range(64)]
def enc(c,b,w): return c|(b<<6)|(w<<12)
def mul(g,h):
    c,b,w=g&63,(g>>6)&63,g>>12
    c2,b2,w2=h&63,(h>>6)&63,h>>12
    return enc(c^c2,b^b2,w^w2^OM[b][c2])
def prod(*sets):
    cur={0}
    for s in sets: cur={mul(x,y) for x in cur for y in s}
    return cur
A=[enc(c,0,0) for c in range(64)]
D=[enc(0,b,0) for b in range(64)]
Bv=[0]+[ (u<<(2*i)) for i in range(3) for u in (1,2,3)]
B=[enc(0,y,0) for y in Bv]
C=[enc(z,0,0) for z in Bv]
S=prod(A,B,C,D); print('S',len(S))
N1=len(prod(B,C,D)); N4=len(prod(A,B,C))
N2=max(len(prod(A,[b],C,D)) for b in B); N3=max(len(prod(A,B,[c],D)) for c in C)
print(N1,N2,N3,N4, len(S)**3, N1*N2*N3*N4, len(S)**3>N1*N2*N3*N4)
# group axioms sanity: associativity on random triples
import random
for _ in range(20000):
    x,y,z=[random.randrange(1<<17) for _ in range(3)]
    assert mul(mul(x,y),z)==mul(x,mul(y,z))
print('assoc ok')
