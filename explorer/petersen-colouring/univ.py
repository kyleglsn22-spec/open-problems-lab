import itertools,pickle,networkx as nx
from pcol import P,PE,PEi
# perfect matchings of P
pms=[]
for M in itertools.combinations(range(15),5):
    vs=set()
    for i in M: vs|=set(PE[i])
    if len(vs)==10: pms.append(set(M))
print('pms',len(pms))
cnt=0;U=[]
for t in itertools.product(range(15),repeat=5):
    if all(sum(x in M for x in t)%2==1 for M in pms): cnt+=1
print('U size',cnt)
