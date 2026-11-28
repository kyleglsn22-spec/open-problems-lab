import re,ast,networkx as nx,glob
from multi import F,disjoint,MP
from pcol import colourable,pcol_set
f=F()
for line in open('/dev/stdin'):
    m=re.match(r"HIT k (\d+) E (\[.*\]) dang (\[.*\]) perm",line)
    k=int(m[1]);E=ast.literal_eval(m[2]);dang=ast.literal_eval(m[3])
    X=MP(k,E,dang)
    n,edges,d,offs=disjoint(X,f,f)
    D=[d[0:5],d[5:10],d[10:15]]
    for i in range(3):
        j=(i+1)%3; edges+=[(D[i][2],D[j][0]),(D[i][3],D[j][1])]
    c=n; edges+=[(D[i][4],c) for i in range(3)]; n+=1
    G=nx.MultiGraph(); G.add_edges_from(edges)
    simple=nx.Graph(edges)
    print('k',k,'n',n,'multi-edges',len(edges)-simple.number_of_edges(),'bridgeless',(len(edges)==nx.Graph(edges).number_of_edges() and nx.is_k_edge_connected(simple,2)),
          'Xcol',len(pcol_set(k,E+[(v,None) for v in dang])),'colourable',colourable(n,edges))
