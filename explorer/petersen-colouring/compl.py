import pickle,time,itertools
from multi import MP,F,disjoint
from pcol import pcol_set,P,PE,STAR
f=F()
n,edges,dang,offs=disjoint(f,f)
d1,d2=dang[:5],dang[5:]
c=n; n+=1
edges+= [(d1[2],d2[0]),(d1[3],d2[1]),(d1[4],c),(d2[4],c)]
# Y dangling order = what hole's (r1,r2,b1,b2,e) attach to
Ydang=[d2[2],d2[3],d1[0],d1[1],c]
t=time.time()
S=pcol_set(n,edges+[(v,None) for v in Ydang])
print('|S|',len(S),time.time()-t)
CF=pickle.load(open('cols.pkl','rb'))['F']
print('|Col F|',len(CF),'intersection',len(S&CF))
pickle.dump(S,open('S1.pkl','wb'))
# all 5-tuples realizable by any multipole? count tuples with parity-like constraint: just count distinct
