import pickle, time
from multi import F, W
from pcol import pcol_set
t=time.time()
cw=pcol_set(*W().as_edges()); print('W',len(cw),time.time()-t)
cf=pcol_set(*F().as_edges()); print('F',len(cf),time.time()-t)
pickle.dump({'W':cw,'F':cf},open('cols.pkl','wb'))
