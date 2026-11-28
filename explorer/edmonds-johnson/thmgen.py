"""THM certificates: 2*S^-1 (nonsingular) or an integral kernel vector (singular) for every
square submatrix with increasing row and column indices. Used by thmgen2.py."""
import itertools, sympy
def certs(A):
    m=len(A); n=len(A[0]); E=[]
    for k in range(1,6):
      for R in itertools.combinations(range(m),k):
        for C in itertools.combinations(range(n),k):
          S=sympy.Matrix([[A[r][c] for c in C] for r in R])
          if S.det()!=0:
            N=2*S.inv(); assert all(x.is_integer for x in N), ('not THM',R,C)
            E.append((R,C,'N',[[int(x) for x in N.row(i)] for i in range(k)]))
          else:
            v=S.nullspace()[0]; l=sympy.ilcm(1,1,*[x.q for x in v]); v=[int(x*l) for x in v]
            E.append((R,C,'v',v))
    return E
def fl(l): return "["+", ".join(str(x) for x in l)+"]"
A6=[[0,0,1,-1,0,0],[0,1,1,0,2,0],[0,1,0,1,0,2],[1,0,1,0,2,0],[1,0,0,1,0,2]]
A6p=[[0,0,1,1,0,0],[0,1,1,0,2,0],[0,1,0,1,0,2],[1,0,1,0,2,0],[1,0,0,1,0,2]]
A7=[[0,0,1,-1,2,-2,2],[0,1,1,0,2,0,0],[0,1,0,1,0,2,0],[1,0,1,0,2,0,0],[1,0,0,1,0,2,0]]
