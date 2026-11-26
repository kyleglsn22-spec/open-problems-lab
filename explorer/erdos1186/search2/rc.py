import ctypes, numpy as np, os
lib=ctypes.CDLL(os.path.join(os.path.dirname(os.path.abspath(__file__)),'librc.so'))
lib.density.restype=ctypes.c_double
def word_arcs(word):
    """word (str/list of 0/1) of length M -> (breakpoints list, colours list) merging equal runs"""
    M=len(word); bp=[0.0]; col=[]
    for i,ch in enumerate(word):
        c=int(ch)
        if not col or col[-1]!=c:
            if col: bp.append(i/M)
            col.append(c)
    bp.append(1.0); return bp,col
def density(r, S):
    """S: list over residues s of (breakpoints, colours)"""
    b=len(S); ns=[len(c) for _,c in S]; a=[]; off=[]; col=[]
    for bp,c in S:
        off.append(len(a)); a+=list(bp); col+=list(c)
    I=ctypes.c_int*b
    return lib.density(b,r,I(*ns),(ctypes.c_double*len(a))(*a),I(*off),(ctypes.c_int*len(col))(*col))
