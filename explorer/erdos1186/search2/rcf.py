import ctypes,os,numpy as np
lib=ctypes.CDLL(os.path.join(os.path.dirname(os.path.abspath(__file__)),'librcf.so'));lib.dens.restype=ctypes.c_double
def dens(bp,q):
    bp=np.ascontiguousarray(bp,float);q=np.ascontiguousarray(q,float)
    return lib.dens(len(q),bp.ctypes.data_as(ctypes.POINTER(ctypes.c_double)),q.ctypes.data_as(ctypes.POINTER(ctypes.c_double)))
