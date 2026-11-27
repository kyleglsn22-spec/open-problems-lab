import sys, itertools; sys.path.insert(0, "explorer/block-equitable")
from ratio_search import *
# template: central clique of size m; special vertices 0..t-1 of Q, vertex i gets s blocks of size k;
# vertex t ("c") gets p pendant vertices.
res = []
for m in range(3, 9):
  for t in range(2, min(m-1, 4)+1):
    for s in range(1, 4):
      for k in range(2, 8):
        for p in range(0, 4):
          blocks = [list(range(m))]; n = m
          for i in range(t):
            for _ in range(s):
              blocks.append([i] + list(range(n, n+k-1))); n += k-1
          for _ in range(p):
            blocks.append([t, n]); n += 1
          if n > 45: continue
          adj = adjacency(n, blocks)
          L, om, am = L_of(n, adj, blocks)
          chi = chi_eq(n, adj, L)
          if chi / L > 1.25 or chi - L >= 2:
            print(f"m={m} t={t} s={s} k={k} p={p}: n={n} L={L} omega={om} amin={am} chi={chi} ratio={chi/L:.3f}", flush=True)
