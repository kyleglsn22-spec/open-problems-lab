import sys, ast
from wdeg import weight_vectors, solve, RV
d, t, N, tl = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
done = set()
for f in sys.argv[5:]:
    for l in open(f):
        if l.startswith("w="): done.add(ast.literal_eval(l[2:l.index(")")+1]))
vecs = [v for v in sorted(weight_vectors(d, t, N), key=lambda v: (len(v), v)) if v not in done]
print(f"resume d={d}: {len(vecs)} weight vectors", flush=True)
for w in vecs:
    st, sol, tt = solve(list(w), d, tl)
    print(f"w={w} V={sum(RV[x] for x in w)}: {st} ({tt:.1f}s)", flush=True)
    if sol: print("  SOLUTION", ''.join(map(str, sol)), flush=True)
