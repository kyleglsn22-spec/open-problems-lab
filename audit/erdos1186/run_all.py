import json, subprocess, math, sys
from fractions import Fraction as F
def isprime(n): return n > 1 and all(n % q for q in range(2, math.isqrt(n)+1))
N = int(sys.argv[1])
for fn, lim in (("cert_22_2.json", F(27,242)), ("cert_44_3.json", F(479,4356))):
    c = json.load(open(fn)); b, K = c["b"], c["K"]; worst = 0
    for r, T in sorted(c["tables"].items(), key=lambda x: int(x[0])):
        r = int(r); p = N
        while not (p % b == r and isprime(p)): p += 1
        cnt, v = subprocess.run(["./bf", str(p), str(b), str(K), T], capture_output=True, text=True).stdout.split()
        e = float(v) - float(lim); worst = max(worst, abs(p*e))
        print(f"{fn} r={r:2d} p={p}: m4={float(v):.10f} err={e:+.2e} p*err={p*e:+.3f}", flush=True)
    print(f"{fn}: max |p*err| = {worst:.3f}")
