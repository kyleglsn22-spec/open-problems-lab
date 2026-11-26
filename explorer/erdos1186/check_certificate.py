"""Check a colouring certificate for m4(Z_p): exact limit density for every residue class.

usage: python3 check_certificate.py cert.json [--primes N]
  --primes N : also brute-force count m4(Z_p, c) for the first prime p > N in every residue
               class (slow, O(p^2) each) and print it next to the exact limit.
"""
import json, sys, math
from fractions import Fraction as Fr
import numpy as np
from family import exact_density, count_mono


def is_prime(n):
    return n > 1 and all(n % q for q in range(2, math.isqrt(n) + 1))


def main():
    cert = json.load(open(sys.argv[1]))
    b, K = cert["b"], cert["K"]
    N = int(sys.argv[sys.argv.index("--primes") + 1]) if "--primes" in sys.argv else None
    units = [r for r in range(b) if math.gcd(r, b) == 1]
    assert sorted(map(int, cert["tables"])) == units, "need one table per unit residue"
    worst = Fr(0)
    for r in units:
        G = np.array(list(map(int, cert["tables"][str(r)]))).reshape(b, K)
        v = exact_density(G, r)
        worst = max(worst, v)
        line = f"r = {r:3d}: limit density {v} = {float(v):.9f}"
        if N:
            p = next(q for q in range(N, 10 * N) if q % b == r and is_prime(q))
            x = np.arange(p)
            col = G[x % b, (K * x) // p]
            line += f" | p = {p}: m4 = {count_mono(col) / p**2:.9f}"
        print(line, flush=True)
    print(f"max over residues: {worst} = {float(worst):.9f}")
    print(f"Lu-Peng 2012 bound 17/150 = {17/150:.9f}; random colouring 1/8")
    if "claimed_max" in cert:
        assert worst == Fr(cert["claimed_max"]), "claimed value does not match"
        print("claimed value confirmed:", cert["claimed_max"])


if __name__ == "__main__":
    main()
