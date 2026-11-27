"""Numerical cross-check for FW-1: compute down/up integers below LIMIT from the CGS representation
and list the 4-step gap sets D_4, U_4 (9 should be in U_4 only)."""
LIMIT = 200000
fib = [0, 1]
while fib[-1] < 10 * LIMIT:
    fib.append(fib[-1] + fib[-2])
kind = {}
for t in range(2, len(fib) - 1):
    ft, f1 = fib[t], fib[t - 1]
    if ft + f1 > LIMIT:
        break
    for a in range(1, ft + 1):
        if a * ft + a * f1 > LIMIT:
            break
        for b in range(a, ft + 1):
            n = a * ft + b * f1
            if n > LIMIT:
                break
            assert n not in kind, f"{n} represented twice"
            kind[n] = t % 2
assert all(n in kind for n in range(2, LIMIT + 1))
D = [n for n in range(2, LIMIT + 1) if kind[n] == 0]
U = [n for n in range(2, LIMIT + 1) if kind[n] == 1]
gap = lambda s, l: sorted({s[k + l] - s[k] for k in range(len(s) - l)})
print("D_4 =", gap(D, 4))
print("U_4 =", gap(U, 4))
print("D_3 == U_3 below limit:", gap(D, 3) == gap(U, 3))
