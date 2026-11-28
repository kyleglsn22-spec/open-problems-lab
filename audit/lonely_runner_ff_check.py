"""Independent check of Hu (arXiv:2608.18818, Theorem 1.2 / Proposition 3.1): for the thirteen
polynomials F* over F_2 and every power series alpha = sum_{n>=1} a_n T^{-n}, some f in F* has
||alpha f|| <= 2^-4, i.e. the coefficients of T^-1, T^-2, T^-3 in alpha*f vanish. Only a_1..a_7
matter (deg f <= 4). Computes alpha*f by explicit polynomial-times-Laurent multiplication
(truncated), independently of the kernel formulation, and also checks the coefficient table used
in Lab/LonelyRunner/FunctionField.lean."""
import itertools, re
F = ["1", "T^2+T", "T^2+T+1", "T^3", "T^3+T^2+1", "T^3+T+1", "T^3+T^2+T+1", "T^4+T^2", "T^4+T",
     "T^4+T^3+1", "T^4+T^2+1", "T^4+T+1", "T^4+T^3+T^2+T+1"]
def exps(s):
    return {0 if t == "1" else 1 if t == "T" else int(t[2:]) for t in s.split("+")}
polys = [exps(s) for s in F]
assert len(set(map(frozenset, polys))) == 13
worst = 0
for a in itertools.product([0, 1], repeat=7):          # a[n-1] = coefficient of T^-n
    best = None
    for P in polys:
        # coefficient of T^e in alpha*f, for e = -1, -2, ...: sum over d in P of a_{d - e}
        def c(e):
            return sum(a[d - e - 1] for d in P if 1 <= d - e <= 7) % 2
        m = next((m for m in range(1, 4) if c(-m)), None)  # nonzero coefficient among T^-1..T^-3?
        norm = 2.0 ** -m if m is not None else 2 ** -4  # otherwise ||alpha f|| <= 2^-4
        best = norm if best is None else min(best, norm)
    worst = max(worst, best)
print("max over alpha of min_f ||alpha f||  <=", worst)
assert worst <= 2 ** -4
src = open("Lab/LonelyRunner/FunctionField.lean").read()
rows = re.findall(r"!\[(\d), (\d), (\d), (\d), (\d)\]", src.split("def tbl")[1].split("open Classical")[0])
assert [{j for j, b in enumerate(map(int, r)) if b} for r in rows] == polys
print("Lean table matches; 13 < 15. OK")
