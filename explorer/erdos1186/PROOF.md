# Why the computed numbers are upper bounds for m4(Z_p)

**Notation (Lu–Peng 2012).** For a 2-colouring c of Z_p, m4(Z_p, c) is the fraction of the p^2 pairs
(a, d) in Z_p^2 for which c(a) = c(a+d) = c(a+2d) = c(a+3d), and m4(Z_p) = min_c m4(Z_p, c).
Pairs with d = 0 are p of the p^2, so they do not affect limits.

**Colourings.** Fix b, K >= 1 and, for each residue r coprime to b, a 0/1 table G_r of size b x K.
For a prime p with p = r (mod b), colour x in {0, ..., p-1} by

    c_p(x) = G_r[x mod b][floor(K x / p)].

**Theorem.** m4(Z_p, c_p) = D(G_r, r) + O_{b,K}(1/p), where

    D(G, r) = sum over cells C of the arrangement below of area(C) * N_C(G, r) / b^2,

and N_C(G, r) is the number of (a0, d0) in Z_b^2 such that the four colours
G[(a0 + i d0 - r k_i) mod b][j_i], i = 0..3, are equal, with (k_i, j_i) the labels of C.
Consequently m4(Z_p) <= max_r D(G_r, r) + o(1) as p -> infinity over primes.

**Arrangement.** In the unit square (u, t) in [0,1)^2 draw the lines u + i t = m / K for i = 0..3 and all
integers m. On each open cell the integers k_i = floor(u + i t) and j_i = floor(K frac(u + i t)) are constant;
these are the labels of the cell.

**Proof.** Take (a, d) with 0 <= a, d < p and put (u, t) = (a/p, d/p). The i-th term of the progression is
the residue y_i = a + i d - p k_i in [0, p) with k_i = floor((a + i d)/p) = floor(u + i t), and
floor(K y_i / p) = floor(K frac(u + i t)) = j_i. Because p = r (mod b),
y_i = a + i d - r k_i (mod b), so c_p(y_i) = G_r[(a0 + i d0 - r k_i) mod b][j_i] with a0 = a mod b,
d0 = d mod b. Hence, for (u, t) inside a cell C, whether (a, d) is monochromatic depends only on C and on
(a0, d0). Each cell is a convex polygon inside the unit square, so the number of points (a, d) of the
shifted lattice (a0, d0) + b Z^2 lying in p C is area(C) p^2 / b^2 + O(p) (the error is bounded by a
constant times the perimeter of pC divided by b, plus 1). Points on the finitely many lines number
O(K p). Summing over the finitely many cells and the b^2 classes (a0, d0) and dividing by p^2 gives
the theorem. QED.

**Exact areas.** Two arrangement lines (or a line and a side of the square) cross only at t in (1/(6K))Z,
since the slopes i differ by 1, 2 or 3. On each strip m/(6K) < t < (m+1)/(6K) the cut points in u are
linear in t and keep their order, so every cell's length at height t is linear there and the midpoint
rule is exact. `family.py: patterns(K)` does exactly this with rational arithmetic and asserts that the
areas sum to 1.

**Sanity checks done.** (1) The table for Lu–Peng's block colouring B20 (b = 20, K = 1) gives exactly
their 17/150 for every residue. (2) For every certificate, `check_certificate.py --primes N` brute-forces
m4(Z_p, c_p) for an actual prime in each residue class; the values approach D at rate ~1/p (from above or below depending on the class).
