# Erdős #1186: fewer one-colour 4-term progressions mod a prime

**Question.** Colour 0, 1, ..., p−1 (p prime, arithmetic mod p) red and blue. How small can the share
of 4-term progressions a, a+d, a+2d, a+3d that are all one colour be? A random colouring gives 1/8.
Best published bound: 17/150 ≈ 0.11333 (Lu–Peng 2012). Best lower bound: 7/96 ≈ 0.0729. Best bound we know
of anywhere: ≈ 0.109645 (Marquardt, unrefereed GitHub project, Nov 2026, colourings by position only).

**Our result (claim 1186-2).** For every large prime p there is a colouring with share
479/4356 + o(1) ≈ 0.10996, i.e. 12.0% below random (Lu–Peng: 9.3%). A simpler one gives 27/242 ≈ 0.11157
(claim 1186-1). **Not a record**: Marquardt's 0.109645 is lower.

**Correction (2026-11-26, later).** We first thought using x mod b made these a new kind of colouring.
It does not: multiplying every number by the inverse of b mod p (which maps 4-term progressions to
4-term progressions) turns c(x) = G_r[x mod b][floor(Kx/p)] into an ordinary position-only colouring
with bK equal blocks, exactly the kind Marquardt optimises. `equiv_check.py` checks this pointwise on
real primes and recomputes 479/4356 exactly from the 132-block word. So our colourings are special
cases of his family, and "combining" the two adds nothing. Details and the later searches: `search2/`.

**The colourings.** c(x) = G_r[x mod b][floor(Kx/p)]: the colour depends on x's remainder mod b and on
which of K equal slices of 0..p−1 contains x, with one table per remainder r = p mod b.
- `cert_22_2.json` (b = 22, K = 2, value 27/242): one string A = 1011110001001000011101 works for all p:
  c(x) = A[x mod 22] if x < p/2, else A[(x + 5p) mod 22].
- `cert_44_3.json` (b = 44, K = 3, value 479/4356): 20 tables, one per residue class mod 44.

**Files.**
- `PROOF.md`: why the exact number is the limit for these colourings (elementary lattice-point count).
- `family.py`: exact cell areas (rational) and the limit density; brute-force counter for real primes.
- `check_certificate.py cert.json [--primes N]`: exact check over all residue classes; with `--primes`
  also counts real primes (`--primes 6000` takes ~15 s).
- `tabu_family.c`: the search (`python3 family.py K > patK.txt; ./tabu_family b K r iters restarts seed < patK.txt`).

Search history and dead ends: `ledger/erdos-1186.md`.
