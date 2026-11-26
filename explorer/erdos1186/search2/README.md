# Erdős #1186: trying to beat Marquardt's 0.109645 (negative result, 2026-11-26)

Goal: beat the best known bound m4(Z_p) ≤ 0.109645 + o(1) of Max Marquardt
([github.com/incrediblecrab/erdos-problems](https://github.com/incrediblecrab/erdos-problems), folder `p1186`,
2 Nov 2026, unrefereed). His colourings are *circle colourings*: c(x) = S(x/p) for a set S of arcs of the
circle [0,1) with freely placed endpoints; his best has 26 arcs, continuum value 0.1096440255 and certified
grid value 1478233/13482006 ≈ 0.1096448852. All credit for that bound and for the circle-colouring search
is his. **We did not beat it.** This folder records what we tried, so nobody repeats it.

## 1. Our mod-b colourings are a special case of his (so "combining" is empty)

Our claims 1186-1/1186-2 use c(x) = G_r[x mod b][floor(Kx/p)]. Let λ = b⁻¹ mod p. Multiplying by λ is a
bijection of Z_p that maps 4-term progressions to 4-term progressions, and for 0 ≤ x < p

    λx mod p = (x + p·t(x)) / b,   t(x) = (−x·r⁻¹) mod b,  r = p mod b,

so position λx/p ∈ [t/b, (t+1)/b) records the residue class and x/p together. Hence our colouring is the
circle colouring with bK equal blocks W[tK + j] = G_r[s][j], s = (−t·r) mod b. `../equiv_check.py` checks
this pointwise on the primes 100003 and 100019 and recomputes 479/4356 exactly from the 132-block word for r = 1 (the other classes follow from the same bijection).
More generally, per-residue circle colourings S_{x mod b}(x/p) are circle colourings, so the "residue +
free breakpoints" combination we had queued is exactly Marquardt's family.

## 2. Larger families tested (all reduce to, or do not beat, his optimum)

All numbers are floating-point search values unless marked exact. Evaluators were checked against exact
values: `rc.c` reproduces his 2998-block word (0.10964488519) and our 479/4356; `t2q.c`/`rcf.c` reproduce
17/150 and his words.

| Idea | Why it is a genuinely different family | Result |
| --- | --- | --- |
| Random colourings with position-dependent odds q(x/p) (probabilistic method: some colouring is at most the average) | not a circle colouring for fractional q | Expected share is the multilinear extension of the circle functional (`frac.py`, `rcf.c`). Free arcs with free values in [0,1], started at his optimum with extra thin boundary arcs: L-BFGS returns to his ±1 optimum 0.1096440255. On grids (m = 44, 496) fractional values help only as a stand-in for moving a breakpoint inside a block. |
| Second coordinate x²/p mod 1, c(x) = F(x/p, x²/p) | uses the quadratic relation y0 − 3y1 + 3y2 − y3 = 0 of the four squares | Exact grid formula in `t2q.c`. We derived (Fourier expansion, not written up): share = fractional-odds share + (1/8)·(4-wise term of the w-dependent part). Tabu at m = 44 with 4, 5, 7 quadratic slices: 0.11106, 0.11106, 0.11105 vs the fractional relaxation 0.11105 at the same grid. No gain. Higher powers x³, ... should give independent terms, i.e. the fractional family (same derivation, not written up). |
| Two linear coordinates, F(x/p, λx/p) with λ ≈ √p (2-D torus colourings) | 2-D sets | Contained in the closure of circle colourings anyway (u ↦ F(u, Nu) with N → ∞). Continuum test: 2 and 3 strips in v, each with its own 26 free breakpoints, randomly perturbed from his optimum: L-BFGS returns to his optimum (strips identical to 1e-9). |
| Wide multistart over antipodal circle colourings with 18 to 62 arcs (`ms.py`, `polish.py`) | his search stopped at 30 arcs | 138 random starts (18 to 62 arcs, 6 hops each) plus 60-hop polishes of the two best and a non-symmetric polish of the best: best 0.10964429 (30 arcs), 9 starts below 0.10965, none below his 0.10964403. Raw results: `multistart_results.json`. |

## 3. What this means

Numerically (L-BFGS from perturbed starts, not a proof), his 26-arc optimum is a local minimum against every deformation we could think of that is not itself a
circle colouring, and random restarts with many more arcs land in basins at or slightly above it. Our
evidence suggests circle colourings near 0.10964 may be close to the limit of "linear" constructions; a
record probably needs a genuinely different idea (for example a quadratic structure that correlates with
the wrap-around, or a proof-side lower-bound improvement instead).

## Files
- `rc.c`, `rc.py`: float evaluator for residue + circle colourings (clipping the (u, t) square).
- `rcf.c`, `rcf.py`, `frac.py`: fractional (random-odds) circle colourings; `frac.py` is the grid version with gradient.
- `t2q.c`: exact grid evaluator and tabu search for c(x) = F[floor(Mu·x/p)][floor(Mw·frac(x²/p))].
- `rc4.c`, `t2c.py`, `t2opt.py`: 2-D torus colourings with v-strips (continuum in u), started from `marquardt_continuum.json`.
- `fopt.py`: free arcs with free odds in [0,1] (needs Marquardt's `results/zp_k4_c.json` copied here).
- `mslib.py`, `ms.py`, `polish.py`: multistart over antipodal arc colourings, then basin hopping.
- Build: `gcc -O3 -shared -fPIC -o librc.so rc.c` (same for `rcf.c`), `gcc -O3 -o t2q t2q.c`.
