# Erdős #757: searching for self-similar gadgets below 5/9

Goal: a (4,5)-set family whose largest Sidon subset is below 5/9 of its size. That would beat the
reader's 5/9 family (erdosproblemaday.com 7bkzb8; we have checked it only up to K = 8, i.e. 47/83).

## The construction class

The 5/9 family is a *self-similar chain*. Take a (4,5)-set O with a = min O, b = max O and two
interior points p, q. Let φ be the affine map with φ(a) = p, φ(b) = q, and put
S_K = O ∪ φ(O) ∪ … ∪ φ^K(O). Neighbouring copies share exactly the pair (p, q). If S_K has no
3-term progressions across copies, its Sidon subsets are the sets whose trace on every copy is
Sidon. So the Sidon number grows by a fixed amount g per copy, and S_K has ratio → g/(|O| − 2).

**g is computable from O alone**: it is the maximum cycle mean of a 4×4 max-plus matrix
W[s][t] (s = which of a, b are chosen, t = which of p, q are chosen). A potential π with
W[s][t] ≤ g + π(t) − π(s) is a finite certificate that gives h(S_K) ≤ const + gK for **every** K
(`transfer_certificate.py`; for the 5/9 family: π = (0, 1, 1, 1), g = 5, h(S_K) ≤ 7 + 5K).
This bound needs no geometry: a Sidon subset of S_K has a Sidon trace on every copy, and extra
progressions across copies would only make it smaller (Auditor's remark, 2026-11-25). The geometric
half of an all-K proof (|S_K| = 11 + 9K and S_K stays a (4,5)-set) is not covered here.

Each copy adds t = |O| − 2 points. At most t of them can be middles of progressions, and the best
gadgets use all of them, so O is *rigid*: every interior point is the middle of exactly one
progression, and O is determined by its progression structure.

## All-K proof of the 5/9 family (`five_ninths_all_k.py`)

This is a self-contained, exact, computer-assisted proof that every S_K is a (4,5)-set with
|S_K| = 11 + 9K and h(S_K) ≤ 7 + 5K. That gives c* ≤ 5/9. The geometric half uses a "no mixing"
lemma: no additive relation uses points from copies two or more levels apart. It is proved by
interval arithmetic over nested intervals, refined level by level, and it closes at level 3
(110 → 8 → 0 open cases). The script runs in about 1 second. The proof outline is in its docstring. The same proof is now
checked in Lean: `Lab/Erdos757/FiveNinths.lean` (`sSup_le_five_ninths`).

## Search method

`ord.py`: SAT over ordered structures (labels = real order, so no relabelling symmetry). Variables
pick, for every interior j, the progression (i, j, k) with i < j < k. Clauses: linearity, chain
compatibility, and "W[s][t] ≤ g + π(t) − π(s)" with π encoded in order encoding. Each SAT model is
then solved exactly over the rationals (x_min = 0, x_max = 1, x_j = (x_i + x_k)/2). If the result is
not increasing (LP check) or has an extra additive coincidence, a minimal conflicting set of
progressions is extracted. It is added as a clause for every order-preserving relabelling (CEGAR).
`ord2.py` allows one interior point that is not a middle (a one-parameter family of realizations).

A potential certificate may need span up to 3·(den·t − num); `ord.py` uses span 4 unless told otherwise.
Cycle means are k/L with L ≤ 4, so for each size the target is the largest such value below 5t/9.

## Results (2026-11-25)

| \|O\| | t | target g (beats 5/9 iff possible) | result |
| --- | --- | --- | --- |
| 11 | 9 | 5 (= 5/9, sanity check) | many gadgets found in seconds, e.g. {0, 40, 59, 78, 80, 82, 85, 92, 102, 124, 156}, ports (82, 59) |
| 12 | 10 | 11/2 (11/20) | **none**: all 50 port choices UNSAT, complete for potentials (rerun by the Auditor with span 27, the full needed range), also with one spare point |
| 13 | 11 | 6 (6/11) | **none with bounded potentials** (span ≤ 4; complete needs ≤ 15): all 60 port choices UNSAT (re-run with exact rational row-space tests), also with one spare point |
| 14 | 12 | 13/2 (13/24) | **none with bounded potentials** (span ≤ 4; complete needs ≤ 33), every interior point a middle: all 72 port choices UNSAT. One-spare-point variant still running |
| 15 | 13 | 7 (7/13) | exact solver too slow (> 10 min per port choice); random search only |

Binary-tree gluing (two child pairs per copy) is worse: 0.587 for the reader's O.

Other designs tried (2026-11-25, `multiglue.py`, `results/multiglue.log`): gluing copies along 2 or 3
shared points with any affine contraction, applied to the reader's O and to the Ma–Tang 14-point set.
Best ratios: 5/9 (the known gluing) and 7/12. The ratio is an upper estimate: it is the within-copy transfer
value and ignores cross-copy relations and (4,5)-validity. Cross-copy progressions could only lower the true
ratio, so this is **not** a proof that these gluings cannot beat 5/9. Maps whose two shared sets overlap
(a point shared with both parent and child) were skipped. **16 points**: the exact solver (`ord.py 16 31 4`) did not
finish its first SAT call within 120 s for any of the 18 port choices tried (`results/o16_*.log`), so the
16-point case is out of reach for this solver.

Caveats: these are computer searches, not certified proofs. The SAT answers are not
proof-logged, and the order check uses a floating-point LP. They cover only this construction class:
2-point gluing, copies attached at min/max, and at most one non-middle point.
The n = 12 and n = 14 answers needed no geometry at all: the progression structure alone (linear,
ordered, every interior point a middle) already rules them out. The n = 13 answers used 61 geometric
conflicts, each checked with exact rank tests.
Logs are in `results/` (o = every interior point a middle, s = one spare point allowed).

## Files
- `transfer_certificate.py`: standalone exact checker of the all-K Sidon bound (5/9 family).
- `ord.py`, `ord2.py`: the exact gadget solver (needs `python-sat`, `ortools`).
- `gad.py`, `cegar.py`, `sa.py`, `harm.py`: realization checks, transfer-matrix code, random search.
