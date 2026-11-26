# C44: can a degree-5 Boolean function depend on 47 variables?

**Question.** R_d is the most variables a Boolean function of degree d can depend on.
Chiarelli–Hatami–Saks (2018) built functions with R_d ≥ 3·2^(d−1) − 2 (so 46 at degree 5,
94 at degree 6) and this gives the lower bound C44 ≥ 3/2. Because their doubling step
R_(d+1) ≥ 2R_d + 2 works for any function, **one degree-5 function with 47 relevant variables
(or a degree-6 one with 95) would raise the lower bound for C44 for the first time since 2018.**
Known upper bounds: R_5 ≤ 50, R_6 ≤ 107 (Pinho, Nov 2026, unrefereed).

## What we searched: block compositions

Every known extremal function is built by plugging smaller extremal functions into a small
"pattern". We searched all such patterns of a given size.

A pattern is a Boolean function G on N variables, variable i carrying a weight w_i ∈ {1,…,d−1},
such that every monomial of G has total weight ≤ d. Replacing each weight-w variable by its own
copy of an extremal degree-w function (R_1..R_4 = 1, 4, 10, 22, all exact; R_5 ≥ 46 used at d = 6)
gives a Boolean function of degree ≤ d with V = Σ R_(w_i) relevant variables (if G depends on
every one of its variables). CHS is the pattern G(s,t,u,v) = ½(s+t)u + ½(s−t)v with weights
(1, 1, d−1, d−1). The pattern class includes every gadget of the form Σ_j s_j(x)·h_j(y_j), every
way of nesting them with at most N blocks, and products and selectors of extremal pieces.

For each weight vector with V ≥ 47 (d = 5) or V ≥ 95 (d = 6) we asked a SAT-style solver
(OR-tools CP-SAT) whether such a G exists.

## Results

| Degree | Target | Blocks N | Shapes | Ruled out | Undecided | Found |
| --- | --- | --- | --- | --- | --- | --- |
| 5 | ≥ 47 | ≤ 9 | 127 | **127** | 0 | 0 |
| 5 | ≥ 47 | 10–11 | 94 | 83 | 11 | 0 |
| 6 | ≥ 95 | ≤ 9 | 361 | **361** | 0 | 0 |
| 6 | ≥ 95 | 10 | 172 | 167 | 5 | 0 |

**No block composition with at most 9 blocks beats the 2018 construction, at degree 5 or 6.**
So an improvement of the lower bound, if one exists, needs a genuinely new degree-5 (or 6)
building block, not a rearrangement of the known pieces.

Controls (must be feasible, and are): CHS shapes (4,4,1,1), (4,3,3,1,1,1,1), (3,3,3,3,1^6) at
degree 5 (value 46); (5,5,1,1), (5,4,4,1^4), (4,4,4,4,1^6) at degree 6 (value 94); (3,3,1,1)
at degree 4 (22). Degree 3 and 4 runs reproduce the known exact values R_3 = 10, R_4 = 22 for
all shapes they decided (logs/w3.log, logs/w4.log).

## Trust

- The "ruled out" entries are solver verdicts (CP-SAT, no exported proof certificate).
- Two independent encodings agree: `wdeg.py` (full truth table of G, local derivative
  constraints) and `wdeg2.py` (exploits that heavy blocks never share a monomial, so
  G = A(z) + Σ_j u_j B_j(z); used for logs w5c, w5d, w6c, w6d). `wdeg2.py` re-decided all 89
  degree-5 shapes with ≤ 8 blocks that `wdeg.py` had ruled out: same verdict on every one
  (logs/wdeg2_recheck_d5.log).
- `crosscheck_mip.py` re-derives verdicts with a third encoding (all Fourier coefficients, MIP
  solver SCIP, no shared code): it independently rules out **all 35 degree-5 shapes with ≤ 6
  blocks** plus 16 larger ones, and disagrees with CP-SAT nowhere (logs/crosscheck_mip_d5.log).
  It times out on the rest.
- Any solution found would be checked by direct Fourier computation before being claimed.

## Files

- `wdeg.py`, `wdeg2.py`: the two CP-SAT searches. `resume.py`: rerun the shapes a log has not decided.
- `gadget.py`: first, narrower signed-partition search (subsumed).
- `controls.py`: positive controls. `crosscheck_mip.py`: SCIP cross-check.
- `logs/`: raw solver output. d = 5: w5a (wdeg, 300 s), w5b (wdeg, 60 s), w5c (wdeg2, 300 s),
  w5d (wdeg2, 1800 s; snapshot of a run still in progress when committed: its first 3 lines are
  the 3 extra shapes counted in the 10–11-block row). d = 6: w6c (≤ 9 blocks), w6d (10 blocks).

Reproduce one line, e.g. `echo "w=(4, 4, 1, 1, 1)" | python3 wdeg2.py 5 60`.
