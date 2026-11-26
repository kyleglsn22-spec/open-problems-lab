# C37 explorer: degree 5, sensitivity 14

Target: is there `q : {0,1}^14 → {0,1}` with `deg q ≤ 5`, `q(0) = 0` and `q(e_i) = 1` for every `i`?
A yes gives `C37 ≥ log_5 14 ≈ 1.6397` by composition powers (beating `log_3 6 ≈ 1.6309`); a no extends
the degree-4 result. Ledger: `../../ledger/c37-degree-sensitivity.md`.

Everything here is exploratory search code plus one finished certificate. Nothing in this folder is
Lean-checked, and no claim here has been audited yet.

## The one idea used everywhere

Write `q = Σ_S c_S x^S` (multilinear, 0/1 inputs). The `c_S` are integers (Möbius inversion of 0/1
values), `c_∅ = 0`, every `c_{i} = 1`, and `c_S = 0` for `|S| > d`. Group the coordinates into blocks
(a Young subgroup `S_{a_1} × … × S_{a_m}`). For each pattern `l = (l_1..l_m)` let `C_l` be the sum of
`c_S` over sets with `l_t` elements in block `t`: an **integer**. The number of ones of `q` among inputs
with `w_t` ones in block `t` is

    N(w) = Σ_l C_l · Π_t binom(a_t − l_t, w_t − l_t),   and   0 ≤ N(w) ≤ Π_t binom(a_t, w_t).

Why these are integers and why `N(w)` is affine in them: `c_S = Σ_{T⊆S} (−1)^{|S∖T|} q(T)` is an
integer combination of 0/1 values, so each `C_l` is an integer. And `N(w) = Σ_{x in class w} q(x) =
Σ_x Σ_{S⊆x} c_S = Σ_S c_S · #{x in class w : S ⊆ x}`. The count depends only on the pattern of `S`,
and it equals the product of binomials above, so `N(w)` is an affine function of the `C_l`.

Every partition of the coordinates gives a small integer program that must be feasible if `q` exists.
One block is the classical symmetrisation (Nisan–Szegedy) plus integrality; it reproduces exactly the
247 starting profiles of Stepanovs (2012, Table 4.1) for `n = 14` and the 8 profiles for `n = 15`.

## Results so far (2026-11-25)

| What | Result | Files |
| --- | --- | --- |
| Degree 4, n = 10 (Koshta 2026's theorem) | **Short exact proof.** With blocks (8, 2) the LP relaxation already forces `C_(1,2) = Σ_k c_{9,10,k} = 14/3`, not an integer. 17 rational multipliers; two checkers agree. | `results/cert_n10_d4_split8_2.json`, `make_cert.py`, `check_indep.py` |
| Degree 4, n = 10, other block splits | (8,2), (5,5) and most 3–4 block splits infeasible; positive controls n = 9 (NAE∘NAE) and n = 6, d = 3 (Kushilevitz) feasible for every partition | `results/young_n10_d4.txt` |
| Degree 5, n = 14, block splits | Every partition into ≤ 3 blocks, and every 4-block partition tried, is **feasible**: block symmetry alone does not decide it | `results/young_n14_d5.txt` |
| Degree 5, cross-coordinate counting, level 1 (Stepanovs §6.2: per-coordinate split types must add up to the global profile) | n = 15: 8 → 2 profiles (matches Stepanovs). n = 14: 247 → 202 | `lvl1.py`, `results/profiles_d5.json` |
| Same, level 2 (all pairs, CP-SAT with lex symmetry breaking) | n = 15: 1 profile left, `C = (0,15,−105,280,−315,126)`; level 3 not finished in 10 min. Stepanovs reports level 4 kills n = 15; **not yet reproduced by us** | `hier.py`, `hier2.py` |
| Symmetric ansatz, n = 14: `q` invariant under a group G | **No such q** for G = PGL(2,13), PSL(2,13), Heawood-graph group PGL(2,7), PSL(3,2) on Fano points+lines, S7×C2 and AGL(1,7)×C2 (diagonal on 7+7), AGL(1,13) fixing a point, F21×C2, D14, AGL(1,7) diagonal. Smaller groups still running | `symsearch.py`, `groups14.py` |

Controls for the symmetric search: it finds Kushilevitz's function (n = 6, G = PSL(2,5)) and NAE∘NAE
(n = 9, G = S3 wr S3), and correctly reports n = 10, d = 4 infeasible under C10.

## Reproduce

Python 3.11+, `pip install ortools scipy numpy highspy`.

    python3 -I check_indep.py results/cert_n10_d4_split8_2.json   # standard library only, < 1 s
    python3 make_cert.py                                          # regenerates the certificate (HiGHS)
    python3 young.py 4 8 2      # degree 4, blocks (8,2): INFEASIBLE
    python3 young.py 5 7 7      # degree 5, blocks (7,7): feasible
    python3 lvl1.py 14 5        # level-1 cross-coordinate counting, ~7 s
    python3 hier2.py 15 5 2 60  # level 2, per profile
    python3 groups14.py 'PGL(2,13)' 'D14'

`check_indep.py` rebuilds each class constraint by brute force over the cube (no binomial formulas),
checks that the rational combination cancels every free variable except the target, and checks that
the forced interval contains no integer. Changing any multiplier makes it fail.

## Status of the claims

- The degree-4 certificate re-proves a known (unrefereed) result. It is **not the first short proof**.
  Pinho (hexagonmath 2610.00694, Oct 2026) states that his rational Fourier-lattice packet also
  reproves B4 ≤ 9. His packet uses one rational functional on the univariate symmetrisation, plus
  Parseval and the fact that the Fourier coefficients lie in 2^{-(d-1)}Z. Ours uses an LP over
  two-block orbit sums plus integrality of a single orbit sum. The two are different routes to a
  certificate of similar size. Wellens 2022's LP (no integrality) leaves this case open. Needs an Auditor's independent checker before the ledger marks it checked.
- The symmetric-ansatz exclusions are CP-SAT verdicts without exported certificates. Treat them as
  search results, not proofs, until certificates are exported.
- Who: Kyle (lead) with Claude (Anthropic, Claude Opus 5.5) writing all code and running all searches.
