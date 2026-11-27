---
problem: Gap-one conjecture for the equitable chromatic number of block graphs (Dybizbański–Furmańczyk–Mkrtchyan 2024)
source: https://arxiv.org/abs/2608.14517 (Lauri, disproof, Aug 2026)
lean_statement: Lab/BlockEquitable/Counterexample.lean (all definitions stated by us; clique number is Mathlib's `SimpleGraph.cliqueNum`)
status: solved (formalized)
---

# Equitable colouring of block graphs: the gap-one conjecture

## Statement
An equitable `q`-colouring of a graph on `n` vertices is a proper colouring in which every colour class has
`⌊n/q⌋` or `⌈n/q⌉` vertices; `χ_=(G)` is the least such `q`. With `α(G,v)` the largest independent set through
`v`, `α_min(G) = min_v α(G,v)` and `L(G) = max {ω(G), ⌈(n+1)/(α_min(G)+1)⌉}`, every graph has `χ_=(G) ≥ L(G)`.
Dybizbański, Furmańczyk and Mkrtchyan (Discrete Appl. Math. 354 (2024) 15–28) conjectured that every block graph
(every block is a clique) has `χ_=(G) ≤ L(G) + 1`. They proved it for several subclasses and checked all block
graphs on at most 19 vertices by computer.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| False: for `d ≥ 2`, `k ≥ 4d − 1`, a connected block graph `G_{d,k}` with `L = k` and `χ_= = k + d`; so `χ_= − L` is unbounded | Lauri, arXiv 2608.14517 | Yes: `d = 2`, `k = 7` (BEQ-1); the whole family (BEQ-2) |
| True for forests, well-covered block graphs, connected block graphs with `α_min ≤ 2`, and when every cut vertex is in exactly two blocks; true up to 19 vertices | Dybizbański–Furmańczyk–Mkrtchyan 2024; Chang 2009 (forests) | No |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| BEQ-1 | Lean: `G_{2,7}` (32 vertices: a `K_7` `Q ∋ v, w, c`, a pendant `u` at `c`, two `K_7` blocks hanging at `v` and two at `w`) is a connected block graph with `ω = 7`, `α_min = 4`, `L = 7` and `χ_= = 9`; hence `¬ GapOneConjecture` | Kyle + Claude, 2026-11-27 | audited (internal audit PASS, PR 19 review) | `not_gapOneConjecture`, `exists_counterexample` in `Lab/BlockEquitable/Counterexample.lean`; data and brute-force cross-check `explorer/block-equitable/gen.py` |
| BEQ-2 | Lean: Lauri's Theorem 1.1 in full. For all `d ≥ 2`, `k ≥ 4d − 1`, `G_{d,k}` (central `K_{4d−1}`, pendant `u` at `c`, two `K_k` blocks at `v` and two at `w`; `4(k+d−1)` vertices) is a connected block graph with `L = k` and `χ_= = k + d`. Hence `χ_= − L` is unbounded on connected block graphs | Kyle + Claude, 2026-11-27 | pending audit | `lauri_family`, `gap_unbounded` in `Lab/BlockEquitable/Family.lean`; cross-check `explorer/block-equitable/family_check.py` (`d = 2..4`, four values of `k` each: colouring, all α values, clique number) |

Statement notes for the Auditor:
- `IsBlockGraph G` (ours): every vertex set `S` whose induced subgraph is connected and stays connected after
  deleting any single vertex of `S` is a clique. Such an `S` has at most two vertices or is 2-connected, so lies in
  a single block; conversely each block induces such a subgraph. So this is "every block is complete".
- `αAt G v = sSup {|s| : s independent, v ∈ s}` and `αmin G = ⨅ v, αAt G v` (minimum over a nonempty finite type).
- `L G = max G.cliqueNum ((|V| + 1 + αmin) / (αmin + 1))`, the ceiling of `(|V|+1)/(αmin+1)` in `ℕ`.
- `IsEquitableColoring G c` for `c : V → Fin q`: proper, and every class `i : Fin q` (empty ones included) has size
  between `|V| / q` and `(|V| + q − 1) / q` (floor and ceiling). `equitableChromaticNumber G` is the `sInf` of the
  `q` admitting one. This matches the paper's definitions (colour counts are positive integers there; `q = 0`
  admits no colouring of a nonempty graph anyway).
- `GapOneConjecture` quantifies over connected block graphs only (the original says every block graph), so its
  negation is the stronger statement.
- Proof follows the paper (Lemmas on `α_min`, the two-vertex obstruction, the explicit colouring):
  independent sets meet each part (`Q`, `B₁..B₄`, `{u}`) at most once (`indep_card_le`); the non-neighbours of `v`
  meet only `u, B₃, B₄`, so `α(G,v) ≤ 4` and, avoiding `u`, `≤ 3` (same for `w` with `B₁, B₂`); for `q ≤ 8` every
  class needs `⌊32/q⌋ ≥ 4`, but one of the classes of `v`, `w` misses `u` (`no_equitable_le_eight`). The block
  graph property uses that each `Bᵢ` and `{u}` is cut off by its anchor (`G_isBlockGraph`).
- Finite facts are `decide`/`decide +kernel` over `Fin 32`; no `set_option`.

Statement notes for BEQ-2:
- Same definitions as BEQ-1 (imported). Vertices are `Fin (4d−1) ⊕ (Unit ⊕ (Fin 4 × Fin (k−1)))`; adjacency is
  given by cases (`adjR`), with `v, w, c` the `Q`-indices `0, 1, 2` and blocks `0, 1` at `v`, `2, 3` at `w`.
- `gap_unbounded C`: some connected block graph has `L + C < χ_=` (take `d = C + 2`, `k = 4d − 1`).
- The `(k+d)`-colouring is the paper's (Lemma 7, colours shifted down by one, with `Y₁ = [2,d]`,
  `Y₂ = [d+1,2d−1]`, `Y₃ = [2d,3d−1]`, `Y₄ = [3d,4d−3] ∪ {m, m+1}`); block `j` takes its allowed colours in
  increasing order (`f`), with explicit inverse `g`.
- All arguments are general (no `decide` over `d`, `k`); no `set_option`.

## Dead ends and notes
- Other fresh disproofs scouted the same day (none on AFTD): dominating Hadwiger (2609.35361, probabilistic),
  Oxley circuit–cocircuit via the Golay matroid (2610.06033, needs representable matroids), the CGS gap-set
  question (2609.04473), weighted union-closed variant (2609.25101, asymptotic), local antimagic leaves
  (2610.22783). Listed as leads in `ledger/shortlist.md` (Round 5).
- Open (from the paper): is `χ_=(G) ≤ C·L(G)` for connected block graphs? The family forces `C ≥ 9/7`.
