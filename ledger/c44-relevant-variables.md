---
problem: Relevant variables of bounded-degree Boolean functions (Tao constant C44)
source: https://teorth.github.io/optimizationproblems/constants/44a.html
lean_statement: Lab/C44/LowerBound.lean (our own statement; formal-conjectures 9097e2f has none)
status: paused (lower side: block compositions ruled out; Lean 3/2 done)
budget_usd: 150
spent_usd: 0
owner: Kyle
---

# C44: how many variables can a degree-d Boolean function depend on?

## Statement
R_d = the largest number of relevant variables of a Boolean function of real degree ≤ d.
C44 = sup_d R_d / 2^d. Known: 3/2 ≤ C44 ≤ 4.3576549226* (table); Pinho's unrefereed candidate C44 < 1.9917.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| R_d ≥ 3·2^(d-1) − 2, so C44 ≥ 3/2 | Chiarelli–Hatami–Saks 2018 (arXiv:1801.08564), Shinkar–Tal | **Lean-checked (claim C44-1)** |
| R_d ≥ 2R_(d-1) + 2 (CHS gadget, any d) | same | No (Lean covers only the CHS functions Ξ_d) |
| R_3 = 10 | Tarannikov–Kirienko 2000 | No |
| R_4 = 22, 46 ≤ R_5 ≤ 50, 94 ≤ R_6 ≤ 107 | Pinho, Nov 2026, unrefereed (rpinho/math-certificates c44/small-degree-classification) | No |
| C44 ≤ 4.394 / 4.3577* / < 1.9917* | Wellens 2022 / Pinho Oct 2026 / Pinho Nov 2026 | No |

Because (R_d + 2)/2^d never decreases (the CHS gadget), the lower bound 3/2 improves as soon as
**R_5 ≥ 47** or **R_6 ≥ 95**. Nobody has improved it since 2018 (Pinho: "no improvement of the
lower bound is certified"). This is the question we attacked.

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| C44-1 | For every d ≥ 1 there is a Boolean function of degree ≤ d with 3·2^(d-1) − 2 relevant variables; hence any C with R(f) ≤ C·2^deg(f) for all f satisfies C ≥ 3/2 | Kyle + Claude | Lean-checked; internal audit pass (PR 25) | `Lab/C44/LowerBound.lean`: `exists_degLE_all_relevant`, `three_halves_le` |
| C44-2 | No block composition with ≤ 9 blocks beats CHS at degree 5 (127 shapes) or degree 6 (361 shapes); most 10–11-block shapes also ruled out (explorer/c44/README.md) | Kyle + Claude | internal audit pass as solver verdicts (two CP-SAT encodings agree; SCIP cross-check on all ≤ 6-block degree-5 shapes; Auditor brute force on ≤ 4 blocks) | `explorer/c44/` |

## Log
- 2026-11-26: picked up as the backup problem. Upper side is crowded (Pinho, several rounds in Oct–Nov
  2026), lower side quiet. Lean proof of the CHS construction (C44-1). Searched block compositions
  ("weighted-degree" gadgets) at degree 5 and 6 for a function beating CHS: none found (C44-2).

## Dead ends
- Signed-partition gadgets F = Σ_j s_j(x)·h_j(y_j) (h_j disjoint extremal functions) with ≤ 7 control
  bits at degree 5: all infeasible. Subsumed by the weighted-degree search.
- Weighted-degree block compositions (substitute extremal degree-w pieces into a small Boolean G of
  weighted degree ≤ d): see C44-2. Any improvement must come from a genuinely new degree-5 (or 6)
  function, not from composing degree ≤ 4 pieces in a small pattern.
