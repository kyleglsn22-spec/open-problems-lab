---
problem: Exact codegree conjecture for tight Hamiltonian cycles, all-n form (Rödl–Ruciński–Szemerédi Conjecture 1.1, attributed to Katona–Kierstead)
source: https://doi.org/10.5281/zenodo.23006717 (A. Ferudun, Sep 2026, Theorem 1.2(a)); conjecture: Rödl–Ruciński–Szemerédi, Adv. Math. 227 (2011), Conjecture 1.1; Oberwolfach Reports 48/2006 and 01/2008
lean_statement: Lab/TightHamilton/Basic.lean (all definitions stated by us); main theorems in Lab/TightHamilton/Main.lean
status: solved (formalized)
---

# Exact codegree conjecture for tight Hamiltonian cycles (all-`n` form)

## Statement
A `k`-graph has a tight Hamiltonian cycle if its vertices have a cyclic order in which every `k` cyclically
consecutive vertices form an edge. Conjecture: every `k`-graph on `n ≥ k + 1 ≥ 4` vertices whose `(k − 1)`-sets all
have codegree at least `⌊(n − k + 3)/2⌋` has a tight Hamiltonian cycle.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| True for `k = 3` and all large `n` | Rödl–Ruciński–Szemerédi 2011 | No |
| Announced for every fixed `k ≥ 3` and all large `n` | Letzter–Lang–Ranganathan–Sanhueza-Matamala (reported in L.-M. Zhang, arXiv:2609.08613, as cited by Ferudun) | No |
| False for small `n`: `H_k` (hemi-icosahedron on 6 points plus `k − 2` apexes) for `(k, n) = (3, 7), (4, 8), (5, 9)` | Ferudun 2026, Thm 1.2(a) | Yes (TH-1) |
| Further SAT-found counterexamples at `(3, 9)` and `(5, 10)`; 7 vertices is minimal | Ferudun 2026, Thm 1.2(b,c) | No |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| TH-1 | Lean: the all-`n` conjecture is false. For `k = 3, 4, 5`, Ferudun's `H_k` on `k + 4` vertices is `k`-uniform, has minimum codegree `≥ 3 = ⌊7/2⌋`, and has no tight Hamiltonian cycle | Kyle + Claude (Opus 5.5), 2026-11-28 | proved, internal audit pass with notes | `not_codegreeConjecture`, `H_counterexample` in `Lab/TightHamilton/Main.lean`; independent check `audit/tight_hamilton_check.py` (all cyclic orders) |

Statement notes for the Auditor:
- Vertices are `Fin (k + 4)`; `W = {0,…,5}` (the paper's `1,…,6` shifted down by one), apexes are `6,…,k+3`.
  `Dface` is the paper's list `D′` shifted by one.
- `HasTightHamiltonCycle E k`: a bijection `f : Fin n → V` with every window
  `{f(i), f(i+1), …, f(i+k−1)}` (indices mod `n`) in `E`.
- `CodegreeConjecture` quantifies over `k ≥ 3`, `n ≥ k + 1`, `k`-uniform `E`, and the codegree bound with natural
  subtraction and floor division, `(n − k + 3)/2`.
- Proof of no cycle (modeled on Ferudun's Lemma 2.4; the kernel checks its conclusion over every apex position set): the set `P` of positions holding apexes has `k − 2` elements;
  `ForcedPair k` (kernel `decide`, `k = 5` split by the least position of `P` for CI memory) gives two windows each
  with exactly three non-apex positions, and these triples are disjoint. Both triples' images must be faces, but any
  two faces meet (`Dface_meet`).
- Codegree: `codegree_E_eq` rewrites the codegree of a `(k − 1)`-set `S` as the number of `x ∉ S` with
  `S ∪ {x}` good; the kernel then checks `≥ 3` for every `S`.

## Dead ends
None.
