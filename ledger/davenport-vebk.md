---
problem: van Emde Boas–Kruyswijk conjecture on the Davenport constant of C_n^r (1969)
source: https://arxiv.org/abs/2611.24775 (Gao, Geroldinger, Wang, Zeng; v3, 24 Nov 2026); conjecture in Gao–Geroldinger survey 2006, Conjecture 3.5
lean_statement: none upstream (formal-conjectures 9097e2f has no Davenport-constant file); ours is Lab/Davenport/VanEmdeBoasKruyswijk.lean
status: active
budget_usd: 150
spent_usd: 0
owner: Kyle
---

# Davenport constant of C_n^r: the van Emde Boas–Kruyswijk conjecture

## Statement
`D(G)` is the least `ℓ` such that every sequence of `ℓ` elements of the finite abelian group `G`
has a nonempty subsequence summing to 0. Van Emde Boas and Kruyswijk (1969) conjectured
`D(C_n^r) = r(n-1) + 1` for all `n, r`. The lower bound `≥` is classical, so the content is
`≤`: every sequence of `r(n-1)+1` elements has a nonempty zero-sum subsequence.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| True for prime-power `n` and for `r ≤ 2` | Olson, Kruyswijk (1960s) | no |
| `D(C_n^r) ≥ r(n-1)+1+⌊(r-1)/(5k-1)⌋` for `n = 2k`, `k ≥ 3` odd: conjecture false from rank `5k` (rank 15 for n = 6) | GGWZ arXiv:2611.24775 v3, Thm 1.1 | **yes, the full theorem (every n ≡ 2 mod 4, n ≥ 6, every r, with the floor term): Lean-checked (DAV-4)**; n = 6 and n = 10 also by CP-SAT |
| Remark: `D(C_6^r) ≥ 5r+1+⌊(r-1)/8⌋` (counterexample from rank 9) | GGWZ v3, Remark after Thm 1.1 (no proof given) | no |
| v1 of the same preprint: counterexample from rank 23 (different construction) | GGWZ v1, 18 Nov 2026 | no (superseded by v3) |
| `D(C_n^3) = 3n-2` for all large `n` | GGWZ v3, Thm 1.2 | no |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| DAV-1 | There is a zero-sumfree sequence of 76 = 15·5+1 elements of (Z/6)^15, so `D(C_6^15) ≥ 77` and the van Emde Boas–Kruyswijk conjecture is false (`not_vanEmdeBoasKruyswijk`). The construction is GGWZ's (v3), the formalization is ours. | Kyle + Claude | audited (internal, PR 29) | `Lab/Davenport/VanEmdeBoasKruyswijk.lean` |
| DAV-3 | For every `n ≡ 2 (mod 4)`, `n ≥ 6`, and every `r` with `2r ≥ 5n`, there is a zero-sumfree sequence of `r(n-1)+1` elements of `(Z/n)^r` (`Family.ggwz`); this is the "in particular" part of GGWZ Theorem 1.1, for the whole family. The floor-term bound `+⌊(r-1)/(5k-1)⌋` (replacement step) is DAV-4. | Kyle + Claude | audited (internal) | `Lab/Davenport/GeneralFamily.lean` |
| DAV-4 | Full GGWZ Theorem 1.1: for every `n ≡ 2 (mod 4)`, `n ≥ 6` (`n = 2k`) and every `r`, there is a zero-sumfree sequence of `r(n-1) + ⌊(r-1)/(5k-1)⌋` elements of `(Z/n)^r` (`Floor.ggwz_floor`), i.e. `D(C_n^r) ≥ r(n-1) + 1 + ⌊(r-1)/(5k-1)⌋`. Formalizes the paper's replacement step (`Floor.replace`) on top of DAV-3. | Kyle + Claude | audited (internal, PR 35 review) | `Lab/Davenport/FloorTerm.lean` |
| DAV-2 | GGWZ v3 sequences for n = 6 (rank 15, length 76) and n = 10 (rank 25, length 226) are zero-sumfree, by a CP-SAT infeasibility verdict (no certificate exported) that does not use the paper's argument | Kyle + Claude | solver verdict | `explorer/davenport/` |

## Novelty (checked 2026-11-26)
- The DARC verification board for this preprint lists "Lean or other formal proof" as open: none known.
- The preprint itself mentions no computer check or formal proof.
- Mathlib has no Davenport constant; formal-conjectures (our pin) has no file on it.
- A Zenodo note (Fujimoto, Apr 2026) formalizes only tiny cases `D(Z_3..Z_5)`, `D(Z_2²)` via `native_decide`.
- So DAV-1 appears to be the first machine-checked disproof. The mathematics is GGWZ's.

## Log
- 2026-11-26 (afternoon): Lean proof of the full Theorem 1.1 with the floor term (DAV-4). The
  replacement step is a general lemma (`replace`: any `P` over `K × C_n` whose `K`-vanishing
  nonempty subsums all have `C_n`-part 1 can replace one term `g` of a zero-sumfree `A`); the key
  property of `P` (base sequence minus the `n - 2` copies of `F₁`) is `P_key`; iterating from basis
  sequences gives `ggwz_floor` for every `r` (including `r = 0`). No `decide`; build ~10 s.
- 2026-11-26 (later): Lean proof for the whole family (DAV-3): every n ≡ 2 mod 4, n ≥ 6, every
  rank r ≥ 5n/2. Arithmetic is symbolic in t (n = 4t+2): block and leaf lemmas reduce each
  congruence to a few multiples of n, then omega. Build ~10 s, leanchecker 6.1 GB.
- 2026-11-26: Rank-9 search for n = 6 (Remark): negative. Rank-2 blocks are exhaustively impossible,
  and structured annealing came within 1 condition. Details are in explorer/davenport/rank9/.
- 2026-11-26: Scouted Tao constants with no 2026 activity; picked this because the 8-day-old
  disproof has an explicit, elementary construction and no formal check. Built the k = 3
  sequence, confirmed zero-sumfree by CP-SAT (k = 3, 5), formalized in Lean (block lemma +
  leaf lemma by `interval_cases`/`omega`, multiset-to-count bridge). Build ~2 min, leanchecker
  peak 6.5 GB.

## Next
- Rank-9 claim for n = 6 (Remark): searched, not found; see `explorer/davenport/rank9/README.md`.
