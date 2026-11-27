---
problem: Erdős Problem 757 (Tao constant C5b)
source: https://www.erdosproblems.com/757
lean_statement: FormalConjectures/ErdosProblems/757.lean (formal-conjectures 9097e2f)
status: Ma–Tang upper bound (4/7) Lean-checked and audited (internal); 4/7 now beaten: c ≤ 5/9 Lean-checked for all K (`Lab/Erdos757/FiveNinths.lean`, theorem `sSup_le_five_ninths`; internal audit 2026-11-25); best known lower bound (9/17) Lean-checked conditional on the Henning–Yeo theorem (claim 757-3), and now unconditionally: the Henning–Yeo Theorem 6 bound formalized (claim 757-4, internal audit 2026-11-26, pass with notes)
---

# Erdős #757: Sidon subsets of (4,5)-sets

## Statement
A finite set of reals is a (4,5)-set if every four of its elements determine at least five
distinct positive differences. What is the largest c such that every (4,5)-set A contains a
Sidon subset of size at least c|A|?

Auditor (2026-11-25): matches erdosproblems.com and the upstream Lean statement. `11 ≤ (B - B).ncard`
is exactly "at least 5 distinct positive differences", and by Ma–Tang Prop. 3.7 the inf over all
finite sets equals the asymptotic constant. Details in `ledger/audits.md`.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| c > 1/2 | Gyárfás–Lehel 1995 | No |
| c < 3/5 | Gyárfás–Lehel 1995 | Yes: Lean proof of `≤ 7/12` (claim 757-1, audited internally) |
| c ≥ 9/17 ≈ 0.5294 | Ma–Tang, arXiv:2602.23282 | Yes (claim 757-4): every step in Lean, including the Henning–Yeo theorem |
| c ≤ 4/7 ≈ 0.5714 | Ma–Tang, arXiv:2602.23282 | Yes: Lean proof (claim 757-2, audited internally) |
| c ≤ 5/9 (reader's self-similar family); first set below 4/7: 65 points, 37/65 ≈ 0.5692 | Reader submission 7bkzb8, erdosproblemaday.com, Oct 2026 (unreviewed by humans) | Partly: S_K for K ≤ 8 checked by two independent solvers (CP-SAT, `explorer/erdos757/check_five_ninths.py`; HiGHS MILP, Auditor), so c ≤ 47/83 ≈ 0.5663 verified. **All K: c ≤ 5/9 checked by us**: exact computer proof `explorer/erdos757/gadgets/five_ninths_all_k.py`, and **Lean-checked** in `Lab/Erdos757/FiveNinths.lean` (`sSup_le_five_ninths`, standard axioms only) |
| No (4,5)-set beats 4/7 below 25 points; (16, 9) impossible | Salavatov, Zenodo 10.5281/zenodo.23494596, Oct 2026 | No |
| Exact f(n) for n = 6..15, 17, 19, 21 | Suresh Kannan 2026 (data and checker, Claude-assisted) | No |

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| 757-1 | `erdos_757.variants.upperBound` follows from one 12-element (4,5)-set with largest Sidon subset 7 (7/12 < 3/5) | Claude (Opus 5.5), from the published f(12) = 7 | **checked** (internal audit 2026-11-25, pass with notes; outside review welcome) | `Lab/Erdos757/UpperBound.lean` (PR #4): witness {0, 92, 95, 107, 119, 184, 188, 190, 238, 261, 284, 384}, finite facts by `decide +kernel` (the Sidon bound goes through the 10 three-term progressions in the set), axioms only propext/Classical.choice/Quot.sound, leanchecker passes. Also `explorer/erdos757/check_n12.py`. Statement fidelity and witness confirmed by the in-house Auditor: `ledger/audits.md`, `audit/erdos757_check.py` |
| 757-2 | `sSup {c | IsAdmissible c} ≤ 4/7` (best known upper bound) follows from Ma–Tang's 14-element (4,5)-set with largest Sidon subset 8 | Claude (Opus 5.5), from Ma–Tang arXiv:2602.23282 §5.1 | **checked** (internal audit 2026-11-25, pass; outside review welcome) | `Lab/Erdos757/FourSevenths.lean`: witness {0, 136, 200, 243, 246, 249, 272, 286, 298, 323, 400, 528, 596, 1056}, same method as 757-1 (Sidon bound via the 12 three-term progressions), finite checks split into pieces so the kernel re-check stays at ~8.2 GB like 757-1. Axioms only propext/Classical.choice/Quot.sound. Also `explorer/erdos757/check_n14.py` |
| 757-3 | `HenningYeoBound → 9/17 ≤ sSup {c | IsAdmissible c}` (hence the upstream `1/2 < sSup`): Ma–Tang's lower bound, with the Henning–Yeo transversal theorem (Graphs Combin. 37 (2021), Thm. 7) as the only assumption | Claude (Opus 5.5), from Ma–Tang arXiv:2602.23282 §5.2 | **checked, conditional on Henning–Yeo** (internal audit 2026-11-25, pass with notes; outside review welcome) | `Lab/Erdos757/LowerBound.lean`: proves unconditionally that every (4,5)-set is weak Sidon, Sidon = 3-AP-free inside it, its 3-AP hypergraph has ≤ n edges, is linear, and has no copy of F7 (Gyárfás–Lehel Prop. 2.6, re-proved here by a 243-case check). Henning–Yeo enters as the hypothesis `HenningYeoBound`. Axioms only propext/Classical.choice/Quot.sound; leanchecker 7.0 GB |
| 757-4 | `9/17 ≤ sSup {c | IsAdmissible c}` and the upstream `1/2 < sSup`, **with no hypothesis**: the Henning–Yeo Theorem 6 bound (first half: `17τ ≤ 4n + 4m + h` for linear 3-uniform F7-free hypergraphs) proved in Lean; the strict part only in a corrected, weaker form used by the induction, hence their Theorem 7 and `HenningYeoBound` | Claude (Opus 5.5), from Henning–Yeo, Graphs Combin. 37 (2021) 867–890 | **checked** (internal audit 2026-11-26, pass with notes; outside review welcome) | `Lab/HenningYeo/` (Claims 1–15, `Theorem6.lean`: `theorem6`), `Lab/Erdos757/Unconditional.lean`: `henningYeoBound`, `nine_seventeenths_le_sSup_unconditional`, `erdos_757_lowerBound` (exact upstream type). Two issues in the paper are handled (see `ledger/henning-yeo-plan.md`). Axioms only propext/Classical.choice/Quot.sound; template checks split so each kernel re-check stays under ~7.4 GB |

## Log
- 2026-11-25: Picked for the first round. DeepMind's AlphaProof Nexus did not attempt it. Both
  known bounds are `sorry` upstream, so Lean proofs of them are a contribution to formal-conjectures.

- 2026-11-25: Claim 757-1 proved in Lean (PR #4). Builds against formal-conjectures 9097e2f
  with no sorry and standard axioms only. Our theorem proves the stronger `sSup ≤ 7/12`.
  Next: the lower bound `> 1/2` from Gyárfás–Lehel, or upstream the proof to formal-conjectures.

- 2026-11-25: In-house Auditor passed claim 757-1 (statement fidelity, axioms, independent witness
  check). Suggested next: Lean proof of `≤ 4/7` from Ma–Tang's 14-point set (best known bound).
- 2026-11-25: Claim 757-2: Lean proof of the best known upper bound `≤ 4/7` (Ma–Tang's
  14-point set). With this, the best known upper bound is formalized; the gap that
  remains open in mathematics is 9/17 ≤ c ≤ 4/7. Next: Lean proof of a lower bound.
- 2026-11-25: Claim 757-3: Ma–Tang's lower bound `9/17` in Lean, conditional on Henning–Yeo.
  All of Ma–Tang's own steps and the Gyárfás–Lehel F7 lemma are now formal. What remains for
  an unconditional `9/17` is formalizing Henning–Yeo (24 pages of hypergraph case analysis);
  an unconditional `> 1/2` would also need a hypergraph transversal theorem (Gyárfás–Lehel).
  Note (coordinator, 2026-11-25): an unreviewed claim puts the upper bound at 5/9.

- 2026-11-25: Novelty check (`ledger/novelty-check.md`). No complete Lean proof of either #757
  bound exists elsewhere (formal-conjectures still `sorry`; two loophole PRs closed unmerged), so
  757-1/757-2 are very likely the first. But 4/7 is no longer best: a reader's self-similar family
  claims 5/9 (all-depth argument AI-refereed, not checked by us); we verified S_K for K ≤ 8, so c ≤ 47/83.
  Next: a Lean proof below 4/7 needs a structured argument (relations stay inside each copy, plus the
  per-copy transfer bound); the 757-1/757-2 enumeration method cannot scale to 65 points.

- 2026-11-25: Search for a construction below 5/9 (thread "Improve Erdős #757 upper bound").
  Class: self-similar chains like the reader's family (copies glued on 2 points, copy min/max
  attached at an interior pair). The Sidon growth per copy is a 4×4 max-plus cycle mean, with a
  finite potential certificate. For the 5/9 family it gives h(S_K) ≤ 7 + 5K for every K
  (`explorer/erdos757/gadgets/transfer_certificate.py`; needs no geometry). The other half of an
  all-K proof (|S_K| = 11 + 9K, S_K a (4,5)-set) is still open for us. An exact solver
  (ordered SAT plus exact rational geometry, CEGAR) rediscovers 5/9 gadgets at 11 points in seconds.
  It finds **no gadget beating 5/9 with 12, 13 or 14 points**, within this class: rigid O (or one
  spare non-middle point, checked for 12 and 13), 2-point gluing with the copy's min/max attached.
  For 12 the search is complete. For 13 and 14 it uses bounded potentials. 12 and 14 are already
  impossible from the progression structure alone. Computer search, not proof-logged. 15 points was too slow for the
  exact solver. Details: `explorer/erdos757/gadgets/README.md`.
- 2026-11-25: All-K proof of the reader's 5/9 family (`explorer/erdos757/gadgets/five_ninths_all_k.py`,
  exact, computer-assisted). Counting: copies meet only in the glued pair. Base case: S_1 is a
  (4,5)-set. No mixing: no additive relation spans copies two levels apart (interval refinement
  closes at level 3). Sidon bound: transfer certificate. Hence c ≤ 5/9 checked by us for all K
  (computer-assisted, exact; internal audit; not yet in Lean).

- 2026-11-25: Lean proof of `sSup {c | IsAdmissible c} ≤ 5/9` (`Lab/Erdos757/FiveNinths.lean`, about
  1,300 lines). Same structure as the Python proof: counting (`card_S`), Sidon bound by a transfer
  argument (`sidon_bound`), and the (4,5) property via two forbidden patterns (`good_S`, `card45`),
  with a finite check of S_2 and a kernel-checked "no mixing" interval computation (`nmA`, `nmB1`,
  `nmB2`). All finite facts use `decide +kernel`; the checks are split into ~150 small pieces and
  run one at a time (`Elab.async false`) so the kernel replay stays under 7 GB.

## Dead ends
- Self-similar 2-point chain gadgets (rigid O, min/max attached) with 12, 13 or 14 points do not beat 5/9 (exact search, 2026-11-25; complete for 12, bounded potentials for 13–14; not proof-logged). Binary-tree gluing of the reader's O is worse (0.587). Random search at 15 points: best 8/13 ≈ 0.615.
- Multi-point gluing (2 or 3 shared points, any affine contraction) of the reader's O and of the Ma–Tang 14-point set: upper-estimate ratios (within-copy transfer value, ignoring cross-copy relations and (4,5)) best 5/9 and 7/12; not a proof that these gluings cannot beat 5/9; maps with overlapping shared sets skipped (2026-11-25, `explorer/erdos757/gadgets/multiglue.py`). Exact 16-point gadget search: solver too slow (first SAT call > 120 s on all 18 port choices tried).
- 2026-11-26: Claim 757-4: the Henning–Yeo Theorem 6 bound formalized (about 7,700 lines under
  `Lab/HenningYeo/`), so Ma–Tang's lower bound `9/17` is now Lean-checked with no assumption.
  Both best known bounds for #757 (9/17 ≤ c ≤ 5/9 by our own upper bound) are formal.
- 2026-11-27: New search method, attempted as a hard item, with no improvement on 5/9.
  - Method: hypergraph first. A generic point of the linear space cut out by the 3-AP relations of an
    abstract hypergraph H is a (4,5)-set whose 3-AP hypergraph is exactly H, provided no extra difference
    coincidence is forced. That is a fast exact test with no ordering or SAT (`explorer/erdos757/hyper/hsearch.py`).
    - It rediscovers f(12) = 7 in seconds, and accepts Ma–Tang's 14-point set.
  - Periodic class (`periodic.py`): vertices (period k, class i), with a fixed list of 3-AP patterns. This is
    strictly larger than the self-similar chains of PR 13: copies need not be affine images.
    - The reader's 5/9 family sits in it (w = 9, offsets {−1, 0}). Window estimates give 5/9 for it, as they should.
  - Annealing results:
    - Unseeded (w ≤ 9): ≥ 0.60.
    - Seeded from the 5/9 pattern with 10–12 classes (offsets ≤ 1, about 2 h): best 0.59.
    - Free hypergraph search, n = 20–32: ≥ 0.60.
  - Nothing below 5/9. The annealer is weak (it does not rediscover 5/9 from scratch). A stronger search,
    for example SAT over pattern choices with the realizability test as a CEGAR oracle, is the obvious next
    step. Parked.
