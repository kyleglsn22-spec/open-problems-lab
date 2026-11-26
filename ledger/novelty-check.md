# Novelty check: are our results firsts? (2026-11-25)

Scope: claims 757-1, 757-2 (Lean proofs of Erdős #757 upper bounds) and C37-1 (short proof of
Koshta's degree-4 theorem). Searches were bounded: a missed private or unindexed result is possible.

## What we can honestly claim

**757-1 / 757-2: very likely the first complete Lean proofs of the #757 upper bounds
(Gyárfás–Lehel's < 3/5 and Ma–Tang's ≤ 4/7).** Evidence, all checked 2026-11-25:

| Place | What is there |
| --- | --- |
| formal-conjectures `ErdosProblems/757.lean` (main) | Statement only; `lowerBound` and `upperBound` are both `sorry`. No `4/7` variant. |
| formal-conjectures PRs #2696, #3218 (Mar 2026) | "formally solved erdos_757 lowerBound and upperBound": closed unmerged. They used the "formally solved elsewhere" pattern and still contain `sorryAx`, so not proofs. |
| formal-conjectures PR #5244 (merged Sep 2026) | Fixed the statement from `= 11` to `11 ≤ (B - B).ncard`; our proofs target the fixed statement. |
| teorth/erdosproblems `data/problems.yaml` | #757 `formal_status: unformalized` (no Lean proof recorded). |
| erdosproblems.com/757 page and forum | No mention of any formal proof. |
| LeanGenius (leangenius.org/proof/erdos-757) | Statement file, "work in progress", bounds only as prose. |
| Lean Zulip (public archive), Mathlib, arXiv | Nothing on #757 found. |

Caveat: the mathematics is not new (the witness sets are published: 757-1 uses a known f(12) = 7
set, 757-2 is Ma–Tang's 14-point set). The new part is the machine-checked proof against the
public formal-conjectures statement. Natural way to make it count: upstream `UpperBound.lean`
to formal-conjectures as a proof of `erdos_757.variants.upperBound`, and add a `≤ 4/7` variant.

**4/7 is no longer the best known upper bound.** An anonymous reader submission on
erdosproblemaday.com (7bkzb8, refereed there by AI agents 19 Oct 2026, not reviewed by humans)
gives a self-similar family with 11 + 9K points and largest Sidon subset 7 + 5K, so c ≤ 5/9 in
the limit; a single finite set beats 4/7 from K = 6 (65 points, 37/65 ≈ 0.5692). We rechecked it
for K ≤ 8 with two independent solvers (`explorer/erdos757/check_five_ninths.py`, exact arithmetic +
CP-SAT; the Auditor's HiGHS MILP): every S_K is a (4,5)-set and h = 7 + 5K is optimal. With Ma–Tang's
inf characterization this verifies c ≤ 47/83 ≈ 0.5663. The limit c ≤ 5/9 is claimed: it rests on the
site's all-depth argument, AI-refereed and not yet checked by us. The erdosproblems.com page and Tao's constant 5b still list 4/7.
Consequence: a Lean proof of ≤ 37/65 (or any S_K, K ≥ 6) would be both a first and the best
formally-checked bound, but it needs a structured proof (cross-copy relations vanish, then a per-copy
bound); enumerating 38-subsets of 65 points is out of reach. Salavatov (Zenodo 10.5281/zenodo.23494596, Oct 2026) reports that no
(4,5)-set beats 4/7 below 25 points and that (n, h) = (16, 9) is impossible.

**C37-1: not a first.** The original proof (Koshta) and one later reproof (Pinho) predate ours:
- Koshta's own certificate (teorth/optimizationproblems PR 283; 479-leaf branch-and-bound, checked
  by `viprchk`).
- Pinho, hexagonmath 2610.00694 v2 (30 Oct 2026): a rational Fourier-lattice functional that
  reproves B4 ≤ 9 (and he says himself the bound is not new).

What we can say: ours is an independent, short certificate by a different method (one LP over
(8,2)-block orbit sums forcing a non-integer value 14/3), audited internally. No formal (Lean)
proof of the degree-4 result exists anywhere we looked, so formalizing C37-1 would be a first.

## Sources
- https://www.erdosproblems.com/757 and https://www.erdosproblems.com/forum/thread/757
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/757.lean
- https://github.com/google-deepmind/formal-conjectures/pull/2696, /pull/3218, /pull/5244
- https://github.com/teorth/erdosproblems/blob/main/data/problems.yaml (entry 757)
- https://www.leangenius.org/proof/erdos-757
- https://teorth.github.io/optimizationproblems/constants/5b.html and /37a.html
- https://erdosproblemaday.com/day/757-reader-five-ninths-refereed
- https://doi.org/10.5281/zenodo.23494596
- https://hexagonmath.org/2610.00694v2
