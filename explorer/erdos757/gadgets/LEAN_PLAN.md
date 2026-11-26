# Lean plan: `sSup {c | IsAdmissible c} ≤ 5/9`

**Done (2026-11-25):** `Lab/Erdos757/FiveNinths.lean`. The final design differs a little from this plan:
the no-mixing checker covers every point of O (not only depth 0), so the induction only needs a
finite check of S_2, and the (4,5) property comes from two forbidden patterns (`card45`).

Goal: formalize `five_ninths_all_k.py`.

## Statement shape
For every K there is a finite (4,5)-set S_K ⊂ ℝ with `ncard = 11 + 9K` whose Sidon subsets have
at most `7 + 5K` elements. Then `IsAdmissible c → c ≤ (7+5K)/(11+9K)` for all K, and letting
K → ∞ gives `c ≤ 5/9`. The last step is a short real-analysis lemma (or use
`(7+5K)/(11+9K) - 5/9 = 8/(9(11+9K))`).

Work in ℚ (or in ℤ after scaling by 269^K) and cast to ℝ as in `FourSevenths.lean`.
Define `S 0 = O`, `S (K+1) = O ∪ φ '' S K` with `φ x = 101 + 18x/269`. This recursion makes
every proof an induction on K.

## Pieces, easiest first
1. **Sidon bound** (small). Define the trace of I on O and on φ''(S K). Prove the two finite
   inequalities of `transfer_certificate.py` by `decide` on 2^11 subsets, then telescope by
   induction: `|I| ≤ 6 + 5K + π(state)`. No geometry is needed. This is about the size of
   FourSevenths.lean.
2. **Counting** (small). `S K ⊆ [0,269]`, `φ''(S K) ⊆ [101,119]`, `φ²''(S K) ⊆ I_2`,
   `O ∩ φ''(S K) = {101,119}` (using `O ∩ I_2 = ∅`), so `ncard (S (K+1)) = ncard (S K) + 9`.
   This needs `norm_num` and interval lemmas.
3. **Base case** (medium). S_1 has 20 points and is (4,5): `decide` over C(20,4) = 4845 four-subsets.
   That is 5× the 14-point check, so split it as in FourSevenths. It also needs the list of the 18 APs.
4. **No mixing** (hard, the main risk). The Python check enumerates about 200k slot assignments at
   level 1. Brute `decide` would far exceed the ~8 GB kernel budget. Plan: write a computable
   checker over ℤ (scaled by 269^3) that prunes with sorted lists, prove it sound once, then
   evaluate it by `decide`. The alternative is to split the enumeration by the depth-0 point
   (11 pieces) and use interval reasoning per piece. The soundness proof uses depth
   normalization (φ⁻¹ preserves relations with coefficient sum 0) and the nested intervals.
5. **(4,5) for all K** (medium). Show that "(4,5)" is equivalent to "no 4-point relation and APs
   pairwise share ≤ 1 point" for 4-sets of reals, using `(B - B).ncard`. Then combine 3 and 4 with
   the cross-level case (no AP of O contains both 0 and 269).

## Estimate and risk
Pieces 1, 2, 3 and 5 are routine but long (roughly 600–1000 lines in total). Piece 4 is the
real risk: whether a soundly proven pruning checker fits within the kernel's time and memory.
Recommended order: prototype piece 4 first, since it decides feasibility, then 1, 2, 3, 5.
