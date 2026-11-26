import Mathlib

/-!
# C37: no Boolean function of degree at most 4 has sensitivity 10

Koshta (2026) proved this with a 479-leaf branch-and-bound certificate. This file gives a short
proof (claim C37-1 in `ledger/c37-degree-sensitivity.md`).

Write `q x = ∑_{S ⊆ x} c S` with integer coefficients `c`. Split the 10 coordinates into
`A` (8 coordinates) and `B` (2 coordinates). For each pattern `(p1, p2)` let `Cp c p1 p2` be the sum
of `c S` over sets with `p1` elements in `A` and `p2` in `B`. The sum `N c w1 w2` of `q` over the
points with `w1` ones in `A` and `w2` in `B` is `∑ K 8 w1 p1 * K 2 w2 p2 * Cp c p1 p2` (`N_eq_Cp`),
and `0 ≤ N ≤ choose 8 w1 * choose 2 w2`. These 54 inequalities force `3 * Cp c 1 2 = 14`,
which is impossible for an integer.
-/

namespace OpenProblemsLab.C37

open Finset

/-- Number of `k`-subsets of `A` containing a fixed `T ⊆ A`. -/
lemma card_filter_superset_powersetCard {α : Type*} [DecidableEq α] (A T : Finset α)
    (hT : T ⊆ A) (k : ℕ) :
    ((A.powersetCard k).filter (fun y => T ⊆ y)).card =
      if T.card ≤ k then (A.card - T.card).choose (k - T.card) else 0 := by
  split_ifs with hk
  · rw [← card_sdiff_of_subset hT, ← card_powersetCard]
    apply card_nbij' (fun y => y \ T) (fun z => z ∪ T)
    · intro y hy
      simp only [mem_coe, mem_filter, mem_powersetCard] at hy ⊢
      refine ⟨sdiff_subset_sdiff hy.1.1 le_rfl, ?_⟩
      rw [card_sdiff_of_subset hy.2, hy.1.2]
    · intro z hz
      simp only [mem_coe, mem_filter, mem_powersetCard] at hz ⊢
      have hdisj : Disjoint z T := by
        rw [disjoint_left]; intro a ha haT; exact (mem_sdiff.mp (hz.1 ha)).2 haT
      refine ⟨⟨union_subset (hz.1.trans sdiff_subset) hT, ?_⟩, subset_union_right⟩
      rw [card_union_of_disjoint hdisj, hz.2]; omega
    · intro y hy
      simp only [mem_coe, mem_filter, mem_powersetCard] at hy
      simp [sdiff_union_of_subset hy.2]
    · intro z hz
      simp only [mem_coe, mem_filter, mem_powersetCard] at hz
      have hdisj : Disjoint z T := by
        rw [disjoint_left]; intro a ha haT; exact (mem_sdiff.mp (hz.1 ha)).2 haT
      simp [union_sdiff_right, hdisj.sdiff_eq_left]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro y hy hTy
    rw [mem_powersetCard] at hy
    exact hk (hy.2 ▸ card_le_card hTy)


/-- Block `A` = the first 8 coordinates, block `B` = the last 2. -/
abbrev A : Finset (Fin 10) := univ.filter (fun i => i.val < 8)
abbrev B : Finset (Fin 10) := univ.filter (fun i => 8 ≤ i.val)

/-- Value of the multilinear polynomial with coefficients `c` at the 0/1 point with support `x`. -/
def qval (c : Finset (Fin 10) → ℤ) (x : Finset (Fin 10)) : ℤ := ∑ S ∈ x.powerset, c S

/-- Sum of `q` over the points with `w1` ones in `A` and `w2` ones in `B`. -/
def N (c : Finset (Fin 10) → ℤ) (w1 w2 : ℕ) : ℤ :=
  ∑ xa ∈ A.powersetCard w1, ∑ xb ∈ B.powersetCard w2, qval c (xa ∪ xb)

lemma subset_union_iff_blocks {xa xb S : Finset (Fin 10)} (ha : xa ⊆ A) (hb : xb ⊆ B) :
    S ⊆ xa ∪ xb ↔ S ∩ A ⊆ xa ∧ S ∩ B ⊆ xb := by
  constructor
  · intro h
    constructor
    · intro i hi
      rw [mem_inter] at hi
      rcases mem_union.mp (h hi.1) with h1 | h1
      · exact h1
      · have := hb h1; simp [A, B] at hi this; omega
    · intro i hi
      rw [mem_inter] at hi
      rcases mem_union.mp (h hi.1) with h1 | h1
      · have := ha h1; simp [A, B] at hi this; omega
      · exact h1
  · rintro ⟨h1, h2⟩ i hi
    by_cases hlt : i.val < 8
    · exact mem_union_left _ (h1 (mem_inter.mpr ⟨hi, by simp [A, hlt]⟩))
    · exact mem_union_right _ (h2 (mem_inter.mpr ⟨hi, by simp [B]; omega⟩))

lemma N_eq (c : Finset (Fin 10) → ℤ) (w1 w2 : ℕ) :
    N c w1 w2 = ∑ S : Finset (Fin 10), c S *
      ((((A.powersetCard w1).filter (fun y => S ∩ A ⊆ y)).card : ℤ) *
       (((B.powersetCard w2).filter (fun y => S ∩ B ⊆ y)).card : ℤ)) := by
  have hpow : ∀ x : Finset (Fin 10), x.powerset = univ.filter (fun S => S ⊆ x) := by
    intro x; ext S; simp
  unfold N qval
  simp_rw [hpow, sum_filter]
  calc _ = ∑ xa ∈ A.powersetCard w1, ∑ S : Finset (Fin 10), ∑ xb ∈ B.powersetCard w2,
              (if S ⊆ xa ∪ xb then c S else 0) := by
          refine sum_congr rfl (fun xa _ => ?_); exact sum_comm
    _ = ∑ S : Finset (Fin 10), ∑ xa ∈ A.powersetCard w1, ∑ xb ∈ B.powersetCard w2,
              (if S ⊆ xa ∪ xb then c S else 0) := sum_comm
    _ = _ := by
          refine sum_congr rfl (fun S _ => ?_)
          rw [card_filter, card_filter, Nat.cast_sum, Nat.cast_sum, sum_mul_sum, mul_sum]
          refine sum_congr rfl (fun xa hxa => ?_)
          rw [mul_sum]
          refine sum_congr rfl (fun xb hxb => ?_)
          rw [mem_powersetCard] at hxa hxb
          have key := subset_union_iff_blocks (S := S) hxa.1 hxb.1
          by_cases h1 : S ∩ A ⊆ xa <;> by_cases h2 : S ∩ B ⊆ xb <;> simp [h1, h2, key]

lemma cardA : A.card = 8 := by decide
lemma cardB : B.card = 2 := by decide

/-- Pattern sums of the coefficients: sets with `p1` elements in `A` and `p2` in `B`. -/
def Cp (c : Finset (Fin 10) → ℤ) (p1 p2 : ℕ) : ℤ :=
  ∑ S ∈ univ.filter (fun S : Finset (Fin 10) => (S ∩ A).card = p1 ∧ (S ∩ B).card = p2), c S

/-- Count factor `K(w, p)`. -/
def K (n w p : ℕ) : ℤ := if p ≤ w then ((n - p).choose (w - p) : ℤ) else 0

lemma N_eq_Cp (c : Finset (Fin 10) → ℤ) (w1 w2 : ℕ) :
    N c w1 w2 = ∑ p1 ∈ range 9, ∑ p2 ∈ range 3, K 8 w1 p1 * K 2 w2 p2 * Cp c p1 p2 := by
  rw [N_eq]
  have hA : ∀ S : Finset (Fin 10),
      (((A.powersetCard w1).filter (fun y => S ∩ A ⊆ y)).card : ℤ) = K 8 w1 (S ∩ A).card := by
    intro S
    rw [card_filter_superset_powersetCard A (S ∩ A) inter_subset_right, cardA, K]
    split_ifs <;> simp
  have hB : ∀ S : Finset (Fin 10),
      (((B.powersetCard w2).filter (fun y => S ∩ B ⊆ y)).card : ℤ) = K 2 w2 (S ∩ B).card := by
    intro S
    rw [card_filter_superset_powersetCard B (S ∩ B) inter_subset_right, cardB, K]
    split_ifs <;> simp
  simp_rw [hA, hB]
  have hmaps : ∀ S ∈ (univ : Finset (Finset (Fin 10))),
      ((S ∩ A).card, (S ∩ B).card) ∈ range 9 ×ˢ range 3 := by
    intro S _
    have h1 : (S ∩ A).card ≤ 8 := cardA ▸ card_le_card inter_subset_right
    have h2 : (S ∩ B).card ≤ 2 := cardB ▸ card_le_card inter_subset_right
    simp only [mem_product, mem_range]; omega
  rw [← sum_fiberwise_of_maps_to hmaps, sum_product]
  refine sum_congr rfl (fun p1 _ => sum_congr rfl (fun p2 _ => ?_))
  unfold Cp
  rw [mul_sum]
  refine sum_congr ?_ (fun S hS => ?_)
  · ext S; simp [Prod.ext_iff]
  · simp only [mem_filter] at hS
    rw [hS.2.1, hS.2.2]; ring

lemma qval_nonneg_le (c : Finset (Fin 10) → ℤ) (hq : ∀ x, 0 ≤ qval c x ∧ qval c x ≤ 1)
    (w1 w2 : ℕ) : 0 ≤ N c w1 w2 ∧ N c w1 w2 ≤ (8 : ℕ).choose w1 * (2 : ℕ).choose w2 := by
  unfold N
  constructor
  · exact sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => (hq _).1))
  · calc _ ≤ ∑ xa ∈ A.powersetCard w1, ∑ xb ∈ B.powersetCard w2, (1 : ℤ) :=
          sum_le_sum (fun _ _ => sum_le_sum (fun _ _ => (hq _).2))
      _ = _ := by simp [card_powersetCard, cardA, cardB]

lemma qval_singleton (c : Finset (Fin 10) → ℤ) (h0 : c ∅ = 0) (h1 : ∀ i, c {i} = 1) (i : Fin 10) :
    qval c {i} = 1 := by
  have : ({i} : Finset (Fin 10)).powerset = {∅, {i}} := by
    ext S; simp [Finset.subset_singleton_iff]
  rw [qval, this, sum_pair (by simp), h0, h1]; norm_num

lemma N00 (c : Finset (Fin 10) → ℤ) (h0 : c ∅ = 0) : N c 0 0 = 0 := by
  simp [N, qval, h0]

lemma N10 (c : Finset (Fin 10) → ℤ) (h0 : c ∅ = 0) (h1 : ∀ i, c {i} = 1) : N c 1 0 = 8 := by
  unfold N
  rw [sum_congr rfl (g := fun _ => (1 : ℤ))]
  · simp [card_powersetCard, cardA]
  · intro xa hxa
    obtain ⟨i, rfl⟩ := card_eq_one.mp (mem_powersetCard.mp hxa).2
    simp [qval_singleton c h0 h1]

lemma N01 (c : Finset (Fin 10) → ℤ) (h0 : c ∅ = 0) (h1 : ∀ i, c {i} = 1) : N c 0 1 = 2 := by
  unfold N
  simp only [powersetCard_zero, sum_singleton, empty_union]
  rw [sum_congr rfl (g := fun _ => (1 : ℤ))]
  · simp [card_powersetCard, cardB]
  · intro xb hxb
    obtain ⟨i, rfl⟩ := card_eq_one.mp (mem_powersetCard.mp hxb).2
    exact qval_singleton c h0 h1 i

lemma Cp_high (c : Finset (Fin 10) → ℤ) (hd : ∀ S : Finset (Fin 10), 5 ≤ S.card → c S = 0)
    (p1 p2 : ℕ) (h : 5 ≤ p1 + p2) : Cp c p1 p2 = 0 := by
  unfold Cp
  refine sum_eq_zero (fun S hS => hd S ?_)
  simp only [mem_filter, mem_univ, true_and] at hS
  have : S.card = (S ∩ A).card + (S ∩ B).card := by
    rw [← card_union_of_disjoint]
    · congr 1; ext i; simp only [mem_union, mem_inter, A, B, mem_filter, mem_univ, true_and]
      constructor
      · intro hi; by_cases h8 : i.val < 8
        · exact Or.inl ⟨hi, h8⟩
        · exact Or.inr ⟨hi, by omega⟩
      · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
    · rw [disjoint_left]; intro i h1 h2
      simp only [mem_inter, A, B, mem_filter, mem_univ, true_and] at h1 h2; omega
  omega

/-- **No Boolean function of degree at most 4 has sensitivity 10.**
Stated for the multilinear coefficients `c` of `q : {0,1}^10 → {0,1}` (identifying a point with its
support `x`, so `q x = ∑_{S ⊆ x} c S`): `q(0) = 0` and `q(e_i) = 1` force `c ∅ = 0` and `c {i} = 1`,
degree `≤ 4` means `c S = 0` for `|S| ≥ 5`, and Boolean values mean `0 ≤ q x ≤ 1` (`c` is integral). -/
theorem no_degree4_sensitivity10 :
    ¬ ∃ c : Finset (Fin 10) → ℤ, c ∅ = 0 ∧ (∀ i, c {i} = 1) ∧
      (∀ S : Finset (Fin 10), 5 ≤ S.card → c S = 0) ∧ ∀ x, 0 ≤ qval c x ∧ qval c x ≤ 1 := by
  rintro ⟨c, h0, h1, hd, hq⟩
  have hb := qval_nonneg_le c hq
  have h00 := N00 c h0
  have h10 := N10 c h0 h1
  have h01 := N01 c h0 h1
  have b00 := hb 0 0
  have b01 := hb 0 1
  have b02 := hb 0 2
  have b10 := hb 1 0
  have b11 := hb 1 1
  have b12 := hb 1 2
  have b20 := hb 2 0
  have b21 := hb 2 1
  have b22 := hb 2 2
  have b30 := hb 3 0
  have b31 := hb 3 1
  have b32 := hb 3 2
  have b40 := hb 4 0
  have b41 := hb 4 1
  have b42 := hb 4 2
  have b50 := hb 5 0
  have b51 := hb 5 1
  have b52 := hb 5 2
  have b60 := hb 6 0
  have b61 := hb 6 1
  have b62 := hb 6 2
  have b70 := hb 7 0
  have b71 := hb 7 1
  have b72 := hb 7 2
  have b80 := hb 8 0
  have b81 := hb 8 1
  have b82 := hb 8 2
  simp only [N_eq_Cp, Finset.sum_range_succ, Finset.sum_range_zero, K] at b00 b01 b02 b10 b11 b12 b20 b21 b22 b30 b31 b32 b40 b41 b42 b50 b51 b52 b60 b61 b62 b70 b71 b72 b80 b81 b82 h00 h10 h01
  simp only [show Nat.choose 0 0 = 1 from rfl, show Nat.choose 1 0 = 1 from rfl, show Nat.choose 1 1 = 1 from rfl, show Nat.choose 2 0 = 1 from rfl, show Nat.choose 2 1 = 2 from rfl, show Nat.choose 2 2 = 1 from rfl, show Nat.choose 3 0 = 1 from rfl, show Nat.choose 3 1 = 3 from rfl, show Nat.choose 3 2 = 3 from rfl, show Nat.choose 3 3 = 1 from rfl, show Nat.choose 4 0 = 1 from rfl, show Nat.choose 4 1 = 4 from rfl, show Nat.choose 4 2 = 6 from rfl, show Nat.choose 4 3 = 4 from rfl, show Nat.choose 4 4 = 1 from rfl, show Nat.choose 5 0 = 1 from rfl, show Nat.choose 5 1 = 5 from rfl, show Nat.choose 5 2 = 10 from rfl, show Nat.choose 5 3 = 10 from rfl, show Nat.choose 5 4 = 5 from rfl, show Nat.choose 5 5 = 1 from rfl, show Nat.choose 6 0 = 1 from rfl, show Nat.choose 6 1 = 6 from rfl, show Nat.choose 6 2 = 15 from rfl, show Nat.choose 6 3 = 20 from rfl, show Nat.choose 6 4 = 15 from rfl, show Nat.choose 6 5 = 6 from rfl, show Nat.choose 6 6 = 1 from rfl, show Nat.choose 7 0 = 1 from rfl, show Nat.choose 7 1 = 7 from rfl, show Nat.choose 7 2 = 21 from rfl, show Nat.choose 7 3 = 35 from rfl, show Nat.choose 7 4 = 35 from rfl, show Nat.choose 7 5 = 21 from rfl, show Nat.choose 7 6 = 7 from rfl, show Nat.choose 7 7 = 1 from rfl, show Nat.choose 8 0 = 1 from rfl, show Nat.choose 8 1 = 8 from rfl, show Nat.choose 8 2 = 28 from rfl, show Nat.choose 8 3 = 56 from rfl, show Nat.choose 8 4 = 70 from rfl, show Nat.choose 8 5 = 56 from rfl, show Nat.choose 8 6 = 28 from rfl, show Nat.choose 8 7 = 8 from rfl, show Nat.choose 8 8 = 1 from rfl] at *
  have z := fun p1 p2 h => Cp_high c hd p1 p2 h
  rw [z 5 0 (by norm_num), z 6 0 (by norm_num), z 7 0 (by norm_num), z 8 0 (by norm_num),
    z 4 1 (by norm_num), z 5 1 (by norm_num), z 6 1 (by norm_num), z 7 1 (by norm_num),
    z 8 1 (by norm_num), z 3 2 (by norm_num), z 4 2 (by norm_num), z 5 2 (by norm_num),
    z 6 2 (by norm_num), z 7 2 (by norm_num), z 8 2 (by norm_num)] at *
  norm_num at *
  have key : 3 * Cp c 1 2 = 14 := by linarith
  omega

end OpenProblemsLab.C37
