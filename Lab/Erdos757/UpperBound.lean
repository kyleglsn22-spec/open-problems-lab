import FormalConjectures.ErdosProblems.«757»

/-!
# Erdős #757: the upper bound `sSup {c | IsAdmissible c} < 3 / 5`

Proof: the 12-element integer set
`A₀ = {0, 92, 95, 107, 119, 184, 188, 190, 238, 261, 284, 384}`
(published by Suresh Kannan, 2026; re-checked by `explorer/erdos757/check_n12.py`)
is a (4,5)-set whose largest Sidon subset has 7 elements. So every admissible `c`
satisfies `12 c ≤ 7`, hence the supremum is at most `7/12 < 3/5`.

The two finite facts about `A₀` are checked by the kernel with `decide +kernel`
(no `native_decide`, so no extra axioms).
-/

open scoped Pointwise

namespace OpenProblemsLab.E757

open _root_.Erdos757

/-- The witness set, as integers. -/
def A₀ : Finset ℤ := {0, 92, 95, 107, 119, 184, 188, 190, 238, 261, 284, 384}

lemma card_A₀ : A₀.card = 12 := by decide +kernel

/-- Every 4-element subset of `A₀` has at least 11 elements in its difference set. -/
lemma A₀_45 : ∀ B ∈ A₀.powersetCard 4, 11 ≤ (B - B).card := by decide +kernel

/-- All ten 3-term arithmetic progressions `a < c < b`, `a + b = c + c`, inside `A₀`.
(Found by brute force; `A₀_hit` below is what the proof actually relies on.) -/
def AP : List (ℤ × ℤ × ℤ) :=
  [(0, 184, 92), (95, 119, 107), (238, 284, 261), (0, 190, 95), (92, 284, 188),
   (119, 261, 190), (92, 384, 238), (184, 384, 284), (107, 261, 184), (0, 238, 119)]

lemma AP_spec : ∀ t ∈ AP, t.1 + t.2.1 = t.2.2 + t.2.2 ∧ t.1 < t.2.2 := by decide +kernel

/-- Every 8-element subset of `A₀` contains one of the progressions in `AP`.
(Checking this hitting property is far cheaper for the kernel than deciding `IsSidon`
directly, which needed about 12 GB to replay.) -/
lemma A₀_hit : ∀ B ∈ A₀.powersetCard 8, ∃ t ∈ AP, t.1 ∈ B ∧ t.2.1 ∈ B ∧ t.2.2 ∈ B := by
  decide +kernel

/-- No 8-element subset of `A₀` is a Sidon set. -/
lemma A₀_no_sidon8 : ∀ B ∈ A₀.powersetCard 8, ¬ IsSidon (B : Set ℤ) := by
  intro B hB hSid
  obtain ⟨⟨a, b, c⟩, ht, ha, hb, hc⟩ := A₀_hit B hB
  obtain ⟨hsum, hlt⟩ := AP_spec _ ht
  rcases hSid a ha c hc b hb c hc hsum with ⟨h, -⟩ | ⟨h, -⟩ <;> simp at hlt <;> omega

/-- The cast `ℤ → ℝ` as an additive monoid hom. -/
abbrev ι : ℤ →+ ℝ := Int.castAddHom ℝ

lemma ι_injective : Function.Injective ι := Int.cast_injective

/-- The witness set inside `ℝ`. -/
def A : Set ℝ := ι '' (A₀ : Set ℤ)

lemma A_finite : A.Finite := (A₀.finite_toSet).image _

lemma ncard_A : A.ncard = 12 := by
  rw [A, Set.ncard_image_of_injective _ ι_injective, Set.ncard_coe_finset, card_A₀]

/-- A subset of `A` is the image of a subset of `A₀`. -/
lemma exists_preimage {B : Set ℝ} (hB : B ⊆ A) :
    ∃ B₀ : Finset ℤ, B₀ ⊆ A₀ ∧ B = ι '' (B₀ : Set ℤ) := by
  classical
  refine ⟨A₀.filter (fun z => ι z ∈ B), Finset.filter_subset _ _, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := hB hx
    exact ⟨z, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_coe.1 hz, hx⟩), rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 hz)).2

lemma is45 : ∀ B ⊆ A, B.ncard = 4 → 11 ≤ (B - B).ncard := by
  intro B hB hcard
  obtain ⟨B₀, hB₀, rfl⟩ := exists_preimage hB
  rw [Set.ncard_image_of_injective _ ι_injective, Set.ncard_coe_finset] at hcard
  have hmem : B₀ ∈ A₀.powersetCard 4 := Finset.mem_powersetCard.2 ⟨hB₀, hcard⟩
  have key := A₀_45 B₀ hmem
  rw [← Set.image_sub, Set.ncard_image_of_injective _ ι_injective, ← Finset.coe_sub,
    Set.ncard_coe_finset]
  exact key

lemma isSidon_preimage {S₀ : Finset ℤ} (h : IsSidon (ι '' (S₀ : Set ℤ))) :
    IsSidon (S₀ : Set ℤ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  have := h (ι i₁) ⟨i₁, hi₁, rfl⟩ (ι j₁) ⟨j₁, hj₁, rfl⟩ (ι i₂) ⟨i₂, hi₂, rfl⟩
    (ι j₂) ⟨j₂, hj₂, rfl⟩ (by rw [← map_add, ← map_add, hsum])
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨ι_injective h1, ι_injective h2⟩
  · exact Or.inr ⟨ι_injective h1, ι_injective h2⟩

/-- Every Sidon subset of `A` has at most 7 elements. -/
lemma sidon_le_seven {S : Set ℝ} (hS : S ⊆ A) (hSid : IsSidon S) : S.ncard ≤ 7 := by
  obtain ⟨S₀, hS₀, rfl⟩ := exists_preimage hS
  rw [Set.ncard_image_of_injective _ ι_injective, Set.ncard_coe_finset]
  have hSid₀ := isSidon_preimage hSid
  by_contra hlt
  push Not at hlt
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (show 8 ≤ S₀.card by omega)
  exact A₀_no_sidon8 T (Finset.mem_powersetCard.2 ⟨hTS.trans hS₀, hTcard⟩)
    (fun i₁ h₁ j₁ h₂ i₂ h₃ j₂ h₄ => hSid₀ i₁ (hTS h₁) j₁ (hTS h₂) i₂ (hTS h₃) j₂ (hTS h₄))

lemma admissible_le {c : ℝ} (hc : IsAdmissible c) : c ≤ 7 / 12 := by
  obtain ⟨S, hSA, hSid, hle⟩ := hc A_finite is45
  have h7 : (S.ncard : ℝ) ≤ 7 := by exact_mod_cast sidon_le_seven hSA hSid
  rw [ncard_A] at hle
  push_cast at hle
  linarith

/-- **Erdős #757, upper bound** (Gyárfás–Lehel 1995 state `< 3/5`; this proof gives `≤ 7/12`). -/
theorem upperBound : sSup {c : ℝ | IsAdmissible c} < 3 / 5 := by
  have h : sSup {c : ℝ | IsAdmissible c} ≤ 7 / 12 :=
    Real.sSup_le (fun c hc => admissible_le hc) (by norm_num)
  linarith

/-- The same statement as `Erdos757.erdos_757.variants.upperBound` in formal-conjectures. -/
theorem erdos_757_upperBound {_A : Set ℝ} : sSup {c | IsAdmissible c} < 3 / (5 : ℝ) := by
  simpa using upperBound

end OpenProblemsLab.E757
