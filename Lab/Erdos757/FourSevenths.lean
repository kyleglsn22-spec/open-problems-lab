import FormalConjectures.ErdosProblems.«757»

/-!
# Erdős #757: the best known upper bound `sSup {c | IsAdmissible c} ≤ 4 / 7`

Proof: the 14-element integer set
`A₀ = {0, 136, 200, 243, 246, 249, 272, 286, 298, 323, 400, 528, 596, 1056}`
from Ma–Tang (arXiv:2602.23282) is a (4,5)-set whose largest Sidon subset has 8 elements.
So every admissible `c` satisfies `14 c ≤ 8`, hence the supremum is at most `4/7`.

Same method as `Lab/Erdos757/UpperBound.lean` (claim 757-1). The finite facts about `A₀`
are checked by the kernel with `decide +kernel` (no `native_decide`, so no extra axioms).
-/

open scoped Pointwise

namespace OpenProblemsLab.E757.FourSevenths

open _root_.Erdos757

/-- The witness set, as integers (Ma–Tang, arXiv:2602.23282). -/
def A₀ : Finset ℤ := {0, 136, 200, 243, 246, 249, 272, 286, 298, 323, 400, 528, 596, 1056}

lemma card_A₀ : A₀.card = 14 := by decide +kernel

/-- The witness without its two smallest elements; used to split the finite checks into
smaller pieces, which keeps the kernel's memory use down when the proof is re-checked. -/
def A₂ : Finset ℤ := {200, 243, 246, 249, 272, 286, 298, 323, 400, 528, 596, 1056}

lemma A₀_eq : A₀ = insert 0 (insert 136 A₂) := by decide +kernel

lemma not_mem_136 : (136 : ℤ) ∉ A₂ := by decide +kernel

lemma not_mem_0 : (0 : ℤ) ∉ insert 136 A₂ := by decide +kernel

/-- Splitting a check over `k+1`-subsets of `insert a s` into subsets avoiding `a` and
subsets containing `a`. -/
lemma forall_powersetCard_insert {P : Finset ℤ → Prop} {a : ℤ} {s : Finset ℤ} (ha : a ∉ s)
    {k : ℕ} (h₁ : ∀ B ∈ s.powersetCard (k + 1), P B)
    (h₂ : ∀ B ∈ s.powersetCard k, P (insert a B)) :
    ∀ B ∈ (insert a s).powersetCard (k + 1), P B := by
  intro B hB
  rw [Finset.powersetCard_succ_insert ha, Finset.mem_union, Finset.mem_image] at hB
  rcases hB with hB | ⟨C, hC, rfl⟩
  · exact h₁ B hB
  · exact h₂ C hC

lemma A₂_45 : ∀ B ∈ A₂.powersetCard 4, 11 ≤ (B - B).card := by decide +kernel

lemma A₂_45_136 : ∀ B ∈ A₂.powersetCard 3, 11 ≤ (insert 136 B - insert 136 B).card := by
  decide +kernel

lemma A₁_45_0 : ∀ B ∈ (insert 136 A₂).powersetCard 3, 11 ≤ (insert 0 B - insert 0 B).card := by
  decide +kernel

/-- Every 4-element subset of `A₀` has at least 11 elements in its difference set. -/
lemma A₀_45 : ∀ B ∈ A₀.powersetCard 4, 11 ≤ (B - B).card := by
  rw [A₀_eq]
  exact forall_powersetCard_insert (P := fun B => 11 ≤ (B - B).card) not_mem_0
    (forall_powersetCard_insert (P := fun B => 11 ≤ (B - B).card) not_mem_136 A₂_45 A₂_45_136)
    A₁_45_0

/-- All twelve 3-term arithmetic progressions `a < c < b`, `a + b = c + c`, inside `A₀`. -/
def AP : List (ℤ × ℤ × ℤ) :=
  [(0, 272, 136), (0, 400, 200), (0, 596, 298), (0, 1056, 528), (136, 1056, 596),
   (200, 286, 243), (200, 298, 249), (243, 249, 246), (246, 298, 272), (246, 400, 323),
   (249, 323, 286), (272, 528, 400)]

lemma AP_spec : ∀ t ∈ AP, t.1 + t.2.1 = t.2.2 + t.2.2 ∧ t.1 < t.2.2 := by decide +kernel

/-- "`B` contains one of the progressions in `AP`." -/
def Hits (B : Finset ℤ) : Prop := ∃ t ∈ AP, t.1 ∈ B ∧ t.2.1 ∈ B ∧ t.2.2 ∈ B

instance : DecidablePred Hits := fun B => by unfold Hits; infer_instance

lemma A₂_hit : ∀ B ∈ A₂.powersetCard 9, Hits B := by decide +kernel

lemma A₂_hit_136 : ∀ B ∈ A₂.powersetCard 8, Hits (insert 136 B) := by decide +kernel

lemma A₂_hit_0 : ∀ B ∈ A₂.powersetCard 8, Hits (insert 0 B) := by decide +kernel

lemma A₂_hit_0_136 : ∀ B ∈ A₂.powersetCard 7, Hits (insert 0 (insert 136 B)) := by
  decide +kernel

/-- Every 9-element subset of `A₀` contains one of the progressions in `AP`.
(Checking this hitting property is far cheaper for the kernel than deciding `IsSidon`.) -/
lemma A₀_hit : ∀ B ∈ A₀.powersetCard 9, Hits B := by
  rw [A₀_eq]
  exact forall_powersetCard_insert not_mem_0
    (forall_powersetCard_insert not_mem_136 A₂_hit A₂_hit_136)
    (forall_powersetCard_insert (P := fun B => Hits (insert 0 B)) not_mem_136 A₂_hit_0
      A₂_hit_0_136)

/-- No 9-element subset of `A₀` is a Sidon set. -/
lemma A₀_no_sidon9 : ∀ B ∈ A₀.powersetCard 9, ¬ IsSidon (B : Set ℤ) := by
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

lemma ncard_A : A.ncard = 14 := by
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

/-- Every Sidon subset of `A` has at most 8 elements. -/
lemma sidon_le_eight {S : Set ℝ} (hS : S ⊆ A) (hSid : IsSidon S) : S.ncard ≤ 8 := by
  obtain ⟨S₀, hS₀, rfl⟩ := exists_preimage hS
  rw [Set.ncard_image_of_injective _ ι_injective, Set.ncard_coe_finset]
  have hSid₀ := isSidon_preimage hSid
  by_contra hlt
  push Not at hlt
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (show 9 ≤ S₀.card by omega)
  exact A₀_no_sidon9 T (Finset.mem_powersetCard.2 ⟨hTS.trans hS₀, hTcard⟩)
    (fun i₁ h₁ j₁ h₂ i₂ h₃ j₂ h₄ => hSid₀ i₁ (hTS h₁) j₁ (hTS h₂) i₂ (hTS h₃) j₂ (hTS h₄))

lemma admissible_le {c : ℝ} (hc : IsAdmissible c) : c ≤ 4 / 7 := by
  obtain ⟨S, hSA, hSid, hle⟩ := hc A_finite is45
  have h8 : (S.ncard : ℝ) ≤ 8 := by exact_mod_cast sidon_le_eight hSA hSid
  rw [ncard_A] at hle
  push_cast at hle
  linarith

/-- **Erdős #757, best known upper bound** (Ma–Tang, arXiv:2602.23282): `sSup ≤ 4/7`. -/
theorem sSup_le_four_sevenths : sSup {c : ℝ | IsAdmissible c} ≤ 4 / 7 :=
  Real.sSup_le (fun c hc => admissible_le hc) (by norm_num)

end OpenProblemsLab.E757.FourSevenths
