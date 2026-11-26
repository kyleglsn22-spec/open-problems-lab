import Lab.HenningYeo.Claim44

/-!
# Copies of `F₇`: lines `ln g k` and facts about the template
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-- Line `k` of the copy of `F₇` given by `g`. -/
def ln (g : Fin 7 → α) (k : Fin 5) : Finset α := (F7L k).image g

section
variable {g : Fin 7 → α} (hg : Function.Injective g)
include hg

lemma mem_ln {i : Fin 7} {k : Fin 5} : g i ∈ ln g k ↔ i ∈ F7L k := by
  simp [ln, hg.eq_iff]

lemma ln_inj {k k' : Fin 5} : ln g k = ln g k' ↔ k = k' :=
  ⟨fun h => F7L_injective (Finset.image_injective hg h), fun h => h ▸ rfl⟩

lemma ln_disj {k k' : Fin 5} : Disjoint (ln g k) (ln g k') ↔ Disjoint (F7L k) (F7L k') :=
  Finset.disjoint_image hg

lemma ln_card (k : Fin 5) : (ln g k).card = 3 := by
  rw [ln, Finset.card_image_of_injective _ hg]; revert k; decide

end

lemma mem_ln_iff {g : Fin 7 → α} {u : α} {k : Fin 5} : u ∈ ln g k ↔ ∃ i ∈ F7L k, g i = u := by
  simp [ln]

/-- A vertex of an edge that meets another edge lies in no isolated edge. -/
lemma not_mem_iso_of_meet {G : Finset (Finset α)} {f f' : Finset α} (hf : f ∈ G) (hf' : f' ∈ G)
    (hne : f ≠ f') (hmeet : ¬ Disjoint f f') {u : α} (hu : u ∈ f) :
    ∀ e ∈ isoEdges G, u ∉ e := by
  intro e he hue
  by_cases hef : e = f
  · subst hef; exact hmeet ((Finset.mem_filter.1 he).2 f' hf' (Ne.symm hne))
  · exact Finset.disjoint_left.1 ((Finset.mem_filter.1 he).2 f hf (Ne.symm hef)) hue hu

/-! ### Facts about the template, by `decide` -/

/-- Each vertex other than `i` (`i` not the centre) lies on a line avoiding `i` that meets another
line avoiding `i`. -/
lemma F7_cov : ∀ i : Fin 7, i ≠ 0 → ∀ j : Fin 7, j ≠ i → ∃ k k' : Fin 5, k ≠ k' ∧ i ∉ F7L k ∧
    i ∉ F7L k' ∧ j ∈ F7L k ∧ ¬ Disjoint (F7L k) (F7L k') := by decide +kernel

/-- Every vertex other than the centre lies on a line through the centre. -/
lemma F7_centre_line : ∀ i : Fin 7, ∃ k : Fin 5, 0 ∈ F7L k ∧ i ∈ F7L k := by decide +kernel

/-- Each line meets another line. -/
lemma F7_meet : ∀ l : Fin 5, ∃ k : Fin 5, k ≠ l ∧ ¬ Disjoint (F7L k) (F7L l) := by decide +kernel

/-- A non-centre vertex lies on exactly two lines. -/
lemma F7_two_lines : ∀ i : Fin 7, i ≠ 0 → ∀ k k' k'' : Fin 5, i ∈ F7L k → i ∈ F7L k' →
    i ∈ F7L k'' → k = k' ∨ k = k'' ∨ k' = k'' := by decide +kernel

/-- The centre lies on lines `0, 1, 2` only; the others are lines `3, 4`. -/
lemma F7_centre_iff : ∀ k : Fin 5, 0 ∈ F7L k ↔ k = 0 ∨ k = 1 ∨ k = 2 := by decide +kernel

lemma F7_noncentre : ∀ i : Fin 7, i ≠ 0 → i ∈ F7L 3 ∨ i ∈ F7L 4 := by decide +kernel

lemma F7_off : ∀ l : Fin 5, ∀ i : Fin 7, i ∉ F7L l →
    ∃ k, i ∈ F7L k ∧ ¬ Disjoint (F7L k) (F7L l) := by decide +kernel

/-- Case `|S| = 4` of Claim 4.5. -/
lemma F7_caseB : ∀ l : Fin 5, ∀ i ∈ F7L l, ∃ k₁ k₂ : Fin 5, ∃ i' y : Fin 7, k₁ ≠ l ∧ k₂ ≠ l ∧
    i ∈ F7L k₁ ∧ i' ∈ F7L l ∧ i' ≠ i ∧ i' ∈ F7L k₂ ∧ y ∈ F7L k₁ ∧ y ∈ F7L k₂ := by decide +kernel

end OpenProblemsLab.HY
