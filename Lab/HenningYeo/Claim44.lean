import Lab.HenningYeo.Claim43

/-!
# Henning–Yeo Claim 4.4

For every 3-set `S₀ ⊆ S`, the hypergraph `H₃ = (H - {v₁, v₂}) + S₀` is linear but contains a copy
of `F₇` (this combines Claim 4.4 with the paragraph after it).
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

lemma hE_insert_le (f : Finset α) (F : Finset (Finset α)) : hE (insert f F) ≤ hE F + 1 := by
  have hsub : isoEdges (insert f F) ⊆ insert f (isoEdges F) := by
    intro g hg
    by_cases hgf : g = f
    · rw [hgf]; exact Finset.mem_insert_self _ _
    refine Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨?_, fun g' hg' hne => ?_⟩)
    · exact (Finset.mem_insert.1 (isoEdges_subset _ hg)).resolve_left hgf
    · exact (Finset.mem_filter.1 hg).2 g' (Finset.mem_insert_of_mem hg') hne
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

lemma IsL3.insert {F : Finset (Finset α)} (hL : IsL3 F) {f : Finset α} (hf : f.card = 3)
    (hlin : ∀ g ∈ F, (g ∩ f).card ≤ 1) : IsL3 (insert f F) := by
  constructor
  · intro g hg
    rcases Finset.mem_insert.1 hg with rfl | hg
    · exact hf
    · exact hL.card3 g hg
  · intro a ha b hb hab
    rcases Finset.mem_insert.1 ha with ha' | ha' <;> rcases Finset.mem_insert.1 hb with hb' | hb'
    · exact absurd (ha'.trans hb'.symm) hab
    · subst ha'; rw [Finset.inter_comm]; exact hlin b hb'
    · subst hb'; exact hlin a ha'
    · exact hL.linear a ha' b hb' hab

namespace Leaf

variable {E : Finset (Finset α)} {x v₁ v₂ : α} {e₁ e₂ : Finset α}

lemma verts_del12_sub (L : Leaf E x v₁ v₂ e₁ e₂) {w : α} (hw : w ∈ verts (del E {v₁, v₂})) :
    w ∈ verts E ∧ w ≠ x ∧ w ≠ v₁ ∧ w ≠ v₂ :=
  ⟨verts_mono (del_subset _ _) hw, fun h' => L.x_not_verts_del12 (h' ▸ hw),
    fun h' => not_verts_del12 (Or.inl h') hw, fun h' => not_verts_del12 (Or.inr h') hw⟩

lemma S_sub (L : Leaf E x v₁ v₂ e₁ e₂) {w : α} (hw : w ∈ (e₁ ∪ e₂) \ {v₁, v₂}) :
    w ∈ verts E ∧ w ≠ x ∧ w ≠ v₁ ∧ w ≠ v₂ := by
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    not_or] at hw
  refine ⟨?_, ?_, hw.2.1, hw.2.2⟩
  · rcases hw.1 with h' | h'
    · exact subset_verts L.e1E h'
    · exact subset_verts L.e2E h'
  · rintro rfl
    rcases hw.1 with h' | h'
    · exact L.x_not_e1 h'
    · exact L.x_not_e2 h'

/-- `n(H₃) ≤ n - 3` for `H₃ = (H - {v₁, v₂}) + S₀`, `S₀ ⊆ S`. -/
lemma card_verts_H3 (L : Leaf E x v₁ v₂ e₁ e₂) {S₀ : Finset α}
    (hS0 : S₀ ⊆ (e₁ ∪ e₂) \ {v₁, v₂}) :
    (verts (insert S₀ (del E {v₁, v₂}))).card + 3 ≤ (verts E).card := by
  have hsub : verts (insert S₀ (del E {v₁, v₂})) ⊆ verts E \ {x, v₁, v₂} := by
    intro w hw
    rw [verts_insert, Finset.mem_union] at hw
    have : w ∈ verts E ∧ w ≠ x ∧ w ≠ v₁ ∧ w ≠ v₂ := by
      rcases hw with hw | hw
      · exact L.S_sub (hS0 hw)
      · exact L.verts_del12_sub hw
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact this
  have h1 := Finset.card_le_card hsub
  have h2 : ({x, v₁, v₂} : Finset α) ⊆ verts E := subset_verts L.he
  have h3 : ({x, v₁, v₂} : Finset α).card = 3 :=
    Finset.card_eq_three.2 ⟨x, v₁, v₂, L.x1, L.x2, L.v12, rfl⟩
  rw [Finset.card_sdiff_of_subset h2, h3] at h1
  have := Finset.card_le_card h2
  rw [h3] at this
  omega


lemma H3_L3 (L : Leaf E x v₁ v₂ e₁ e₂) (h : MinCex E) {S₀ : Finset α}
    (hS0 : S₀ ⊆ (e₁ ∪ e₂) \ {v₁, v₂}) (hc : S₀.card = 3) : IsL3 (insert S₀ (del E {v₁, v₂})) :=
  (h.L.mono (del_subset _ _)).insert hc fun g hg =>
    (Finset.card_le_card fun w hw => Finset.mem_inter.2
      ⟨(Finset.mem_inter.1 hw).1, hS0 (Finset.mem_inter.1 hw).2⟩).trans (L.claim43 h hg)

/-- **Claim 4.4** (with the paragraph after it): `H₃ = (H - {v₁, v₂}) + S₀` contains `F₇`. -/
lemma claim44 (L : Leaf E x v₁ v₂ e₁ e₂) (h : MinCex E) {S₀ : Finset α}
    (hS0 : S₀ ⊆ (e₁ ∪ e₂) \ {v₁, v₂}) (hc : S₀.card = 3) :
    ¬ F7Free (insert S₀ (del E {v₁, v₂})) := by
  intro hF
  set Hs := del E {v₁, v₂}
  have hm : Hs.card + 3 = E.card := L.card_del12 h.L
  have hn : (verts (insert S₀ Hs)).card + 3 ≤ (verts E).card := L.card_verts_H3 hS0
  have hm3 : (insert S₀ Hs).card ≤ Hs.card + 1 := Finset.card_insert_le _ _
  have hh3 : hE (insert S₀ Hs) ≤ 1 := by
    have := hE_insert_le S₀ Hs; rw [L.claim42 h] at this; exact this
  refine h.no_plus_one (E' := insert S₀ Hs) ?_ (L.H3_L3 h hS0 hc) hF ?_ ?_
  · unfold sz; omega
  · intro T hT
    obtain ⟨s, hs⟩ := hT S₀ (Finset.mem_insert_self _ _)
    rw [Finset.mem_inter] at hs
    have hse : s ∈ e₁ ∪ e₂ := (Finset.mem_sdiff.1 (hS0 hs.1)).1
    obtain ⟨v, hv⟩ := L.cover (fun f hf => hT f (Finset.mem_insert_of_mem hf)) hs.2 hse
    exact ⟨insert v T, Finset.card_insert_le _ _, hv⟩
  · rw [Leaf.wt_eq h]; unfold wt; omega

end Leaf

end OpenProblemsLab.HY
