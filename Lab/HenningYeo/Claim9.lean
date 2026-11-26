import Lab.HenningYeo.Claim8
import Lab.HenningYeo.Cubic

/-!
# Henning–Yeo Claim 9: the minimal counterexample is not 2-regular

The dual of a 2-regular linear 3-uniform hypergraph is a cubic graph; a large matching in it
(`Cubic.cubic_matching`) gives a small transversal.
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-- The dual graph: edges of `E`, adjacent when they meet. -/
def dualG (E : Finset (Finset α)) : SimpleGraph {e // e ∈ E} where
  Adj e f := e ≠ f ∧ ¬ Disjoint e.1 f.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun h' => h.2 h'.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

namespace MinCex

variable {E : Finset (Finset α)}

lemma claim9 (h : MinCex E) : ∃ v ∈ verts E, deg E v = 3 := by
  classical
  by_contra hno
  push Not at hno
  have h2 : ∀ v ∈ verts E, deg E v = 2 := fun v hv =>
    (h.deg_two_or_three hv).resolve_right (hno v hv)
  have hL := h.L
  -- the other edge at a vertex
  have hoth : ∀ e : {e // e ∈ E}, ∀ a ∈ e.1, ∃ f : {e // e ∈ E}, f ≠ e ∧ a ∈ f.1 ∧
      ∀ g ∈ E, a ∈ g → g = e.1 ∨ g = f.1 := fun e a ha => by
    obtain ⟨f, hf, hne, haf, hall⟩ := exists_other_edge e.2 ha (h2 a (subset_verts e.2 ha))
    exact ⟨⟨f, hf⟩, fun h' => hne (congrArg Subtype.val h'), haf, hall⟩
  let K := dualG E
  have h3 : ∀ e, K.degree e = 3 := by
    intro e
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hL.card3 e.1 e.2]
    symm
    refine Finset.card_bij (fun a ha => (hoth e a ha).choose) ?_ ?_ ?_
    · intro a ha
      obtain ⟨hne, haf, -⟩ := (hoth e a ha).choose_spec
      rw [SimpleGraph.mem_neighborFinset]
      exact ⟨hne.symm, Finset.not_disjoint_iff.2 ⟨a, ha, haf⟩⟩
    · intro a ha a' ha' heq
      obtain ⟨hne, haf, -⟩ := (hoth e a ha).choose_spec
      obtain ⟨-, haf', -⟩ := (hoth e a' ha').choose_spec
      rw [← heq] at haf'
      by_contra hab
      exact hne (Subtype.ext (hL.eq_of_two (hoth e a ha).choose.2 e.2 hab haf haf' ha ha'))
    · intro f hf
      rw [SimpleGraph.mem_neighborFinset] at hf
      obtain ⟨a, hae, haf⟩ := Finset.not_disjoint_iff.1 hf.2
      refine ⟨a, hae, ?_⟩
      obtain ⟨hne, -, hall⟩ := (hoth e a hae).choose_spec
      rcases hall f.1 f.2 haf with h' | h'
      · exact absurd (Subtype.ext h').symm hf.1
      · exact (Subtype.ext h').symm
  obtain ⟨M, hM, hcard⟩ := Cubic.cubic_matching K h3
  -- the transversal
  have hpick : ∀ e : {e // e ∈ E}, ∃ a, a ∈ e.1 ∧ ∀ f, M.Adj e f → a ∈ f.1 := by
    intro e
    by_cases he : e ∈ M.verts
    · obtain ⟨f, hf, -⟩ := hM he
      obtain ⟨a, hae, haf⟩ := Finset.not_disjoint_iff.1 (M.adj_sub hf).2
      refine ⟨a, hae, fun f' hf' => ?_⟩
      rw [hM.eq_of_adj_left hf' hf]; exact haf
    · obtain ⟨a, ha⟩ : e.1.Nonempty := by rw [← Finset.card_pos, hL.card3 e.1 e.2]; norm_num
      exact ⟨a, ha, fun f hf => absurd (M.edge_vert hf) he⟩
  choose φ hφe hφf using hpick
  have hφ : ∀ e f, M.Adj e f → φ e = φ f := by
    intro e f hef
    have hne : e.1 ≠ f.1 := fun h' => (M.adj_sub hef).1 (Subtype.ext h')
    exact Finset.card_le_one.1 (hL.linear e.1 e.2 f.1 f.2 hne) _
      (Finset.mem_inter.2 ⟨hφe e, hφf e f hef⟩)
      _ (Finset.mem_inter.2 ⟨hφf f e (M.adj_symm hef), hφe f⟩)
  set T := (Finset.univ : Finset {e // e ∈ E}).image φ with hT
  set Mv := (Finset.univ : Finset {e // e ∈ E}).filter (· ∈ M.verts) with hMv
  set Un := (Finset.univ : Finset {e // e ∈ E}).filter (· ∉ M.verts) with hUn
  have hTsub : T ⊆ Un.image φ ∪ Mv.image φ := by
    intro y hy
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hy
    by_cases he : e ∈ M.verts
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (by simp [hMv, he]))
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (by simp [hUn, he]))
  have hMv2 : 2 * (Mv.image φ).card ≤ Mv.card := by
    refine Finset.mul_card_image_le_card Mv 2 fun y hy => ?_
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hy
    have he' : e ∈ M.verts := (Finset.mem_filter.1 he).2
    obtain ⟨f, hf, -⟩ := hM he'
    have hsub : ({e, f} : Finset {e // e ∈ E}) ⊆ Mv.filter (fun a => φ a = φ e) := by
      intro g hg
      simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · exact Finset.mem_filter.2 ⟨he, rfl⟩
      · exact Finset.mem_filter.2 ⟨by simp [hMv, M.edge_vert (M.adj_symm hf)], (hφ _ _ hf).symm⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair (M.adj_sub hf).1] at this
  have hsplit : Un.card + Mv.card = E.card := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset {e // e ∈ E}))
      (fun a => a ∈ M.verts)
    rw [Finset.card_univ, Fintype.card_coe] at this
    rw [hUn, hMv]; omega
  have hMvn : M.verts.ncard = Mv.card := by
    rw [← Set.ncard_coe_finset]; congr 1; ext; simp [hMv]
  rw [Fintype.card_coe, hMvn] at hcard
  have hTc := (Finset.card_le_card hTsub).trans (Finset.card_union_le _ _)
  have hUc := Finset.card_image_le (s := Un) (f := φ)
  -- counting
  have hsum := sum_deg h.L.card3
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul] at hsum
  have hne : 0 < E.card := Finset.card_pos.2 h.nonempty
  have hw := h.wt_eq
  refine h.not_good ⟨T, fun e he => ⟨φ ⟨e, he⟩, Finset.mem_inter.2 ⟨hφe _,
    Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩⟩, ?_⟩
  omega

end MinCex

end OpenProblemsLab.HY
