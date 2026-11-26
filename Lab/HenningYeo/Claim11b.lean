import Lab.HenningYeo.Claim11a

/-!
# Henning–Yeo Claim 11, part 2: Claim 11.1

Let `S` be three pairwise non-adjacent neighbours of `x` in a 3-regular minimal counterexample.
Then `H - S` loses exactly the vertices `S ∪ {x}` and has exactly two isolated edges `e₁, e₂`.
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-- The situation of Claim 11, after Claim 11.1. -/
structure C11 (E : Finset (Finset α)) (x : α) (S : Finset α) (e₁ e₂ : Finset α) : Prop where
  h : MinCex E
  reg : ∀ v ∈ verts E, deg E v = 3
  hS : S ⊆ nbr E {x}
  card : S.card = 3
  ind : ∀ f ∈ E, (f ∩ S).card ≤ 1
  iso : isoEdges (del E S) = {e₁, e₂}
  ne : e₁ ≠ e₂
  gone : verts E \ verts (del E S) = insert x S
  U : ∑ v ∈ verts (del E S), deg (hit E S) v = 15

variable {E : Finset (Finset α)}

lemma mem_nbr_singleton {s c : α} : c ∈ nbr E {s} ↔ c ≠ s ∧ ∃ f ∈ E, s ∈ f ∧ c ∈ f := by
  constructor
  · intro hc
    rw [nbr, Finset.mem_sdiff, Finset.mem_singleton] at hc
    obtain ⟨f, hf, hcf⟩ := mem_verts.1 hc.1
    rw [mem_hit, Finset.disjoint_singleton_right, not_not] at hf
    exact ⟨hc.2, f, hf.1, hf.2, hcf⟩
  · rintro ⟨hcs, f, hf, hsf, hcf⟩
    exact MinCex.mem_nbr_of hf hsf hcf hcs

/-- Every edge at `x` contains a vertex of `S`. -/
lemma edges_at_x {x : α} (hx : deg E x = 3) {S : Finset α} (hS : S ⊆ nbr E {x})
    (hcard : S.card = 3) (hind : ∀ f ∈ E, (f ∩ S).card ≤ 1) :
    ∀ f ∈ E, x ∈ f → ¬ Disjoint f S := by
  have hpick : ∀ s ∈ S, ∃ f, f ∈ E.filter (x ∈ ·) ∧ s ∈ f := fun s hs => by
    obtain ⟨-, f, hf, hxf, hsf⟩ := mem_nbr_singleton.1 (hS hs)
    exact ⟨f, Finset.mem_filter.2 ⟨hf, hxf⟩, hsf⟩
  choose! φ hφ hsφ using hpick
  have hinj : Set.InjOn φ S := by
    intro s hs s' hs' heq
    by_contra hne
    have hf := (Finset.mem_filter.1 (hφ s hs)).1
    have : ({s, s'} : Finset α) ⊆ φ s ∩ S := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_inter.2 ⟨hsφ v hs, hs⟩
      · exact Finset.mem_inter.2 ⟨heq ▸ hsφ v hs', hs'⟩
    have := (Finset.card_le_card this).trans (hind _ hf)
    rw [Finset.card_pair hne] at this
    omega
  have himg : S.image φ = E.filter (x ∈ ·) := by
    apply Finset.eq_of_subset_of_card_le
    · intro g hg; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hg; exact hφ s hs
    · rw [Finset.card_image_of_injOn hinj, hcard]; unfold deg at hx; omega
  intro f hf hxf
  have : f ∈ S.image φ := himg ▸ Finset.mem_filter.2 ⟨hf, hxf⟩
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 this
  exact Finset.not_disjoint_iff.2 ⟨s, hsφ s hs, hs⟩

/-- **Claim 11.1** (with its consequences). -/
lemma C11.exists (h : MinCex E) (hreg : ∀ v ∈ verts E, deg E v = 3) {x : α} {S : Finset α}
    (hS : S ⊆ nbr E {x}) (hcard : S.card = 3) (hind : ∀ f ∈ E, (f ∩ S).card ≤ 1) :
    ∃ e₁ e₂, C11 E x S e₁ e₂ := by
  have hL := h.L
  have hSE : S ⊆ verts E := fun s hs => by
    obtain ⟨-, f, hf, -, hsf⟩ := mem_nbr_singleton.1 (hS hs)
    exact subset_verts hf hsf
  have hxS : x ∉ S := fun hx => by
    have := hS hx; rw [nbr, Finset.mem_sdiff] at this; exact this.2 (Finset.mem_singleton_self x)
  obtain ⟨s0, hs0⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  have hxE : x ∈ verts E := by
    obtain ⟨-, f, hf, hxf, -⟩ := mem_nbr_singleton.1 (hS hs0)
    exact subset_verts hf hxf
  have hx3 := hreg x hxE
  have hxgone : x ∉ verts (del E S) :=
    not_mem_verts_del (edges_at_x hx3 hS hcard hind)
  have hsub : insert x S ⊆ verts E \ verts (del E S) := by
    intro v hv
    rw [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact Finset.mem_sdiff.2 ⟨hxE, hxgone⟩
    · exact Finset.mem_sdiff.2 ⟨hSE hv, fun h' =>
        Finset.disjoint_left.1 (verts_del_disjoint E S) h' hv⟩
  have hc4 : (insert x S).card = 4 := by rw [Finset.card_insert_of_notMem hxS, hcard]
  have hR4 := Finset.card_le_card hsub
  have hhit : (hit E S).card = 9 := by
    rw [card_hit_of_ind hind, Finset.sum_congr rfl (g := fun _ => 3) (fun s hs => hreg s (hSE hs)),
      Finset.sum_const, hcard]
    rfl
  have hbal := sum_deg_hit hL hreg S
  have h6 := six_hE_le hL hreg S
  have hng : ¬ (17 * S.card + hE (del E S) ≤
      4 * (verts E \ verts (del E S)).card + 4 * (hit E S).card) := fun hineq => by
    obtain ⟨e, he⟩ : (hit E S).Nonempty := Finset.card_pos.1 (by omega)
    exact h.no_good_del (hE (del E S)) Finset.sdiff_subset
      (Finset.disjoint_left.2 fun v hv => (Finset.mem_sdiff.1 hv).2) subset_rfl ⟨e, he⟩ le_rfl
      hineq
  rw [hcard, hhit] at hng
  rw [hhit] at hbal
  have hR : (verts E \ verts (del E S)).card = 4 := by omega
  have hh2 : hE (del E S) = 2 := by omega
  obtain ⟨e₁, e₂, hne, heq⟩ := Finset.card_eq_two.1 hh2
  exact ⟨e₁, e₂, h, hreg, hS, hcard, hind, heq, hne,
    (Finset.eq_of_subset_of_card_le hsub (by omega)).symm, by omega⟩

end OpenProblemsLab.HY
