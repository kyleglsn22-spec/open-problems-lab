import Lab.HenningYeo.Star5

/-!
# Henning–Yeo Claim 8: `h(H - x) = 0` for every vertex `x`
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

namespace MinCex

variable {E : Finset (Finset α)}

/-- An isolated edge of `H - x` has at most `deg x` vertices. -/
lemma card_iso_le_deg (h : MinCex E) {x : α} {w : Finset α} (hw : w ∈ isoEdges (del E {x})) :
    w.card ≤ deg E x := by
  have hwE := del_subset _ _ (isoEdges_subset _ hw)
  have hxw : x ∉ w := fun h' =>
    Finset.disjoint_left.1 (mem_del.1 (isoEdges_subset _ hw)).2 h' (Finset.mem_singleton_self x)
  have hsub : w ⊆ (E.filter (x ∈ ·)).biUnion (fun g => w ∩ g) := by
    intro c hc
    have hcn := h.iso_sub_nbr hw hc
    rw [nbr, Finset.mem_sdiff] at hcn
    obtain ⟨g, hg, hcg⟩ := mem_verts.1 hcn.1
    rw [mem_hit, Finset.disjoint_singleton_right, not_not] at hg
    exact Finset.mem_biUnion.2 ⟨g, Finset.mem_filter.2 hg, Finset.mem_inter.2 ⟨hc, hcg⟩⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∑ g ∈ E.filter (x ∈ ·), (w ∩ g).card ≤ ∑ _g ∈ E.filter (x ∈ ·), 1 :=
    Finset.sum_le_sum fun g hg => by
      have hg' := Finset.mem_filter.1 hg
      exact h.L.linear w hwE g hg'.1 (fun h' => hxw (h' ▸ hg'.2))
  rw [Finset.sum_const, smul_eq_mul, mul_one] at h2
  unfold deg
  omega

/-- **Claim 8**. -/
lemma claim8 (h : MinCex E) (x : α) : hE (del E {x}) = 0 := by
  by_contra h0
  obtain ⟨w, hw⟩ : (isoEdges (del E {x})).Nonempty := Finset.card_pos.1 (Nat.pos_of_ne_zero h0)
  have hc := h.card_iso_le_deg hw
  rw [h.L.card3 w (del_subset _ _ (isoEdges_subset _ hw))] at hc
  have h3 : deg E x = 3 := by have := h.claim5 x; omega
  obtain ⟨u, v, S, -, hdu⟩ := h.star_of_iso h3 hw
  have := S.claim7 h 0
  rw [hdu 0] at this
  omega

end MinCex

end OpenProblemsLab.HY
