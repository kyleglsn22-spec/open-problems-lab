import Lab.HenningYeo.Count

/-!
# Henning–Yeo Theorem 6: Claims 3 and 4 (minimum degree at least 2)
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

lemma deg_eq_one_iff {E : Finset (Finset α)} {v : α} {f : Finset α} (hf : f ∈ E) (hvf : v ∈ f) :
    deg E v = 1 ↔ ∀ g ∈ E, v ∈ g → g = f := by
  constructor
  · intro h g hg hvg; exact eq_of_deg_one h hf hvf hg hvg
  · intro h
    unfold deg
    rw [Finset.card_eq_one]
    refine ⟨f, ?_⟩
    ext g
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun hg => h g hg.1 hg.2, fun hg => hg ▸ ⟨hf, hvf⟩⟩

/-- A vertex of an isolated edge of `H - X` outside `N(X)` has degree 1 in `H`. -/
lemma deg_one_of_iso_del {E : Finset (Finset α)} {X : Finset α} {f : Finset α}
    (hf : f ∈ isoEdges (del E X)) {v : α} (hvf : v ∈ f) (hvn : v ∉ nbr E X) : deg E v = 1 := by
  have hfd := isoEdges_subset _ hf
  have hfE := del_subset E X hfd
  refine (deg_eq_one_iff hfE hvf).2 fun g hg hvg => ?_
  by_cases hgX : Disjoint g X
  · by_contra hgf
    exact Finset.disjoint_left.1 ((Finset.mem_filter.1 hf).2 g (mem_del.2 ⟨hg, hgX⟩) hgf) hvf hvg
  · exfalso; apply hvn
    refine Finset.mem_sdiff.2 ⟨mem_verts.2 ⟨g, mem_hit.2 ⟨hg, hgX⟩, hvg⟩, fun hvX => ?_⟩
    exact Finset.disjoint_left.1 (mem_del.1 hfd).2 hvf hvX


/-- A vertex of degree 2 in `e` lies in exactly one other edge. -/
lemma exists_other_edge {E : Finset (Finset α)} {v : α} {e : Finset α} (he : e ∈ E) (hve : v ∈ e)
    (hv : deg E v = 2) : ∃ f ∈ E, f ≠ e ∧ v ∈ f ∧ ∀ g ∈ E, v ∈ g → g = e ∨ g = f := by
  unfold deg at hv
  obtain ⟨a, b, hab, hab'⟩ := Finset.card_eq_two.1 hv
  have hmem : ∀ g ∈ E, v ∈ g → g = a ∨ g = b := fun g hg hvg => by
    have : g ∈ E.filter (v ∈ ·) := Finset.mem_filter.2 ⟨hg, hvg⟩
    rw [hab'] at this; simpa using this
  have ha : a ∈ E.filter (v ∈ ·) := by rw [hab']; simp
  have hb : b ∈ E.filter (v ∈ ·) := by rw [hab']; simp
  rw [Finset.mem_filter] at ha hb
  rcases hmem e he hve with rfl | rfl
  · exact ⟨b, hb.1, Ne.symm hab, hb.2, hmem⟩
  · exact ⟨a, ha.1, hab, ha.2, fun g hg hvg => (hmem g hg hvg).symm⟩

/-- Linearity: two distinct edges share at most one vertex. -/
lemma IsL3.eq_of_two {E : Finset (Finset α)} (hL : IsL3 E) {e f : Finset α} (he : e ∈ E)
    (hf : f ∈ E) {a b : α} (hab : a ≠ b) (hae : a ∈ e) (hbe : b ∈ e) (haf : a ∈ f) (hbf : b ∈ f) :
    e = f := by
  by_contra hne
  have := hL.linear e he f hf hne
  have : ({a, b} : Finset α) ⊆ e ∩ f := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp_all
  have := Finset.card_le_card this
  rw [Finset.card_pair hab] at this
  omega

namespace MinCex

variable {E : Finset (Finset α)}

/-- Claim 2 restated: no edge has two vertices of degree 1. -/
lemma two_leaves_false (h : MinCex E) {f : Finset α} (hf : f ∈ E) {y z : α} (hyf : y ∈ f)
    (hzf : z ∈ f) (hyz : y ≠ z) (hy : deg E y = 1) (hz : deg E z = 1) : False := by
  have hcard := h.L.card3 f hf
  obtain ⟨x, hx⟩ : ∃ x, f = {x, y, z} ∧ x ≠ y ∧ x ≠ z := by
    have h2 : ({y, z} : Finset α) ⊆ f := by
      intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> assumption
    have : (f \ {y, z}).card = 1 := by
      rw [Finset.card_sdiff_of_subset h2, hcard, Finset.card_pair hyz]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 this
    have hxf : x ∈ f \ {y, z} := hx ▸ Finset.mem_singleton_self x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hxf
    refine ⟨x, ?_, hxf.2.1, hxf.2.2⟩
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      by_cases hv' : v ∈ ({y, z} : Finset α)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv' ⊢; tauto
      · have : v ∈ f \ {y, z} := Finset.mem_sdiff.2 ⟨hv, hv'⟩
        rw [hx, Finset.mem_singleton] at this; simp [this]
    · rw [hcard, Finset.card_eq_three.2 ⟨x, y, z, hxf.2.1, hxf.2.2, hyz, rfl⟩]
  obtain ⟨rfl, hxy, hxz⟩ := hx
  exact h.no_two_leaves hf hxy hxz hyz hy hz

/-- Every isolated edge of `H - X` meets `N(X)` in at least two vertices. -/
lemma two_le_inter_nbr (h : MinCex E) {X : Finset α} {f : Finset α}
    (hf : f ∈ isoEdges (del E X)) : 2 ≤ (f ∩ nbr E X).card := by
  have hfE := del_subset E X (isoEdges_subset _ hf)
  have hcard := h.L.card3 f hfE
  by_contra hlt
  push Not at hlt
  have h1 : 2 ≤ (f \ nbr E X).card := by
    have := Finset.card_sdiff_add_card_inter f (nbr E X); omega
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.1 (show 1 < (f \ nbr E X).card by omega)
  rw [Finset.mem_sdiff] at hy hz
  exact h.two_leaves_false hfE hy.1 hz.1 hyz (deg_one_of_iso_del hf hy.1 hy.2)
    (deg_one_of_iso_del hf hz.1 hz.2)

/-- Hence `2 h(H - X) ≤ |N(X) ∩ V(H - X)|`. -/
lemma two_mul_hE_del_le (h : MinCex E) (X : Finset α) :
    2 * hE (del E X) ≤ (nbr E X ∩ verts (del E X)).card := by
  refine mul_hE_le _ 2 fun f hf => ?_
  have hfv : f ⊆ verts (del E X) := subset_verts (isoEdges_subset _ hf)
  refine (h.two_le_inter_nbr hf).trans (Finset.card_le_card ?_)
  intro v hv
  rw [Finset.mem_inter] at hv ⊢
  exact ⟨hv.1, Finset.mem_inter.2 ⟨hv.2, hfv hv.1⟩⟩


omit [DecidableEq α] in
lemma mem_of_not_disjoint_singleton {e : Finset α} {v : α} (h : ¬ Disjoint e {v}) : v ∈ e := by
  rwa [Finset.disjoint_singleton_right, not_not] at h

lemma deg_pos_of_mem {E : Finset (Finset α)} {v : α} {e : Finset α} (he : e ∈ E) (hv : v ∈ e) :
    1 ≤ deg E v := Finset.card_pos.2 ⟨e, Finset.mem_filter.2 ⟨he, hv⟩⟩

/-- In a minimal counterexample, a leaf `x` (degree 1) lies in an edge whose other two vertices
both have degree exactly 2 (Claims 2 and 4.1). -/
lemma leaf_nbr_deg_two (h : MinCex E) {x v : α} {e : Finset α} (he : e ∈ E) (hxe : x ∈ e)
    (hve : v ∈ e) (hxv : x ≠ v) (hx : deg E x = 1) : deg E v = 2 := by
  have hv1 : deg E v ≠ 1 := fun hv => h.two_leaves_false he hxe hve hxv hx hv
  have hv0 := deg_pos_of_mem he hve
  by_contra hv2
  set j := deg E v with hj
  have hj3 : 3 ≤ j := by omega
  have hxv' : x ∉ verts (del E {v}) := not_mem_verts_del fun f hf hxf => by
    rw [eq_of_deg_one hx he hxe hf hxf, Finset.disjoint_singleton_right, not_not]; exact hve
  have hvv : v ∉ verts (del E {v}) := fun hv =>
    Finset.disjoint_left.1 (verts_del_disjoint E {v}) hv (Finset.mem_singleton_self v)
  have hxn : x ∈ nbr E {v} := Finset.mem_sdiff.2
    ⟨subset_verts (mem_hit.2 ⟨he, by simpa using hve⟩) hxe, by simpa using hxv⟩
  have hk : 2 * hE (del E {v}) ≤ 2 * j - 1 := by
    refine (h.two_mul_hE_del_le {v}).trans ?_
    have hsub : nbr E {v} ∩ verts (del E {v}) ⊆ (nbr E {v}).erase x := by
      intro w hw; rw [Finset.mem_inter] at hw
      exact Finset.mem_erase.2 ⟨fun hwx => hxv' (hwx ▸ hw.2), hw.1⟩
    refine (Finset.card_le_card hsub).trans ?_
    rw [Finset.card_erase_of_mem hxn]
    have := card_nbr_singleton_le h.L.card3 v
    omega
  refine h.no_fav_del (X := {v}) (R := {v, x}) (D := hit E {v}) (j - 1) ?_ ?_ subset_rfl
    ⟨e, mem_hit.2 ⟨he, by simpa using hve⟩⟩ (by omega) ?_
  · intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact subset_verts he hve
    · exact subset_verts he hxe
  · rw [Finset.disjoint_left]; intro w hw hw'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hvv hw'
    · exact hxv' hw'
  · rw [Finset.card_singleton, card_hit_singleton, Finset.card_pair (Ne.symm hxv)]
    omega

end MinCex

end OpenProblemsLab.HY
