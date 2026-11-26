import Lab.HenningYeo.Claim10

/-!
# Henning–Yeo Claim 11, part 1: counting tools and the set-up

`Σ_{v ∈ H - X} (degree lost by v)` balances the deleted edges (`sum_deg_hit`). For an independent
triple `S` in `N(x)` this forces `H - S` to have exactly two isolated edges (Claim 11.1).
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-- Double counting of incidences. -/
lemma sum_deg_eq (F : Finset (Finset α)) (V : Finset α) :
    ∑ v ∈ V, deg F v = ∑ f ∈ F, (f ∩ V).card := by
  unfold deg
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]

lemma deg_del_add_hit (E : Finset (Finset α)) (X : Finset α) (v : α) :
    deg (del E X) v + deg (hit E X) v = deg E v := by
  unfold deg
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (disjoint_del_hit E X)),
    ← Finset.filter_union, del_union_hit]

lemma deg_iso {F : Finset (Finset α)} {f : Finset α} (hf : f ∈ isoEdges F) {v : α} (hv : v ∈ f) :
    deg F v = 1 := by
  refine (deg_eq_one_iff (isoEdges_subset F hf) hv).2 fun g hg hvg => ?_
  by_contra hgf
  exact Finset.disjoint_left.1 ((Finset.mem_filter.1 hf).2 g hg hgf) hv hvg

lemma card_verts_iso {F : Finset (Finset α)} (h3 : ∀ e ∈ F, e.card = 3) :
    (verts (isoEdges F)).card = 3 * hE F := by
  unfold verts hE
  rw [Finset.card_biUnion (t := id) (fun e he f hf hne => isoEdges_pairwise he hf hne)]
  rw [Finset.sum_congr rfl (g := fun _ => 3) (fun e he => by simpa using h3 e (isoEdges_subset F he)),
    Finset.sum_const, smul_eq_mul, mul_comm]

variable {E : Finset (Finset α)}

/-- In a 3-regular hypergraph the degree lost by the surviving vertices balances the deleted
edges. -/
lemma sum_deg_hit (hL : IsL3 E) (hreg : ∀ v ∈ verts E, deg E v = 3) (X : Finset α) :
    ∑ v ∈ verts (del E X), deg (hit E X) v + 3 * (verts E \ verts (del E X)).card
      = 3 * (hit E X).card := by
  have h1 : ∑ v ∈ verts E, deg (hit E X) v = 3 * (hit E X).card := by
    rw [sum_deg_eq, Finset.sum_congr rfl (g := fun _ => 3), Finset.sum_const, smul_eq_mul,
      mul_comm]
    intro f hf
    have hfE := (mem_hit.1 hf).1
    rw [Finset.inter_eq_left.2 (subset_verts hfE), hL.card3 f hfE]
  have h2 : ∑ v ∈ verts E \ verts (del E X), deg (hit E X) v =
      3 * (verts E \ verts (del E X)).card := by
    rw [Finset.sum_congr rfl (g := fun _ => 3), Finset.sum_const, smul_eq_mul, mul_comm]
    intro v hv
    rw [Finset.mem_sdiff] at hv
    have := deg_del_add_hit E X v
    rw [deg_eq_zero_of_not_mem hv.2, hreg v hv.1] at this
    omega
  have h3 := Finset.sum_sdiff (f := fun v => deg (hit E X) v) (verts_mono (del_subset E X))
  omega

/-- Each isolated edge of `H - X` costs 6 in that balance. -/
lemma six_hE_le (hL : IsL3 E) (hreg : ∀ v ∈ verts E, deg E v = 3) (X : Finset α) :
    6 * hE (del E X) ≤ ∑ v ∈ verts (del E X), deg (hit E X) v := by
  have hsub : verts (isoEdges (del E X)) ⊆ verts (del E X) := verts_mono (isoEdges_subset _)
  have h2 : ∀ v ∈ verts (isoEdges (del E X)), deg (hit E X) v = 2 := by
    intro v hv
    obtain ⟨f, hf, hvf⟩ := mem_verts.1 hv
    have := deg_del_add_hit E X v
    rw [deg_iso hf hvf, hreg v (verts_mono (del_subset E X) (hsub hv))] at this
    omega
  calc 6 * hE (del E X) = 2 * (verts (isoEdges (del E X))).card := by
        rw [card_verts_iso (fun e he => hL.card3 e (del_subset E X he))]; ring
    _ = ∑ v ∈ verts (isoEdges (del E X)), deg (hit E X) v := by
        rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

/-- If every edge meets `S` in at most one vertex, `|hit E S| = Σ_{s ∈ S} deg s`. -/
lemma card_hit_of_ind {S : Finset α} (hS : ∀ f ∈ E, (f ∩ S).card ≤ 1) :
    (hit E S).card = ∑ s ∈ S, deg E s := by
  rw [sum_deg_eq, ← Finset.sum_subset (s₁ := hit E S) (fun f hf => (mem_hit.1 hf).1)]
  · rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun f hf => ?_
    have h1 := hS f (mem_hit.1 hf).1
    have h2 : (f ∩ S).Nonempty := Finset.not_disjoint_iff_nonempty_inter.1 (mem_hit.1 hf).2
    have := Finset.card_pos.2 h2
    omega
  · intro f hfE hf
    rw [Finset.card_eq_zero, ← Finset.disjoint_iff_inter_eq_empty]
    by_contra hd
    exact hf (mem_hit.2 ⟨hfE, hd⟩)

/-- The edges at a vertex of degree 3. -/
lemma edges_three {s : α} (hs : deg E s = 3) {f : Finset α} (hf : f ∈ E) (hsf : s ∈ f) :
    ∃ f₂ f₃, f₂ ∈ E ∧ f₃ ∈ E ∧ s ∈ f₂ ∧ s ∈ f₃ ∧ f₂ ≠ f ∧ f₃ ≠ f ∧ f₂ ≠ f₃ ∧
      ∀ g ∈ E, s ∈ g → g = f ∨ g = f₂ ∨ g = f₃ := by
  have hmem : f ∈ E.filter (s ∈ ·) := Finset.mem_filter.2 ⟨hf, hsf⟩
  have hc : ((E.filter (s ∈ ·)).erase f).card = 2 := by
    rw [Finset.card_erase_of_mem hmem]; unfold deg at hs; omega
  obtain ⟨f₂, f₃, h23, heq⟩ := Finset.card_eq_two.1 hc
  have h2 : f₂ ∈ (E.filter (s ∈ ·)).erase f := by rw [heq]; simp
  have h3 : f₃ ∈ (E.filter (s ∈ ·)).erase f := by rw [heq]; simp
  simp only [Finset.mem_erase, Finset.mem_filter] at h2 h3
  refine ⟨f₂, f₃, h2.2.1, h3.2.1, h2.2.2, h3.2.2, h2.1, h3.1, h23, fun g hg hsg => ?_⟩
  by_cases hgf : g = f
  · exact Or.inl hgf
  · have : g ∈ (E.filter (s ∈ ·)).erase f := Finset.mem_erase.2 ⟨hgf, Finset.mem_filter.2 ⟨hg, hsg⟩⟩
    rw [heq] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    exact Or.inr this

lemma card_le_one_two {E : Finset (Finset α)} (hL : IsL3 E) {a b : α} (hab : a ≠ b) :
    (E.filter (fun f => a ∈ f ∧ b ∈ f)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro f hf g hg
  simp only [Finset.mem_filter] at hf hg
  exact hL.eq_of_two hf.1 hg.1 hab hf.2.1 hf.2.2 hg.2.1 hg.2.2

end OpenProblemsLab.HY
