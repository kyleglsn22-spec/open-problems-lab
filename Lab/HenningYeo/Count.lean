import Lab.HenningYeo.Framework

/-!
# Henning–Yeo: weight bookkeeping for deletions `H - X`
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-- The edges meeting `X`. -/
def hit (E : Finset (Finset α)) (X : Finset α) : Finset (Finset α) :=
  E.filter (fun e => ¬ Disjoint e X)

/-- Neighbours of `X` outside `X`. -/
def nbr (E : Finset (Finset α)) (X : Finset α) : Finset α := verts (hit E X) \ X

lemma mem_hit {E : Finset (Finset α)} {X : Finset α} {e : Finset α} :
    e ∈ hit E X ↔ e ∈ E ∧ ¬ Disjoint e X := Finset.mem_filter

lemma del_union_hit (E : Finset (Finset α)) (X : Finset α) : del E X ∪ hit E X = E := by
  ext e; simp only [Finset.mem_union, mem_del, mem_hit]; tauto

lemma disjoint_del_hit (E : Finset (Finset α)) (X : Finset α) : Disjoint (del E X) (hit E X) := by
  rw [Finset.disjoint_left]; intro e h1 h2; exact (mem_hit.1 h2).2 (mem_del.1 h1).2

lemma card_del_add_hit (E : Finset (Finset α)) (X : Finset α) :
    (del E X).card + (hit E X).card = E.card := by
  rw [← Finset.card_union_of_disjoint (disjoint_del_hit E X), del_union_hit]

lemma isoEdges_pairwise {E : Finset (Finset α)} {e f : Finset α} (he : e ∈ isoEdges E)
    (hf : f ∈ isoEdges E) (hne : e ≠ f) : Disjoint e f :=
  (Finset.mem_filter.1 he).2 f (isoEdges_subset E hf) (Ne.symm hne)

/-- In a hypergraph without isolated edges, every isolated edge of `H - X` meets `N(X)`. -/
lemma iso_del_meets_nbr {E : Finset (Finset α)} (h0 : hE E = 0) {X : Finset α} {f : Finset α}
    (hf : f ∈ isoEdges (del E X)) : ¬ Disjoint f (nbr E X) := by
  have hfd := isoEdges_subset _ hf
  have hfE := del_subset E X hfd
  have hnot : f ∉ isoEdges E := by
    intro h; rw [hE, Finset.card_eq_zero] at h0; rw [h0] at h; exact Finset.notMem_empty f h
  simp only [isoEdges, Finset.mem_filter, not_and, not_forall] at hnot
  obtain ⟨g, hg, hgf, hdis⟩ := hnot hfE
  have hgd : g ∉ del E X := fun hgd => hdis ((Finset.mem_filter.1 hf).2 g hgd hgf)
  have hgX : ¬ Disjoint g X := fun h => hgd (mem_del.2 ⟨hg, h⟩)
  obtain ⟨v, hvf, hvg⟩ := Finset.not_disjoint_iff.1 hdis
  have hvX : v ∉ X := fun h => Finset.disjoint_left.1 (mem_del.1 hfd).2 hvf h
  rw [Finset.not_disjoint_iff]
  exact ⟨v, hvf, Finset.mem_sdiff.2 ⟨mem_verts.2 ⟨g, mem_hit.2 ⟨hg, hgX⟩, hvg⟩, hvX⟩⟩

/-- Counting isolated edges: if each one meets `S` in at least `t` vertices, `t h ≤ |S|`. -/
lemma mul_hE_le {E : Finset (Finset α)} (S : Finset α) (t : ℕ)
    (ht : ∀ f ∈ isoEdges E, t ≤ (f ∩ S).card) : t * hE E ≤ S.card := by
  unfold hE
  have hdisj : (isoEdges E : Set (Finset α)).PairwiseDisjoint (fun f => f ∩ S) := by
    intro e he f hf hne
    exact Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left (isoEdges_pairwise he hf hne))
  calc t * (isoEdges E).card = ∑ _f ∈ isoEdges E, t := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ f ∈ isoEdges E, (f ∩ S).card := Finset.sum_le_sum ht
    _ = ((isoEdges E).biUnion (fun f => f ∩ S)).card := (Finset.card_biUnion hdisj).symm
    _ ≤ S.card := Finset.card_le_card (Finset.biUnion_subset.2 fun f _ => Finset.inter_subset_right)

/-- Weight of `H - X`, given vertices `R` and edges `D` known to disappear. -/
lemma wt_del_le {E : Finset (Finset α)} {X R : Finset α} {D : Finset (Finset α)}
    (hR : R ⊆ verts E) (hRd : Disjoint R (verts (del E X))) (hD : D ⊆ hit E X) :
    wt (del E X) + 4 * R.card + 4 * D.card ≤ 4 * (verts E).card + 4 * E.card + hE (del E X) := by
  have h1 : (verts (del E X)).card + R.card ≤ (verts E).card := by
    rw [← Finset.card_union_of_disjoint hRd.symm]
    exact Finset.card_le_card (Finset.union_subset (verts_mono (del_subset E X)) hR)
  have h2 := card_del_add_hit E X
  have h3 := Finset.card_le_card hD
  unfold wt
  omega

lemma sz_del_lt {E : Finset (Finset α)} {X : Finset α} (h : (hit E X).Nonempty) :
    sz (del E X) < sz E := by
  unfold sz
  have h1 := card_del_add_hit E X
  have h2 := Finset.card_pos.2 h
  have h3 := Finset.card_le_card (verts_mono (del_subset E X))
  omega

namespace MinCex

variable {E : Finset (Finset α)}

/-- A favorable deletion leads to a contradiction. -/
lemma no_fav_del (h : MinCex E) {X R : Finset α} {D : Finset (Finset α)} (k : ℕ)
    (hR : R ⊆ verts E) (hRd : Disjoint R (verts (del E X))) (hD : D ⊆ hit E X)
    (hDne : D.Nonempty) (hk : hE (del E X) ≤ k)
    (hineq : 17 * X.card + k < 4 * R.card + 4 * D.card) : False := by
  have hw := wt_del_le hR hRd hD
  have h0 := h.hE_eq_zero
  refine h.no_favorable (X := X) (sz_del_lt (hDne.mono hD)) (h.L.mono (del_subset E X))
    (h.F7.mono (del_subset E X)) (fun T hT => hT.of_del) ?_
  unfold wt at hw ⊢
  omega

/-- A good deletion gives `Good E`. -/
lemma good_del (h : MinCex E) {X R : Finset α} {D : Finset (Finset α)} (k : ℕ)
    (hR : R ⊆ verts E) (hRd : Disjoint R (verts (del E X))) (hD : D ⊆ hit E X)
    (hDne : D.Nonempty) (hk : hE (del E X) ≤ k)
    (hineq : 17 * X.card + k ≤ 4 * R.card + 4 * D.card) : Good E := by
  have hw := wt_del_le hR hRd hD
  have h0 := h.hE_eq_zero
  refine h.good_of_reduction (X := X) (sz_del_lt (hDne.mono hD)) (h.L.mono (del_subset E X))
    (h.F7.mono (del_subset E X)) (fun T hT => hT.of_del) ?_
  unfold wt at hw ⊢
  omega

end MinCex

end OpenProblemsLab.HY

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

lemma hit_singleton (E : Finset (Finset α)) (x : α) : hit E {x} = E.filter (x ∈ ·) := by
  ext e; simp [hit, Finset.disjoint_singleton_right]

lemma card_hit_singleton (E : Finset (Finset α)) (x : α) : (hit E {x}).card = deg E x := by
  rw [hit_singleton]; rfl

/-- A vertex all of whose edges meet `X` is not a vertex of `H - X`. -/
lemma not_mem_verts_del {E : Finset (Finset α)} {X : Finset α} {y : α}
    (hy : ∀ f ∈ E, y ∈ f → ¬ Disjoint f X) : y ∉ verts (del E X) := by
  intro hy'
  obtain ⟨f, hf, hyf⟩ := mem_verts.1 hy'
  exact hy f (del_subset E X hf) hyf (mem_del.1 hf).2

lemma eq_of_deg_one {E : Finset (Finset α)} {y : α} {e : Finset α} (hy : deg E y = 1) (he : e ∈ E)
    (hye : y ∈ e) {f : Finset α} (hf : f ∈ E) (hyf : y ∈ f) : f = e := by
  unfold deg at hy
  obtain ⟨g, hg⟩ := Finset.card_eq_one.1 hy
  have h1 : e ∈ E.filter (y ∈ ·) := Finset.mem_filter.2 ⟨he, hye⟩
  have h2 : f ∈ E.filter (y ∈ ·) := Finset.mem_filter.2 ⟨hf, hyf⟩
  rw [hg, Finset.mem_singleton] at h1 h2
  rw [h1, h2]

lemma card_verts_hit_singleton {E : Finset (Finset α)} (h3 : ∀ e ∈ E, e.card = 3) (x : α) :
    (verts (hit E {x})).card ≤ 1 + 2 * deg E x := by
  have hsub : verts (hit E {x}) ⊆ {x} ∪ (hit E {x}).biUnion (fun e => e.erase x) := by
    intro v hv
    obtain ⟨e, he, hve⟩ := mem_verts.1 hv
    by_cases hvx : v = x
    · simp [hvx]
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨e, he, Finset.mem_erase.2 ⟨hvx, hve⟩⟩)
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  rw [Finset.card_singleton, ← card_hit_singleton]
  have : ((hit E {x}).biUnion (fun e => e.erase x)).card ≤ ∑ e ∈ hit E {x}, (e.erase x).card :=
    Finset.card_biUnion_le
  have h2 : ∑ e ∈ hit E {x}, (e.erase x).card = ∑ _e ∈ hit E {x}, 2 := by
    refine Finset.sum_congr rfl fun e he => ?_
    have hxe : x ∈ e := by
      have := (mem_hit.1 he).2; rw [Finset.disjoint_singleton_right, not_not] at this; exact this
    rw [Finset.card_erase_of_mem hxe, h3 e (mem_hit.1 he).1]
  rw [h2, Finset.sum_const, smul_eq_mul] at this
  omega

lemma card_nbr_singleton_le {E : Finset (Finset α)} (h3 : ∀ e ∈ E, e.card = 3) (x : α) :
    (nbr E {x}).card ≤ 2 * deg E x := by
  have h := card_verts_hit_singleton h3 x
  unfold nbr
  have := Finset.card_sdiff_add_card_inter (verts (hit E {x})) {x}
  have h' : (verts (hit E {x}) ∩ {x}).card ≤ 1 := (Finset.card_le_card Finset.inter_subset_right).trans (by simp)
  by_cases hx : deg E x = 0
  · have : hit E {x} = ∅ := by rw [← Finset.card_eq_zero, card_hit_singleton, hx]
    simp [this, verts]
  · have hxv : x ∈ verts (hit E {x}) := by
      obtain ⟨e, he⟩ := Finset.card_pos.1 (show 0 < (hit E {x}).card by rw [card_hit_singleton]; omega)
      have := (mem_hit.1 he).2; rw [Finset.disjoint_singleton_right, not_not] at this
      exact subset_verts he this
    have : (verts (hit E {x}) ∩ {x}).card = 1 := by
      rw [Finset.inter_singleton_of_mem hxv, Finset.card_singleton]
    omega

namespace MinCex

variable {E : Finset (Finset α)}

/-- Claim 2: no edge with two vertices of degree 1. -/
lemma no_two_leaves (h : MinCex E) {x y z : α} (he : ({x, y, z} : Finset α) ∈ E)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hy : deg E y = 1) (hz : deg E z = 1) : False := by
  set e : Finset α := {x, y, z}
  have h0 := h.hE_eq_zero
  by_cases hx1 : deg E x = 1
  · -- `e` is an isolated edge
    have hiso : e ∈ isoEdges E := by
      refine Finset.mem_filter.2 ⟨he, fun f hf hfe => ?_⟩
      rw [Finset.disjoint_left]
      intro v hve hvf
      simp only [e, Finset.mem_insert, Finset.mem_singleton] at hve
      rcases hve with rfl | rfl | rfl
      · exact hfe (eq_of_deg_one hx1 hf hvf he (by simp [e])).symm
      · exact hfe (eq_of_deg_one hy hf hvf he (by simp [e])).symm
      · exact hfe (eq_of_deg_one hz hf hvf he (by simp [e])).symm
    rw [hE, Finset.card_eq_zero] at h0; rw [h0] at hiso; exact Finset.notMem_empty e hiso
  have hxpos : 1 ≤ deg E x := by
    unfold deg; exact Finset.card_pos.2 ⟨e, Finset.mem_filter.2 ⟨he, by simp [e]⟩⟩
  have hx2 : 2 ≤ deg E x := by omega
  have hmem : ∀ v ∈ e, ∀ f ∈ E, v ∈ f → v ≠ x → f = e := by
    intro v hv f hf hvf hvx
    simp only [e, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact absurd rfl hvx
    · exact eq_of_deg_one hy he (by simp [e]) hf hvf
    · exact eq_of_deg_one hz he (by simp [e]) hf hvf
  have hex : ¬ Disjoint e {x} := by simp [e]
  have hyv : y ∉ verts (del E {x}) :=
    not_mem_verts_del fun f hf hyf => (hmem y (by simp [e]) f hf hyf (Ne.symm hxy)) ▸ hex
  have hzv : z ∉ verts (del E {x}) :=
    not_mem_verts_del fun f hf hzf => (hmem z (by simp [e]) f hf hzf (Ne.symm hxz)) ▸ hex
  have hxv : x ∉ verts (del E {x}) := fun hx =>
    Finset.disjoint_left.1 (verts_del_disjoint E {x}) hx (Finset.mem_singleton_self x)
  -- isolated edges of `H - x` meet `N(x) \ {y, z}`
  set S := ((nbr E {x}).erase y).erase z with hSdef
  have hS : (S).card + 2 ≤ (nbr E {x}).card := by
    have hy' : y ∈ nbr E {x} := Finset.mem_sdiff.2 ⟨subset_verts (mem_hit.2 ⟨he, hex⟩) (by simp [e]),
      by simpa using hxy.symm⟩
    have hz' : z ∈ (nbr E {x}).erase y := Finset.mem_erase.2 ⟨hyz.symm,
      Finset.mem_sdiff.2 ⟨subset_verts (mem_hit.2 ⟨he, hex⟩) (by simp [e]), by simpa using hxz.symm⟩⟩
    rw [hSdef, Finset.card_erase_of_mem hz', Finset.card_erase_of_mem hy']
    have := Finset.card_pos.2 ⟨z, hz'⟩
    rw [Finset.card_erase_of_mem hy'] at this
    omega
  have hk : 1 * hE (del E {x}) ≤ S.card := by
    refine mul_hE_le S 1 fun f hf => ?_
    obtain ⟨v, hvf, hvn⟩ := Finset.not_disjoint_iff.1 (iso_del_meets_nbr h0 hf)
    have hfv : f ⊆ verts (del E {x}) := subset_verts (isoEdges_subset _ hf)
    refine Finset.card_pos.2 ⟨v, Finset.mem_inter.2 ⟨hvf, ?_⟩⟩
    refine Finset.mem_erase.2 ⟨fun hvz => hzv (hvz ▸ hfv hvf), Finset.mem_erase.2
      ⟨fun hvy => hyv (hvy ▸ hfv hvf), hvn⟩⟩
  have hn := card_nbr_singleton_le h.L.card3 x
  refine h.no_fav_del (X := {x}) (R := e) (D := hit E {x}) S.card (subset_verts he) ?_
    subset_rfl ⟨e, mem_hit.2 ⟨he, hex⟩⟩ (by omega) ?_
  · rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [e, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hxv hv'
    · exact hyv hv'
    · exact hzv hv'
  · rw [Finset.card_singleton, card_hit_singleton, Finset.card_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩]
    omega

end MinCex

end OpenProblemsLab.HY
