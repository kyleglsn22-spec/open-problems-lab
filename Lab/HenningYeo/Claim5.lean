import Lab.HenningYeo.Claim45

/-!
# Henning–Yeo Claims 5 and 6

After Claim 4 (`δ ≥ 2`) a minimal counterexample has no vertex of degree 1, so (with our form of
the strict part) it is of type 1: `17 τ > w`. Claim 5: `Δ ≤ 3`. Claim 6: deleting a vertex `x` of
degree 3 with `h(H - x) = 0` leaves every neighbour `y` of degree 2 inside a copy of `H₁₀`/`H₁₀'`.
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

namespace MinCex

variable {E : Finset (Finset α)}

/-- After Claim 4, a minimal counterexample is of type 1. -/
lemma not_good (h : MinCex E) : ¬ Good E := fun hg =>
  h.bad ⟨hg, fun ⟨x, hx⟩ => absurd hx (h.claim4 x)⟩

/-- A good reduction is impossible (type 1). -/
lemma no_good_del (h : MinCex E) {X R : Finset α} {D : Finset (Finset α)} (k : ℕ)
    (hR : R ⊆ verts E) (hRd : Disjoint R (verts (del E X))) (hD : D ⊆ hit E X)
    (hDne : D.Nonempty) (hk : hE (del E X) ≤ k)
    (hineq : 17 * X.card + k ≤ 4 * R.card + 4 * D.card) : False :=
  h.not_good (h.good_del k hR hRd hD hDne hk hineq)

/-- Every isolated edge of `H - X` lies inside `N(X)` (all its vertices have degree 1 there). -/
lemma iso_sub_nbr (h : MinCex E) {X : Finset α} {f : Finset α} (hf : f ∈ isoEdges (del E X)) :
    f ⊆ nbr E X := fun v hv => by
  by_contra hvn
  exact h.claim4 v (deg_one_of_iso_del hf hv hvn)

lemma three_mul_hE_del_le (h : MinCex E) (X : Finset α) :
    3 * hE (del E X) ≤ (nbr E X).card :=
  mul_hE_le _ 3 fun f hf => by
    rw [Finset.inter_eq_left.2 (h.iso_sub_nbr hf),
      h.L.card3 f (del_subset _ _ (isoEdges_subset _ hf))]

/-- **Claim 5**: `Δ(H) ≤ 3`. -/
lemma claim5 (h : MinCex E) (v : α) : deg E v ≤ 3 := by
  by_contra hlt
  push Not at hlt
  have hk : 3 * hE (del E {v}) ≤ 2 * deg E v :=
    (h.three_mul_hE_del_le {v}).trans (card_nbr_singleton_le h.L.card3 v)
  obtain ⟨e, he⟩ : (hit E {v}).Nonempty := Finset.card_pos.1 (by rw [card_hit_singleton]; omega)
  have hvE : v ∈ verts E := by
    have := (mem_hit.1 he).2
    rw [Finset.disjoint_singleton_right, not_not] at this
    exact subset_verts (mem_hit.1 he).1 this
  refine h.no_fav_del (X := {v}) (R := {v}) (D := hit E {v}) (hE (del E {v}))
    (Finset.singleton_subset_iff.2 hvE) ?_ subset_rfl ⟨e, he⟩ le_rfl ?_
  · rw [Finset.disjoint_singleton_left]
    exact fun h' => Finset.disjoint_left.1 (verts_del_disjoint E {v}) h' (Finset.mem_singleton_self v)
  · rw [Finset.card_singleton, card_hit_singleton]
    omega

end MinCex


/-- A connected component through `y`: a closed set containing `y` with no proper nonempty closed
subset. -/
lemma exists_component (F : Finset (Finset α)) {y : α} (hy : y ∈ verts F) :
    ∃ K, IsClosed F K ∧ y ∈ verts K ∧ ∀ K', IsClosed K K' → K'.Nonempty → K' = K := by
  classical
  set C := F.powerset.filter (fun K => IsClosed F K ∧ y ∈ verts K)
  have hF : F ∈ C := Finset.mem_filter.2 ⟨Finset.mem_powerset_self F,
    ⟨subset_rfl, fun e he _ => he⟩, hy⟩
  obtain ⟨K, hK, hmin⟩ := C.exists_min_image Finset.card ⟨F, hF⟩
  obtain ⟨-, hKcl, hyK⟩ := Finset.mem_filter.1 hK
  refine ⟨K, hKcl, hyK, fun K' hK' hne => ?_⟩
  by_cases hyK' : y ∈ verts K'
  · have hC : K' ∈ C := Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (hK'.1.trans hKcl.1),
      hKcl.trans hK', hyK'⟩
    exact Finset.eq_of_subset_of_card_le hK'.1 (hmin K' hC)
  · have hc := hK'.compl
    have hyd : y ∈ verts (K \ K') := by
      have : K = K' ∪ (K \ K') := (Finset.union_sdiff_of_subset hK'.1).symm
      rw [this, verts_union, Finset.mem_union] at hyK
      exact hyK.resolve_left hyK'
    have hC : K \ K' ∈ C := Finset.mem_filter.2 ⟨Finset.mem_powerset.2
      (Finset.sdiff_subset.trans hKcl.1), hKcl.trans hc, hyd⟩
    have h1 := hmin _ hC
    have h2 : (K \ K').card < K.card := by
      rw [Finset.card_sdiff_of_subset hK'.1]
      have := Finset.card_pos.2 hne
      have := Finset.card_le_card hK'.1
      omega
    omega

namespace MinCex

variable {E : Finset (Finset α)}

lemma wt_eq (h : MinCex E) : wt E = 4 * (verts E).card + 4 * E.card := by
  unfold wt; rw [h.hE_eq_zero]; rfl

/-- **Claim 6**: if `deg x = 3`, `deg y = 2`, `x, y` adjacent and `h(H - x) = 0`, then `y` lies in a
copy of `H₁₀`/`H₁₀'` that is a union of components of `H - x`. -/
lemma claim6 (h : MinCex E) {x y : α} (hx : deg E x = 3) (hy : deg E y = 2) {e : Finset α}
    (he : e ∈ E) (hxe : x ∈ e) (hye : y ∈ e) (h0 : hE (del E {x}) = 0) :
    ∃ F, IsClosed (del E {x}) F ∧ y ∈ verts F ∧ IsGadget F := by
  by_contra hno
  have hxy : x ≠ y := by rintro rfl; omega
  obtain ⟨f, hf, hfe, hyf, hat⟩ := exists_other_edge he hye hy
  have hxf : x ∉ f := fun h' => hfe (h.L.eq_of_two hf he hxy h' hyf hxe hye)
  have hfH : f ∈ del E {x} := mem_del.2 ⟨hf, Finset.disjoint_singleton_right.2 hxf⟩
  have hdy : deg (del E {x}) y = 1 := by
    refine (deg_eq_one_iff hfH hyf).2 fun g hg hyg => ?_
    rcases hat g (del_subset _ _ hg) hyg with rfl | rfl
    · exact absurd hxe (Finset.disjoint_singleton_right.1 (mem_del.1 hg).2)
    · rfl
  obtain ⟨K, hK, hyK, hconn⟩ := exists_component (del E {x}) (subset_verts hfH hyf)
  have hdyK : deg K y = 1 := (hK.deg_eq hyK).trans hdy
  have hexc : ¬ HasExc K := by
    rintro ⟨z, -, hz⟩
    rcases hz with hz | ⟨F, hF, hzF, hgad⟩
    · obtain ⟨g, hg, hzg⟩ := mem_verts.1 hz
      have hgK := isoEdges_subset K hg
      have hgcl : IsClosed K {g} := by
        refine ⟨Finset.singleton_subset_iff.2 hgK, fun g' hg' hne => ?_⟩
        by_contra hg'g
        rw [Finset.mem_singleton] at hg'g
        apply hne
        simp only [verts, Finset.singleton_biUnion, id]
        exact ((Finset.mem_filter.1 hg).2 g' hg' hg'g).symm
      have hKg := hconn _ hgcl (Finset.singleton_nonempty g)
      have hiso : g ∈ isoEdges (del E {x}) := by
        refine Finset.mem_filter.2 ⟨hK.1 hgK, fun g' hg' hne => ?_⟩
        by_contra hmeet
        have : g' ∈ K := hK.2 g' hg' (by
          rw [← hKg]; simp only [verts, Finset.singleton_biUnion, id]
          exact fun hd => hmeet hd.symm)
        rw [← hKg, Finset.mem_singleton] at this
        exact hne this
      rw [hE, Finset.card_eq_zero] at h0
      rw [h0] at hiso
      exact Finset.notMem_empty g hiso
    · have hFne : F.Nonempty := by
        obtain ⟨g, hg, -⟩ := mem_verts.1 hzF; exact ⟨g, hg⟩
      have hFK := hconn F hF hFne
      subst hFK
      exact hno ⟨F, hK, hyK, hgad⟩
  have hss : K ⊂ E := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨hK.1.trans (del_subset _ _), fun hKE => ?_⟩
    have : e ∈ del E {x} := hK.1 (hKE ▸ he)
    exact Finset.disjoint_singleton_right.1 (mem_del.1 this).2 hxe
  have hss2 : del E {x} \ K ⊂ E := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.sdiff_subset.trans (del_subset _ _),
      fun hKE => ?_⟩
    have : e ∈ del E {x} := Finset.sdiff_subset (hKE ▸ he)
    exact Finset.disjoint_singleton_right.1 (mem_del.1 this).2 hxe
  have hLK := h.L.mono (hK.1.trans (del_subset _ _))
  obtain ⟨T₁, hT₁, hT₁w⟩ := (h.ih K (sz_lt_of_ssubset hss) hLK
    (h.F7.mono (hK.1.trans (del_subset _ _)))).2 ⟨y, hdyK⟩ hexc
  obtain ⟨T₂, hT₂, hT₂w⟩ := (h.ih _ (sz_lt_of_ssubset hss2)
    (h.L.mono hss2.subset) (h.F7.mono hss2.subset)).1
  have hT := (hT₁.split hK.1 hT₂).of_del (X := {x})
  have hw := hK.wt_eq
  have hxE : x ∈ verts E := subset_verts he hxe
  have hn := card_verts_del_singleton_lt hxE
  have hm := card_del_singleton E x
  have hwE := h.wt_eq
  have hc1 := Finset.card_union_le (T₁ ∪ T₂) {x}
  have hc2 := Finset.card_union_le T₁ T₂
  rw [Finset.card_singleton] at hc1
  apply h.not_good
  refine ⟨_, hT, ?_⟩
  have : wt (del E {x}) = 4 * (verts (del E {x})).card + 4 * (del E {x}).card := by
    unfold wt; rw [h0]; rfl
  omega

end MinCex

end OpenProblemsLab.HY
