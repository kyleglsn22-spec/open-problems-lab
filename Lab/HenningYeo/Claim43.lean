import Lab.HenningYeo.Leaf

/-!
# Henning–Yeo Claim 4.3

`F₇`-freeness survives adding an edge with a new vertex; and in the configuration of Claim 4,
no edge of `H - {v₁, v₂}` meets `S = (e₁ ∪ e₂) \ {v₁, v₂}` twice (Claim 4.3).
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

lemma F7Free_iff {E : Finset (Finset α)} :
    F7Free E ↔ ∀ g : Fin 7 → α, Function.Injective g → ¬ ∀ j, (F7L j).image g ∈ E := by
  unfold F7Free
  refine forall_congr' fun g => imp_congr_right fun _ => not_congr ?_
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩ j
    fin_cases j <;> simpa [F7L, Finset.image_insert] 
  · intro h
    exact ⟨by simpa [F7L] using h 0, by simpa [F7L] using h 1, by simpa [F7L] using h 2,
      by simpa [F7L] using h 3, by simpa [F7L] using h 4⟩

lemma F7L_injective : Function.Injective F7L := by decide

lemma F7L_two : ∀ j : Fin 5, ∀ i ∈ F7L j, ∃ k, k ≠ j ∧ i ∈ F7L k := by decide

/-- Adding an edge with a vertex not in `E'` keeps `F₇`-freeness. -/
lemma F7Free.insert_fresh {E' : Finset (Finset α)} (hF : F7Free E') {f : Finset α} {w : α}
    (hwf : w ∈ f) (hw : w ∉ verts E') : F7Free (insert f E') := by
  rw [F7Free_iff] at hF ⊢
  intro g hg hall
  by_cases hex : ∃ j, (F7L j).image g = f
  · obtain ⟨j, hj⟩ := hex
    rw [← hj, Finset.mem_image] at hwf
    obtain ⟨i, hi, rfl⟩ := hwf
    obtain ⟨k, hkj, hik⟩ := F7L_two j i hi
    rcases Finset.mem_insert.1 (hall k) with hk | hk
    · rw [← hj] at hk
      exact hkj (F7L_injective (Finset.image_injective hg hk))
    · exact hw (subset_verts hk (Finset.mem_image_of_mem g hik))
  · push Not at hex
    exact hF g hg fun j => (Finset.mem_insert.1 (hall j)).resolve_left (hex j)


lemma verts_insert (f : Finset α) (F : Finset (Finset α)) : verts (insert f F) = f ∪ verts F := by
  unfold verts; rw [Finset.biUnion_insert]; rfl

/-- A transversal of `F + {x, s₁, s₂}` with `x` new can be moved off `x`. -/
lemma transversal_off_fresh {F : Finset (Finset α)} {x s₁ s₂ : α} (hx : x ∉ verts F)
    {T : Finset α} (hT : IsTransversal (insert {x, s₁, s₂} F) T) :
    ∃ T' : Finset α, T'.card ≤ T.card ∧ IsTransversal F T' ∧ (s₁ ∈ T' ∨ s₂ ∈ T') := by
  have hf := hT _ (Finset.mem_insert_self _ _)
  have hF : IsTransversal F T := fun e he => hT e (Finset.mem_insert_of_mem he)
  by_cases hs : s₁ ∈ T ∨ s₂ ∈ T
  · exact ⟨T, le_rfl, hF, hs⟩
  · push Not at hs
    obtain ⟨u, hu⟩ := hf
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hu
    have hxT : x ∈ T := by
      rcases hu.1 with rfl | rfl | rfl
      · exact hu.2
      · exact absurd hu.2 hs.1
      · exact absurd hu.2 hs.2
    refine ⟨insert s₁ (T.erase x), ?_, fun e he => ?_, Or.inl (Finset.mem_insert_self _ _)⟩
    · rw [Finset.card_insert_of_notMem (fun h => hs.1 (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem hxT]
      have : 0 < T.card := Finset.card_pos.2 ⟨x, hxT⟩
      omega
    · obtain ⟨w, hw⟩ := hF e he
      rw [Finset.mem_inter] at hw
      have hwx : w ≠ x := fun h => hx (h ▸ subset_verts he hw.1)
      exact ⟨w, Finset.mem_inter.2 ⟨hw.1, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hwx, hw.2⟩)⟩⟩

/-- Replacing an edge `e'` of `F` (with `h(F) = 0`) by an edge `f` that contains two vertices of
`e'` creates at most two isolated edges. -/
lemma hE_insert_erase_le {F : Finset (Finset α)} (h0 : hE F = 0) {e' f : Finset α}
    (he' : e'.card = 3) {s₁ s₂ : α} (h12 : s₁ ≠ s₂) (h1 : s₁ ∈ e') (h2 : s₂ ∈ e') (hf1 : s₁ ∈ f)
    (hf2 : s₂ ∈ f) : hE (insert f (F.erase e')) ≤ 2 := by
  set H := insert f (F.erase e')
  set U := e' \ {s₁, s₂}
  have hU : U.card = 1 := by
    have hsub : ({s₁, s₂} : Finset α) ⊆ e' := by
      intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> assumption
    rw [Finset.card_sdiff_of_subset hsub, he', Finset.card_pair h12]
  obtain ⟨t, ht⟩ := Finset.card_eq_one.1 hU
  have hsub : isoEdges H ⊆ insert f ((isoEdges H).filter (t ∈ ·)) := by
    intro g hg
    by_cases hgf : g = f
    · rw [hgf]; exact Finset.mem_insert_self _ _
    refine Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hg, ?_⟩)
    have hgH := isoEdges_subset _ hg
    have hgF : g ∈ F.erase e' := (Finset.mem_insert.1 hgH).resolve_left hgf
    have hiso := (Finset.mem_filter.1 hg).2
    have hgfd : Disjoint g f := hiso f (Finset.mem_insert_self _ _) (Ne.symm hgf)
    have hnot : g ∉ isoEdges F := by
      intro h'; rw [hE, Finset.card_eq_zero] at h0; rw [h0] at h'; exact Finset.notMem_empty g h'
    simp only [isoEdges, Finset.mem_filter, not_and, not_forall] at hnot
    obtain ⟨g', hg', hg'g, hdis⟩ := hnot (Finset.mem_of_mem_erase hgF)
    have hg'e : g' = e' := by
      by_contra hne
      exact hdis (hiso g' (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hne, hg'⟩)) hg'g)
    subst hg'e
    obtain ⟨u, hug, hue⟩ := Finset.not_disjoint_iff.1 hdis
    have huU : u ∈ U := by
      refine Finset.mem_sdiff.2 ⟨hue, fun hu => ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact Finset.disjoint_left.1 hgfd hug hf1
      · exact Finset.disjoint_left.1 hgfd hug hf2
    rw [ht, Finset.mem_singleton] at huU
    exact huU ▸ hug
  have hle : ((isoEdges H).filter (t ∈ ·)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    by_contra hab
    exact Finset.disjoint_left.1 (isoEdges_pairwise ha.1 hb.1 hab) ha.2 hb.2
  unfold hE
  exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by omega))

namespace MinCex

variable {E : Finset (Finset α)}

/-- A transversal beating the weight contradicts minimality (for both types). -/
lemma no_strict (h : MinCex E) {T : Finset α} (hT : IsTransversal E T)
    (hw : 17 * T.card < wt E) : False :=
  h.bad ⟨⟨T, hT, hw.le⟩, fun _ _ => ⟨T, hT, hw⟩⟩

/-- A good hypergraph `E'` of smaller size whose transversals extend by one vertex. -/
lemma no_plus_one (h : MinCex E) {E' : Finset (Finset α)} (hs : sz E' < sz E) (hL : IsL3 E')
    (hF : F7Free E')
    (hT : ∀ T, IsTransversal E' T → ∃ T₀ : Finset α, T₀.card ≤ T.card + 1 ∧ IsTransversal E T₀)
    (hw : wt E' + 17 < wt E) : False := by
  obtain ⟨T, hT', hTw⟩ := (h.ih E' hs hL hF).1
  obtain ⟨T₀, hc, hT₀⟩ := hT T hT'
  exact h.no_strict hT₀ (by omega)

end MinCex

namespace Leaf

variable {E : Finset (Finset α)} {x v₁ v₂ : α} {e₁ e₂ : Finset α}

/-- Claim 4.1 packaged: a leaf of a minimal counterexample gives the configuration `Leaf`. -/
lemma exists_of_leaf (h : MinCex E) {x : α} (hx : deg E x = 1) :
    ∃ v₁ v₂ e₁ e₂, Leaf E x v₁ v₂ e₁ e₂ := by
  obtain ⟨e, he⟩ : (E.filter (x ∈ ·)).Nonempty := Finset.card_pos.1 (by unfold deg at hx; omega)
  rw [Finset.mem_filter] at he
  have hc : (e.erase x).card = 2 := by rw [Finset.card_erase_of_mem he.2, h.L.card3 e he.1]
  obtain ⟨v₁, v₂, h12, hev⟩ := Finset.card_eq_two.1 hc
  have hv1 : v₁ ∈ e.erase x := by rw [hev]; simp
  have hv2 : v₂ ∈ e.erase x := by rw [hev]; simp
  have hee : e = {x, v₁, v₂} := by rw [← hev, Finset.insert_erase he.2]
  have hx1 := (Finset.mem_erase.1 hv1).1
  have hx2 := (Finset.mem_erase.1 hv2).1
  subst hee
  have d1 := h.leaf_nbr_deg_two he.1 he.2 (Finset.mem_of_mem_erase hv1) hx1.symm hx
  have d2 := h.leaf_nbr_deg_two he.1 he.2 (Finset.mem_of_mem_erase hv2) hx2.symm hx
  obtain ⟨e₁, he₁, hne1, hv1e1, hat1⟩ := exists_other_edge he.1 (Finset.mem_of_mem_erase hv1) d1
  obtain ⟨e₂, he₂, hne2, hv2e2, hat2⟩ := exists_other_edge he.1 (Finset.mem_of_mem_erase hv2) d2
  exact ⟨v₁, v₂, e₁, e₂, ⟨he.1, hx1.symm, hx2.symm, h12, hx, he₁, he₂, hv1e1, hv2e2, hne1, hne2,
    hat1, hat2⟩⟩

lemma del12_eq (L : Leaf E x v₁ v₂ e₁ e₂) : del E {v₁, v₂} = E \ {{x, v₁, v₂}, e₁, e₂} := by
  ext g
  rw [L.mem_del12, Finset.mem_sdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]

lemma card_del12 (L : Leaf E x v₁ v₂ e₁ e₂) (hL : IsL3 E) :
    (del E {v₁, v₂}).card + 3 = E.card := by
  have hsub : ({{x, v₁, v₂}, e₁, e₂} : Finset (Finset α)) ⊆ E := by
    intro g hg; simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl
    exacts [L.he, L.e1E, L.e2E]
  have h3 : ({{x, v₁, v₂}, e₁, e₂} : Finset (Finset α)).card = 3 :=
    Finset.card_eq_three.2 ⟨_, _, _, L.e1ne.symm, L.e2ne.symm, L.e12 hL, rfl⟩
  have := Finset.card_le_card hsub
  rw [L.del12_eq, Finset.card_sdiff_of_subset hsub, h3]
  omega

lemma v1_verts (L : Leaf E x v₁ v₂ e₁ e₂) : v₁ ∈ verts E := subset_verts L.he v1_e
lemma v2_verts (L : Leaf E x v₁ v₂ e₁ e₂) : v₂ ∈ verts E := subset_verts L.he v2_e
lemma x_verts (L : Leaf E x v₁ v₂ e₁ e₂) : x ∈ verts E := subset_verts L.he x_e

lemma not_verts_del12 {v : α} (hv : v = v₁ ∨ v = v₂) : v ∉ verts (del E {v₁, v₂}) := fun h' =>
  Finset.disjoint_left.1 (verts_del_disjoint E _) h' (by rcases hv with rfl | rfl <;> simp)

/-- A transversal of `H - {v₁, v₂}` containing a vertex of `e₁ ∪ e₂` extends by one vertex. -/
lemma cover (L : Leaf E x v₁ v₂ e₁ e₂) {T : Finset α} (hT : IsTransversal (del E {v₁, v₂}) T)
    {s : α} (hs : s ∈ T) (hse : s ∈ e₁ ∪ e₂) : ∃ v, IsTransversal E (insert v T) := by
  have key : ∀ g ∈ E, g ∉ ({{x, v₁, v₂}, e₁, e₂} : Finset (Finset α)) → (g ∩ T).Nonempty := by
    intro g hg hg'
    exact hT g (by rw [L.del12_eq]; exact Finset.mem_sdiff.2 ⟨hg, hg'⟩)
  rcases Finset.mem_union.1 hse with h1 | h2
  · refine ⟨v₂, fun g hg => ?_⟩
    by_cases hg' : g ∈ ({{x, v₁, v₂}, e₁, e₂} : Finset (Finset α))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hg'
      rcases hg' with rfl | rfl | rfl
      · exact ⟨v₂, by simp⟩
      · exact ⟨s, Finset.mem_inter.2 ⟨h1, Finset.mem_insert_of_mem hs⟩⟩
      · exact ⟨v₂, Finset.mem_inter.2 ⟨L.v2e2, Finset.mem_insert_self _ _⟩⟩
    · obtain ⟨w, hw⟩ := key g hg hg'
      rw [Finset.mem_inter] at hw
      exact ⟨w, Finset.mem_inter.2 ⟨hw.1, Finset.mem_insert_of_mem hw.2⟩⟩
  · refine ⟨v₁, fun g hg => ?_⟩
    by_cases hg' : g ∈ ({{x, v₁, v₂}, e₁, e₂} : Finset (Finset α))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hg'
      rcases hg' with rfl | rfl | rfl
      · exact ⟨v₁, by simp⟩
      · exact ⟨v₁, Finset.mem_inter.2 ⟨L.v1e1, Finset.mem_insert_self _ _⟩⟩
      · exact ⟨s, Finset.mem_inter.2 ⟨h2, Finset.mem_insert_of_mem hs⟩⟩
    · obtain ⟨w, hw⟩ := key g hg hg'
      rw [Finset.mem_inter] at hw
      exact ⟨w, Finset.mem_inter.2 ⟨hw.1, Finset.mem_insert_of_mem hw.2⟩⟩

/-- `wt E = 4n + 4m` in a minimal counterexample. -/
lemma wt_eq (h : MinCex E) : wt E = 4 * (verts E).card + 4 * E.card := by
  unfold wt; rw [h.hE_eq_zero]; rfl

/-- **Claim 4.3**: every edge of `H - {v₁, v₂}` meets `S` in at most one vertex. -/
lemma claim43 (L : Leaf E x v₁ v₂ e₁ e₂) (h : MinCex E) {e' : Finset α}
    (he' : e' ∈ del E {v₁, v₂}) : (e' ∩ ((e₁ ∪ e₂) \ {v₁, v₂})).card ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨s₁, hs1, s₂, hs2, h12⟩ := Finset.one_lt_card.1 hlt
  simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, not_or] at hs1 hs2
  set Hs := del E {v₁, v₂}
  set H2 := insert ({x, s₁, s₂} : Finset α) (Hs.erase e')
  have hxHs : x ∉ verts Hs := L.x_not_verts_del12
  have hxF : x ∉ verts (Hs.erase e') := fun h' => hxHs (verts_mono (Finset.erase_subset _ _) h')
  have hxS : ∀ s, (s ∈ e₁ ∨ s ∈ e₂) → x ≠ s := by
    rintro s (hs | hs) rfl
    · exact L.x_not_e1 hs
    · exact L.x_not_e2 hs
  have hxs1 : x ≠ s₁ := hxS s₁ hs1.2.1
  have hxs2 : x ≠ s₂ := hxS s₂ hs2.2.1
  have he'E := del_subset _ _ he'
  -- `H2` is linear, 3-uniform and `F₇`-free
  have hL2 : IsL3 H2 := by
    constructor
    · intro f hf
      rcases Finset.mem_insert.1 hf with rfl | hf
      · exact Finset.card_eq_three.2 ⟨x, s₁, s₂, hxs1, hxs2, h12, rfl⟩
      · exact h.L.card3 f (del_subset _ _ (Finset.mem_of_mem_erase hf))
    · have key : ∀ f ∈ Hs.erase e', (f ∩ {x, s₁, s₂}).card ≤ 1 := by
        intro f hf
        rw [Finset.card_le_one]
        intro a ha b hb
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at ha hb
        have hfx : x ∉ f := fun h' => hxF (subset_verts hf h')
        have hfE := del_subset _ _ (Finset.mem_of_mem_erase hf)
        have hfe : f ≠ e' := Finset.ne_of_mem_erase hf
        rcases ha.2 with rfl | rfl | rfl
        · exact absurd ha.1 hfx
        all_goals rcases hb.2 with rfl | rfl | rfl
        all_goals first
          | rfl
          | exact absurd hb.1 hfx
          | exact absurd (h.L.eq_of_two hfE he'E h12 ha.1 hb.1 hs1.1 hs2.1) hfe
          | exact absurd (h.L.eq_of_two hfE he'E h12.symm ha.1 hb.1 hs2.1 hs1.1) hfe
      intro f hf g hg hfg
      rcases Finset.mem_insert.1 hf with rfl | hf
      · rcases Finset.mem_insert.1 hg with rfl | hg
        · exact absurd rfl hfg
        · rw [Finset.inter_comm]; exact key g hg
      · rcases Finset.mem_insert.1 hg with rfl | hg
        · exact key f hf
        · exact h.L.linear f (del_subset _ _ (Finset.mem_of_mem_erase hf)) g
            (del_subset _ _ (Finset.mem_of_mem_erase hg)) hfg
  have hF2 : F7Free H2 :=
    (h.F7.mono ((Finset.erase_subset _ _).trans (del_subset _ _))).insert_fresh (by simp) hxF
  -- size and weight
  have hc : Hs.card + 3 = E.card := L.card_del12 h.L
  have hHs : e' ∈ Hs := he'
  have hcard2 : H2.card ≤ Hs.card := by
    have : H2.card ≤ (Hs.erase e').card + 1 := Finset.card_insert_le _ _
    rw [Finset.card_erase_of_mem hHs] at this
    have : 0 < Hs.card := Finset.card_pos.2 ⟨e', hHs⟩
    omega
  have hverts2 : verts H2 ⊆ ((verts E).erase v₁).erase v₂ := by
    intro w hw
    rw [verts_insert, Finset.mem_union] at hw
    have hw' : w ∈ verts E ∧ w ≠ v₁ ∧ w ≠ v₂ := by
      rcases hw with hw | hw
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨L.x_verts, L.x1, L.x2⟩
        · exact ⟨subset_verts he'E hs1.1, hs1.2.2.1, hs1.2.2.2⟩
        · exact ⟨subset_verts he'E hs2.1, hs2.2.2.1, hs2.2.2.2⟩
      · have hw' := verts_mono (Finset.erase_subset _ _) hw
        refine ⟨verts_mono (del_subset _ _) hw', fun h' => ?_, fun h' => ?_⟩
        · exact not_verts_del12 (Or.inl h') hw'
        · exact not_verts_del12 (Or.inr h') hw'
    exact Finset.mem_erase.2 ⟨hw'.2.2, Finset.mem_erase.2 ⟨hw'.2.1, hw'.1⟩⟩
  have hn2 : (verts H2).card + 2 ≤ (verts E).card := by
    have := Finset.card_le_card hverts2
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨L.v12.symm, L.v2_verts⟩),
      Finset.card_erase_of_mem L.v1_verts] at this
    have : 2 ≤ (verts E).card := by
      have : ({v₁, v₂} : Finset α) ⊆ verts E := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl; exacts [L.v1_verts, L.v2_verts]
      have := Finset.card_le_card this; rwa [Finset.card_pair L.v12] at this
    omega
  have hh2 : hE H2 ≤ 2 :=
    hE_insert_erase_le (L.claim42 h) (h.L.card3 e' he'E) h12 hs1.1 hs2.1 (by simp) (by simp)
  refine h.no_plus_one (E' := H2) ?_ hL2 hF2 ?_ ?_
  · unfold sz; omega
  · intro T hT
    obtain ⟨T', hT'c, hT', hs⟩ := transversal_off_fresh hxF hT
    have hT's : IsTransversal Hs T' := by
      intro f hf
      by_cases hfe : f = e'
      · subst hfe
        rcases hs with hs | hs
        · exact ⟨s₁, Finset.mem_inter.2 ⟨hs1.1, hs⟩⟩
        · exact ⟨s₂, Finset.mem_inter.2 ⟨hs2.1, hs⟩⟩
      · exact hT' f (Finset.mem_erase.2 ⟨hfe, hf⟩)
    obtain ⟨s, hsT, hse⟩ : ∃ s ∈ T', s ∈ e₁ ∪ e₂ := by
      rcases hs with hs | hs
      · exact ⟨s₁, hs, Finset.mem_union.2 hs1.2.1⟩
      · exact ⟨s₂, hs, Finset.mem_union.2 hs2.2.1⟩
    obtain ⟨v, hv⟩ := L.cover hT's hsT hse
    exact ⟨insert v T', (Finset.card_insert_le _ _).trans (by omega), hv⟩
  · rw [Leaf.wt_eq h]; unfold wt; omega

end Leaf

end OpenProblemsLab.HY
