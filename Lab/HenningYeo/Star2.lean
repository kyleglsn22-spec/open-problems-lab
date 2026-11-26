import Lab.HenningYeo.Star

/-!
# Henning–Yeo Claim 7.2: the second edges `fᵢ` at the `vᵢ` are distinct
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

lemma card_six {β : Type*} [DecidableEq β] {a b c d e f : β} (h1 : a ≠ b) (h2 : a ≠ c)
    (h3 : a ≠ d) (h4 : a ≠ e) (h5 : a ≠ f) (h6 : b ≠ c) (h7 : b ≠ d) (h8 : b ≠ e) (h9 : b ≠ f)
    (h10 : c ≠ d) (h11 : c ≠ e) (h12 : c ≠ f) (h13 : d ≠ e) (h14 : d ≠ f) (h15 : e ≠ f) :
    ({a, b, c, d, e, f} : Finset β).card = 6 := by
  simp [Finset.card_insert_of_notMem, *]

lemma card_sdiff_le_of_two {s R : Finset α} {a b : α} (hab : a ≠ b) (ha : a ∈ s) (hb : b ∈ s)
    (haR : a ∈ R) (hbR : b ∈ R) : (s \ R).card + 2 ≤ s.card := by
  have h1 := Finset.card_sdiff_add_card_inter s R
  have h2 : ({a, b} : Finset α) ⊆ s ∩ R := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> simp [*]
  have h3 := Finset.card_le_card h2
  rw [Finset.card_pair hab] at h3
  omega

lemma card_sdiff_le_of_one {s R : Finset α} {a : α} (ha : a ∈ s) (haR : a ∈ R) :
    (s \ R).card + 1 ≤ s.card := by
  have h1 := Finset.card_sdiff_add_card_inter s R
  have h3 := Finset.card_pos.2 ⟨a, Finset.mem_inter.2 ⟨ha, haR⟩⟩
  omega

lemma exists_perm {i j : Fin 3} (hij : i ≠ j) : ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = j := by
  revert i j; decide

lemma disjoint_verts_del {E : Finset (Finset α)} {X R : Finset α}
    (hR : ∀ w ∈ R, ∀ g ∈ E, w ∈ g → ¬ Disjoint g X) : Disjoint R (verts (del E X)) :=
  Finset.disjoint_left.2 fun w hw => not_mem_verts_del (hR w hw)

namespace MinCex

variable {E : Finset (Finset α)}

/-- Isolated edges of `H - X` lie in the set `C` of vertices of edges meeting `X` outside `R`. -/
lemma three_hE_le (h : MinCex E) {X R C : Finset α} (hRd : Disjoint R (verts (del E X)))
    (hC : ∀ g ∈ E, ¬ Disjoint g X → ∀ w ∈ g, w ∉ R → w ∈ C) : 3 * hE (del E X) ≤ C.card := by
  refine mul_hE_le C 3 fun f hf => ?_
  have hfC : f ⊆ C := fun w hw => by
    have hwn := h.iso_sub_nbr hf hw
    rw [nbr, Finset.mem_sdiff] at hwn
    obtain ⟨g, hg, hwg⟩ := mem_verts.1 hwn.1
    rw [mem_hit] at hg
    exact hC g hg.1 hg.2 w hwg fun hwR =>
      Finset.disjoint_left.1 hRd hwR (subset_verts (isoEdges_subset _ hf) hw)
  rw [Finset.inter_eq_left.2 hfC, h.L.card3 f (del_subset _ _ (isoEdges_subset _ hf))]

end MinCex

namespace Star

variable {E : Finset (Finset α)} {x : α} {u v : Fin 3 → α}

lemma top_perm (σ : Equiv.Perm (Fin 3)) : top (u ∘ σ) = top u :=
  top_eq (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) (σ.injective.ne (by decide))

lemma perm (S : Star E x u v) (σ : Equiv.Perm (Fin 3)) : Star E x (u ∘ σ) (v ∘ σ) where
  hu := S.hu.comp σ.injective
  hv := S.hv.comp σ.injective
  huv i j := S.huv _ _
  hxu i := S.hxu _
  hxv i := S.hxv _
  he i := S.he _
  htop := by rw [show ({(u ∘ σ) 0, (u ∘ σ) 1, (u ∘ σ) 2} : Finset α) = top (u ∘ σ) from rfl,
    top_perm]; exact S.htop
  atx g hg hxg := by
    obtain ⟨i, rfl⟩ := S.atx g hg hxg
    exact ⟨σ.symm i, by simp⟩

/-- The closed neighbourhood `N[x]`. -/
def nx (x : α) (u v : Fin 3 → α) : Finset α :=
  insert x (Finset.univ.image u ∪ Finset.univ.image v)

lemma mem_nx {w : α} : w ∈ nx x u v ↔ w = x ∨ (∃ t, w = u t) ∨ ∃ t, w = v t := by
  simp [nx, eq_comm]

lemma x_nx : x ∈ nx x u v := mem_nx.2 (Or.inl rfl)
lemma u_nx (t : Fin 3) : u t ∈ nx x u v := mem_nx.2 (Or.inr (Or.inl ⟨t, rfl⟩))
lemma v_nx (t : Fin 3) : v t ∈ nx x u v := mem_nx.2 (Or.inr (Or.inr ⟨t, rfl⟩))

lemma nx_perm (σ : Equiv.Perm (Fin 3)) : nx x (u ∘ σ) (v ∘ σ) = nx x u v := by
  ext w
  simp only [mem_nx, Function.comp]
  constructor
  · rintro (h | ⟨t, h⟩ | ⟨t, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨_, h⟩)
    · exact Or.inr (Or.inr ⟨_, h⟩)
  · rintro (h | ⟨t, h⟩ | ⟨t, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨σ.symm t, by simpa using h⟩)
    · exact Or.inr (Or.inr ⟨σ.symm t, by simpa using h⟩)

lemma card_nx (S : Star E x u v) : (nx x u v).card = 7 := by
  unfold nx
  rw [Finset.card_insert_of_notMem, Finset.card_union_of_disjoint,
    Finset.card_image_of_injective _ S.hu, Finset.card_image_of_injective _ S.hv]
  · rfl
  · rw [Finset.disjoint_left]; intro w hw hw'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw hw'
    obtain ⟨i, rfl⟩ := hw; obtain ⟨j, hj⟩ := hw'
    exact S.huv i j hj.symm
  · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, not_or, not_exists]
    exact ⟨fun i h' => S.hxu i h'.symm, fun i h' => S.hxv i h'.symm⟩

lemma top_sub_nx : top u ⊆ nx x u v := by
  intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl <;> exact u_nx _

lemma ed_sub_nx (t : Fin 3) : ed x u v t ⊆ nx x u v := by
  intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact x_nx
  · exact u_nx _
  · exact v_nx _

end Star

/-- A star at `x` all of whose neighbours have degree 2, with second edges `f t ∋ v t`. -/
structure Star2 (E : Finset (Finset α)) (x : α) (u v : Fin 3 → α) (f : Fin 3 → Finset α) :
    Prop where
  S : Star E x u v
  du : ∀ t, deg E (u t) = 2
  dv : ∀ t, deg E (v t) = 2
  hf : ∀ t, f t ∈ E
  vf : ∀ t, v t ∈ f t
  fne : ∀ t, f t ≠ Star.ed x u v t

namespace Star2

open OpenProblemsLab.HY.Star

variable {E : Finset (Finset α)} {x : α} {u v : Fin 3 → α} {f : Fin 3 → Finset α}

lemma _root_.OpenProblemsLab.HY.Star.exists_star2 (S : Star E x u v) (h : MinCex E) {k : Fin 3}
    (huk : deg E (u k) = 2) : ∃ f, Star2 E x u v f := by
  have hall := S.all_deg_two h huk
  have : ∀ t, ∃ g ∈ E, g ≠ ed x u v t ∧ v t ∈ g := fun t => by
    obtain ⟨g, hg, hne, hvg, -⟩ := exists_other_edge (S.he t) (v_ed t) (hall t).2
    exact ⟨g, hg, hne, hvg⟩
  choose f hf hne hvf using this
  exact ⟨f, S, fun t => (hall t).1, fun t => (hall t).2, hf, hvf, hne⟩

lemma perm (T : Star2 E x u v f) (σ : Equiv.Perm (Fin 3)) : Star2 E x (u ∘ σ) (v ∘ σ) (f ∘ σ) :=
  ⟨T.S.perm σ, fun _ => T.du _, fun _ => T.dv _, fun _ => T.hf _, fun _ => T.vf _,
    fun _ => T.fne _⟩

lemma at_v (T : Star2 E x u v f) (t : Fin 3) : ∀ g ∈ E, v t ∈ g → g = ed x u v t ∨ g = f t :=
  eq_or_eq_of_deg_two (T.dv t) (T.S.he t) (T.hf t) (T.fne t).symm (v_ed t) (T.vf t)

lemma x_not_f (T : Star2 E x u v f) (t : Fin 3) : x ∉ f t := fun h' => by
  obtain ⟨m, hm⟩ := T.S.atx _ (T.hf t) h'
  have : t = m := T.S.v_mem_ed.1 (by have := T.vf t; rw [hm] at this; exact this)
  subst this; exact T.fne t hm

lemma f_ne_ed (T : Star2 E x u v f) (t s : Fin 3) : f t ≠ ed x u v s := fun h' =>
  T.x_not_f t (h' ▸ x_ed s)

lemma f_ne_top (T : Star2 E x u v f) (t : Fin 3) : f t ≠ top u := fun h' =>
  T.S.v_not_top t (h' ▸ T.vf t)

lemma u_not_f (T : Star2 E x u v f) (s t : Fin 3) : u s ∉ f t := fun h' => by
  rcases T.S.at_u (T.du s) _ (T.hf t) h' with h'' | h''
  · exact T.f_ne_top t h''
  · exact T.f_ne_ed t s h''

lemma v_mem_f (T : Star2 E x u v f) {s t : Fin 3} (h' : v s ∈ f t) : f t = f s := by
  rcases T.at_v s _ (T.hf t) h' with h'' | h''
  · exact absurd h'' (T.f_ne_ed t s)
  · exact h''

/-- Every edge at a vertex of `N[x]` is `top`, some `eₜ` or some `fₜ`. -/
lemma edges_at (T : Star2 E x u v f) {w : α} (hw : w ∈ nx x u v) {g : Finset α} (hg : g ∈ E)
    (hwg : w ∈ g) : g = top u ∨ (∃ t, g = ed x u v t) ∨ ∃ t, g = f t := by
  rcases mem_nx.1 hw with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact Or.inr (Or.inl (T.S.atx g hg hwg))
  · rcases T.S.at_u (T.du t) g hg hwg with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl ⟨t, h'⟩)
  · rcases T.at_v t g hg hwg with h' | h'
    · exact Or.inr (Or.inl ⟨t, h'⟩)
    · exact Or.inr (Or.inr ⟨t, h'⟩)

lemma f_inter_nx (T : Star2 E x u v f) {t : Fin 3} {w : α} (hw : w ∈ f t) (hwn : w ∈ nx x u v) :
    ∃ s, w = v s ∧ f t = f s := by
  rcases mem_nx.1 hwn with rfl | ⟨s, rfl⟩ | ⟨s, rfl⟩
  · exact absurd hw (T.x_not_f t)
  · exact absurd hw (T.u_not_f s t)
  · exact ⟨s, rfl, T.v_mem_f hw⟩

/-- **Claim 7.2** for the indices `0, 1`. -/
lemma f01 (T : Star2 E x u v f) (h : MinCex E) : f 0 ≠ f 1 := by
  intro h01
  have S := T.S
  have hv2 : v 2 ∉ f 0 := fun h' =>
    S.no_vvv h (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide) (T.hf 0) (T.vf 0)
      (h01 ▸ T.vf 1) h'
  have hf02 : f 0 ≠ f 2 := fun h' => hv2 (h' ▸ T.vf 2)
  set X : Finset α := {u 0, v 1, v 2} with hX
  have hu0 : u 0 ∈ X := by simp [hX]
  have hv1 : v 1 ∈ X := by simp [hX]
  have hv2X : v 2 ∈ X := by simp [hX]
  have meet : ∀ {g : Finset α} {w : α}, w ∈ g → w ∈ X → ¬ Disjoint g X := fun hw hwX =>
    Finset.not_disjoint_iff.2 ⟨_, hw, hwX⟩
  -- every edge at `N[x]` meets `X`
  have hmeet : ∀ g ∈ E, (g = top u ∨ (∃ t, g = ed x u v t) ∨ ∃ t, g = f t) → ¬ Disjoint g X := by
    rintro g - (rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact meet (mem_top 0) hu0
    · fin_cases t
      · exact meet (u_ed 0) hu0
      · exact meet (v_ed 1) hv1
      · exact meet (v_ed 2) hv2X
    · fin_cases t
      · exact meet (h01 ▸ T.vf 1) hv1
      · exact meet (T.vf 1) hv1
      · exact meet (T.vf 2) hv2X
  have hRd : Disjoint (nx x u v) (verts (del E X)) :=
    disjoint_verts_del fun w hw g hg hwg => hmeet g hg (T.edges_at hw hg hwg)
  have hk : hE (del E X) ≤ 1 := by
    have h3 := h.three_hE_le (C := (f 1 \ nx x u v) ∪ (f 2 \ nx x u v)) hRd ?_
    · have c1 := card_sdiff_le_of_two (S.hv.ne (show (0 : Fin 3) ≠ 1 by decide))
        (h01 ▸ T.vf 0) (T.vf 1) (v_nx (x := x) (u := u) 0) (v_nx (x := x) (u := u) 1)
      have c2 := card_sdiff_le_of_one (T.vf 2) (v_nx (x := x) (u := u) 2)
      have := Finset.card_union_le (f 1 \ nx x u v) (f 2 \ nx x u v)
      rw [h.L.card3 _ (T.hf 1)] at c1
      rw [h.L.card3 _ (T.hf 2)] at c2
      omega
    · intro g hg hgX w hwg hwR
      obtain ⟨c, hcg, hcX⟩ := Finset.not_disjoint_iff.1 hgX
      simp only [hX, Finset.mem_insert, Finset.mem_singleton] at hcX
      rcases hcX with rfl | rfl | rfl
      · rcases S.at_u (T.du 0) g hg hcg with rfl | rfl
        · exact absurd (top_sub_nx hwg) hwR
        · exact absurd (ed_sub_nx _ hwg) hwR
      · rcases T.at_v 1 g hg hcg with rfl | rfl
        · exact absurd (ed_sub_nx _ hwg) hwR
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hwg, hwR⟩)
      · rcases T.at_v 2 g hg hcg with rfl | rfl
        · exact absurd (ed_sub_nx _ hwg) hwR
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hwg, hwR⟩)
  have hD := card_six (S.top_ne 0) (S.top_ne 1) (S.top_ne 2) (T.f_ne_top 1).symm
    (T.f_ne_top 2).symm (S.ed_ne (by decide)) (S.ed_ne (by decide)) (T.f_ne_ed 1 0).symm
    (T.f_ne_ed 2 0).symm (S.ed_ne (by decide)) (T.f_ne_ed 1 1).symm (T.f_ne_ed 2 1).symm
    (T.f_ne_ed 1 2).symm (T.f_ne_ed 2 2).symm (h01 ▸ hf02)
  refine h.no_good_del (X := X) (R := nx x u v)
    (D := {top u, ed x u v 0, ed x u v 1, ed x u v 2, f 1, f 2}) 1 ?_ hRd ?_ ⟨top u, by simp⟩ hk ?_
  · intro w hw
    rcases mem_nx.1 hw with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact subset_verts (S.he 0) (x_ed 0)
    · exact S.u_verts t
    · exact S.v_verts t
  · intro g hg
    have hgE : g ∈ E := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [S.htop, S.he 0, S.he 1, S.he 2, T.hf 1, T.hf 2]
    refine mem_hit.2 ⟨hgE, hmeet g hgE ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [Or.inl rfl, Or.inr (Or.inl ⟨0, rfl⟩), Or.inr (Or.inl ⟨1, rfl⟩),
      Or.inr (Or.inl ⟨2, rfl⟩), Or.inr (Or.inr ⟨1, rfl⟩), Or.inr (Or.inr ⟨2, rfl⟩)]
  · rw [S.card_nx, hD]
    have : X.card ≤ 3 := Finset.card_le_three
    omega

/-- **Claim 7.2**: the edges `f t` are distinct. -/
lemma f_inj (T : Star2 E x u v f) (h : MinCex E) : Function.Injective f := by
  intro i j hij
  by_contra hne
  obtain ⟨σ, h0, h1⟩ := exists_perm hne
  exact (T.perm σ).f01 h (by simp [h0, h1, hij])

end Star2

end OpenProblemsLab.HY
