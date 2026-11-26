import Lab.HenningYeo.Gadget

/-!
# Henning–Yeo Claim 7, first part (Claim 7.1)

A *star* at `x`: the three edges `{x, uᵢ, vᵢ}` at `x` together with an edge `{u₀, u₁, u₂}`.
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-! ### General helpers -/

lemma eq_or_eq_of_deg_two {E : Finset (Finset α)} {w : α} (hd : deg E w = 2) {a b : Finset α}
    (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b) (hwa : w ∈ a) (hwb : w ∈ b) :
    ∀ g ∈ E, w ∈ g → g = a ∨ g = b := by
  intro g hg hwg
  have hsub : ({a, b} : Finset (Finset α)) ⊆ E.filter (w ∈ ·) := by
    intro f hf; simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact Finset.mem_filter.2 ⟨ha, hwa⟩
    · exact Finset.mem_filter.2 ⟨hb, hwb⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by unfold deg at hd; rw [hd, Finset.card_pair hab])
  have : g ∈ E.filter (w ∈ ·) := Finset.mem_filter.2 ⟨hg, hwg⟩
  rw [← heq] at this
  simpa using this

lemma deg_del_lt {E : Finset (Finset α)} {X : Finset α} {w : α} {g : Finset α} (hg : g ∈ E)
    (hwg : w ∈ g) (hgX : ¬ Disjoint g X) : deg (del E X) w < deg E w := by
  unfold deg
  refine Finset.card_lt_card (Finset.ssubset_iff_of_subset
    (Finset.filter_subset_filter _ (del_subset E X)) |>.2 ⟨g, Finset.mem_filter.2 ⟨hg, hwg⟩, ?_⟩)
  intro h'
  exact hgX (mem_del.1 (Finset.mem_filter.1 h').1).2

lemma fin3_cases {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (t : Fin 3) :
    t = i ∨ t = j ∨ t = k := by omega

namespace MinCex

variable {E : Finset (Finset α)}

lemma deg_two_or_three (h : MinCex E) {w : α} (hw : w ∈ verts E) : deg E w = 2 ∨ deg E w = 3 := by
  have h1 : 1 ≤ deg E w := by
    obtain ⟨g, hg, hwg⟩ := mem_verts.1 hw
    exact deg_pos_of_mem hg hwg
  have := h.claim5 w
  have := h.claim4 w
  omega

/-- If `deg v = 3`, an isolated edge of `H - v` meets every edge at `v`. -/
lemma iso_meets_each (h : MinCex E) {v : α} (hv : deg E v = 3) {f : Finset α}
    (hf : f ∈ isoEdges (del E {v})) {g : Finset α} (hg : g ∈ E) (hvg : v ∈ g) :
    ¬ Disjoint f g := by
  intro hdis
  have hfE := del_subset _ _ (isoEdges_subset _ hf)
  have hvf : v ∉ f := fun h' =>
    Finset.disjoint_left.1 (mem_del.1 (isoEdges_subset _ hf)).2 h' (Finset.mem_singleton_self v)
  have hsub : f ⊆ ((E.filter (v ∈ ·)).erase g).biUnion (fun g' => f ∩ g') := by
    intro w hw
    have hwn := h.iso_sub_nbr hf hw
    rw [nbr, Finset.mem_sdiff] at hwn
    obtain ⟨g', hg', hwg'⟩ := mem_verts.1 hwn.1
    rw [mem_hit, Finset.disjoint_singleton_right, not_not] at hg'
    refine Finset.mem_biUnion.2 ⟨g', Finset.mem_erase.2 ⟨fun h' => ?_,
      Finset.mem_filter.2 ⟨hg'.1, hg'.2⟩⟩, Finset.mem_inter.2 ⟨hw, hwg'⟩⟩
    subst h'; exact Finset.disjoint_left.1 hdis hw hwg'
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∑ g' ∈ (E.filter (v ∈ ·)).erase g, (f ∩ g').card ≤
      ∑ _g' ∈ (E.filter (v ∈ ·)).erase g, 1 := by
    refine Finset.sum_le_sum fun g' hg' => ?_
    have hg'' := Finset.mem_filter.1 (Finset.mem_of_mem_erase hg')
    exact h.L.linear f hfE g' hg''.1 (fun h' => hvf (h' ▸ hg''.2))
  rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem
    (Finset.mem_filter.2 ⟨hg, hvg⟩)] at h2
  have := h.L.card3 f hfE
  unfold deg at hv
  omega

end MinCex

/-- A star at `x`. -/
structure Star (E : Finset (Finset α)) (x : α) (u v : Fin 3 → α) : Prop where
  hu : Function.Injective u
  hv : Function.Injective v
  huv : ∀ i j, u i ≠ v j
  hxu : ∀ i, x ≠ u i
  hxv : ∀ i, x ≠ v i
  he : ∀ i, ({x, u i, v i} : Finset α) ∈ E
  htop : ({u 0, u 1, u 2} : Finset α) ∈ E
  atx : ∀ g ∈ E, x ∈ g → ∃ i, g = {x, u i, v i}

namespace Star

variable {E : Finset (Finset α)} {x : α} {u v : Fin 3 → α}

/-- The edge `eᵢ = {x, uᵢ, vᵢ}`. -/
abbrev ed (x : α) (u v : Fin 3 → α) (i : Fin 3) : Finset α := {x, u i, v i}
/-- The edge `{u₀, u₁, u₂}`. -/
abbrev top (u : Fin 3 → α) : Finset α := {u 0, u 1, u 2}

lemma mem_top (i : Fin 3) : u i ∈ top u := by fin_cases i <;> simp

lemma u_mem_top_iff (_S : Star E x u v) {w : α} : w ∈ top u ↔ ∃ i, w = u i := by
  constructor
  · intro hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · rintro ⟨i, rfl⟩; exact mem_top i

lemma x_not_top (S : Star E x u v) : x ∉ top u := fun h' => by
  obtain ⟨i, hi⟩ := S.u_mem_top_iff.1 h'; exact S.hxu i hi

lemma v_not_top (S : Star E x u v) (i : Fin 3) : v i ∉ top u := fun h' => by
  obtain ⟨j, hj⟩ := S.u_mem_top_iff.1 h'; exact S.huv j i hj.symm

lemma x_ed (i : Fin 3) : x ∈ ed x u v i := by simp
lemma u_ed (i : Fin 3) : u i ∈ ed x u v i := by simp
lemma v_ed (i : Fin 3) : v i ∈ ed x u v i := by simp

lemma u_mem_ed (S : Star E x u v) {i j : Fin 3} : u i ∈ ed x u v j ↔ i = j := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h' | h' | h')
    · exact absurd h'.symm (S.hxu i)
    · exact S.hu h'
    · exact absurd h' (S.huv i j)
  · rintro rfl; simp

lemma v_mem_ed (S : Star E x u v) {i j : Fin 3} : v i ∈ ed x u v j ↔ i = j := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h' | h' | h')
    · exact absurd h'.symm (S.hxv i)
    · exact absurd h'.symm (S.huv j i)
    · exact S.hv h'
  · rintro rfl; simp

lemma ed_ne (S : Star E x u v) {i j : Fin 3} (hij : i ≠ j) : ed x u v i ≠ ed x u v j := fun h' =>
  hij (S.u_mem_ed.1 (h' ▸ u_ed i))

lemma top_ne (S : Star E x u v) (i : Fin 3) : top u ≠ ed x u v i := fun h' =>
  S.x_not_top (h' ▸ x_ed i)

lemma deg_x (S : Star E x u v) : deg E x = 3 := by
  unfold deg
  have : E.filter (x ∈ ·) = Finset.univ.image (ed x u v) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hg, hxg⟩; obtain ⟨i, rfl⟩ := S.atx g hg hxg; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨S.he i, x_ed i⟩
  rw [this, Finset.card_image_of_injective _ (fun i j h' => by
    by_contra hij; exact S.ed_ne hij h')]
  rfl

/-- When `deg uᵢ = 2`, the edges at `uᵢ` are `top` and `eᵢ`. -/
lemma at_u (S : Star E x u v) {i : Fin 3} (hd : deg E (u i) = 2) :
    ∀ g ∈ E, u i ∈ g → g = top u ∨ g = ed x u v i :=
  eq_or_eq_of_deg_two hd S.htop (S.he i) (S.top_ne i) (mem_top i) (u_ed i)

lemma u_verts (S : Star E x u v) (i : Fin 3) : u i ∈ verts E := subset_verts (S.he i) (u_ed i)
lemma v_verts (S : Star E x u v) (i : Fin 3) : v i ∈ verts E := subset_verts (S.he i) (v_ed i)


lemma exists_others (i : Fin 3) : ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  fin_cases i
  · exact ⟨1, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide⟩

lemma ed_inter (S : Star E x u v) {j k : Fin 3} (hjk : j ≠ k) {c : α} (hj : c ∈ ed x u v j)
    (hk : c ∈ ed x u v k) : c = x := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · rfl
  · exact absurd (S.u_mem_ed.1 hk) hjk
  · exact absurd (S.v_mem_ed.1 hk) hjk

lemma ed_meet (j k : Fin 3) : ¬ Disjoint (ed x u v j) (ed x u v k) :=
  Finset.not_disjoint_iff.2 ⟨x, x_ed j, x_ed k⟩

lemma top_meet (j : Fin 3) : ¬ Disjoint (top u) (ed x u v j) :=
  Finset.not_disjoint_iff.2 ⟨u j, mem_top j, u_ed j⟩

/-- **Claim 7.1 (a)**: in a star of a minimal counterexample, `deg uᵢ = 2` forces `deg vᵢ = 2`. -/
lemma v_deg_two (S : Star E x u v) (h : MinCex E) {i : Fin 3} (hui : deg E (u i) = 2) :
    deg E (v i) = 2 := by
  rcases h.deg_two_or_three (S.v_verts i) with h2 | h3
  · exact h2
  exfalso
  obtain ⟨j, k, hij, hik, hjk⟩ := exists_others i
  have hmem : ∀ g ∈ E, v i ∉ g → g ∈ del E {v i} := fun g hg hvg =>
    mem_del.2 ⟨hg, Finset.disjoint_singleton_right.2 hvg⟩
  have hj := hmem _ (S.he j) (fun h' => hij (S.v_mem_ed.1 h'))
  have hk := hmem _ (S.he k) (fun h' => hik (S.v_mem_ed.1 h'))
  have ht := hmem _ S.htop (S.v_not_top i)
  have hdu : deg (del E {v i}) (u i) = 1 := by
    refine (deg_eq_one_iff ht (mem_top i)).2 fun g hg hug => ?_
    rcases S.at_u hui g (del_subset _ _ hg) hug with h' | h'
    · exact h'
    · exact absurd (h' ▸ v_ed i) (Finset.disjoint_singleton_right.1 (mem_del.1 hg).2)
  have h0 : hE (del E {v i}) = 0 := by
    by_contra h0
    obtain ⟨f, hf⟩ : (isoEdges (del E {v i})).Nonempty := Finset.card_pos.1 (Nat.pos_of_ne_zero h0)
    obtain ⟨w, hwf, hwe⟩ := Finset.not_disjoint_iff.1 (h.iso_meets_each h3 hf (S.he i) (v_ed i))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwe
    rcases hwe with rfl | rfl | rfl
    · exact not_mem_iso_of_meet hj hk (S.ed_ne hjk) (ed_meet j k) (x_ed j) f hf hwf
    · exact not_mem_iso_of_meet ht hj (S.top_ne j) (top_meet j) (mem_top i) f hf hwf
    · exact Finset.disjoint_left.1 (mem_del.1 (isoEdges_subset _ hf)).2 hwf
        (Finset.mem_singleton_self _)
  obtain ⟨F, hF, huF, hgad⟩ := h.claim6 h3 hui (S.he i) (v_ed i) (u_ed i) h0
  obtain ⟨-, -, c, hcj, hck, hc3⟩ := gadget_leaf hF hgad huF hdu ht (mem_top i) (mem_top j)
    (mem_top k) (fun h' => hij (S.hu h').symm) (fun h' => hik (S.hu h').symm)
    (fun h' => hjk (S.hu h')) hj (u_ed j) (S.top_ne j).symm hk (u_ed k) (S.top_ne k).symm
  have hcx := S.ed_inter hjk hcj hck
  subst hcx
  have := deg_del_lt (S.he i) (x_ed i) (Finset.not_disjoint_iff.2
    ⟨v i, v_ed i, Finset.mem_singleton_self _⟩)
  rw [S.deg_x] at this
  omega

lemma exists_third (t j : Fin 3) : ∃ s, s ≠ t ∧ s ≠ j := by
  fin_cases t <;> fin_cases j <;> decide

lemma top_eq {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ({u i, u j, u k} : Finset α) = top u := by
  ext w
  constructor
  · intro hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> exact mem_top _
  · intro hw; simp only [top, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · rcases fin3_cases hij hik hjk 0 with h | h | h <;> subst h <;> simp
    · rcases fin3_cases hij hik hjk 1 with h | h | h <;> subst h <;> simp
    · rcases fin3_cases hij hik hjk 2 with h | h | h <;> subst h <;> simp

lemma mem_del_u {j : Fin 3} {g : Finset α} (hg : g ∈ E) (hug : u j ∉ g) : g ∈ del E {u j} :=
  mem_del.2 ⟨hg, Finset.disjoint_singleton_right.2 hug⟩

lemma ed_mem_del (S : Star E x u v) {j t : Fin 3} (htj : t ≠ j) : ed x u v t ∈ del E {u j} :=
  mem_del_u (S.he t) fun h' => htj (S.u_mem_ed.1 h').symm

/-- Deleting `u j` of degree 3 leaves no isolated edge. -/
lemma hE_del_u (S : Star E x u v) (h : MinCex E) {j : Fin 3} (hd : deg E (u j) = 3) :
    hE (del E {u j}) = 0 := by
  by_contra h0
  obtain ⟨f, hf⟩ : (isoEdges (del E {u j})).Nonempty := Finset.card_pos.1 (Nat.pos_of_ne_zero h0)
  obtain ⟨w, hwf, hwt⟩ := Finset.not_disjoint_iff.1 (h.iso_meets_each hd hf S.htop (mem_top j))
  obtain ⟨t, rfl⟩ := S.u_mem_top_iff.1 hwt
  have htj : t ≠ j := by
    rintro rfl
    exact Finset.disjoint_left.1 (mem_del.1 (isoEdges_subset _ hf)).2 hwf
      (Finset.mem_singleton_self _)
  obtain ⟨s, hst, hsj⟩ := exists_third t j
  exact not_mem_iso_of_meet (S.ed_mem_del htj) (S.ed_mem_del hsj) (S.ed_ne (Ne.symm hst))
    (ed_meet t s) (u_ed t) f hf hwf

lemma deg_u_del (S : Star E x u v) {j k : Fin 3} (hjk : j ≠ k) (hk : deg E (u k) = 2) :
    deg (del E {u j}) (u k) = 1 := by
  refine (deg_eq_one_iff (S.ed_mem_del (Ne.symm hjk)) (u_ed k)).2 fun g hg hug => ?_
  rcases S.at_u hk g (del_subset _ _ hg) hug with h' | h'
  · exact absurd (h' ▸ mem_top j) (Finset.disjoint_singleton_right.1 (mem_del.1 hg).2)
  · exact h'

/-- No edge contains `vᵢ, vⱼ, vₖ` (it would give an `F₇`). -/
lemma no_vvv (S : Star E x u v) (h : MinCex E) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) {e' : Finset α} (he' : e' ∈ E) (hi : v i ∈ e') (hj : v j ∈ e')
    (hk : v k ∈ e') : False := by
  have hvij : v i ≠ v j := S.hv.ne hij
  have hvik : v i ≠ v k := S.hv.ne hik
  have hvjk : v j ≠ v k := S.hv.ne hjk
  have huij : u i ≠ u j := S.hu.ne hij
  have huik : u i ≠ u k := S.hu.ne hik
  have hujk : u j ≠ u k := S.hu.ne hjk
  have hxi := S.hxu i; have hxj := S.hxu j; have hxk := S.hxu k
  have hyi := S.hxv i; have hyj := S.hxv j; have hyk := S.hxv k
  have h1 := S.huv i i; have h2 := S.huv i j; have h3 := S.huv i k
  have h4 := S.huv j i; have h5 := S.huv j j; have h6 := S.huv j k
  have h7 := S.huv k i; have h8 := S.huv k j; have h9 := S.huv k k
  have he'eq : ({v i, v j, v k} : Finset α) = e' := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    · rw [h.L.card3 e' he', Finset.card_eq_three.2 ⟨v i, v j, v k, hvij, hvik, hvjk, rfl⟩]
  refine h.F7 ![x, u i, v i, u j, v j, u k, v k] ?_ ?_
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> simp_all [eq_comm]
  · simp only [Matrix.cons_val]
    refine ⟨S.he i, S.he j, S.he k, ?_, he'eq ▸ he'⟩
    rw [top_eq hij hik hjk]; exact S.htop

/-- **Claim 7.1, second step.** -/
lemma u_deg_two_of (S : Star E x u v) (h : MinCex E) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (huk : deg E (u k) = 2) {e' : Finset α} (he' : e' ∈ E) (hvk : v k ∈ e')
    (hne : e' ≠ ed x u v k) (hvi : v i ∉ e') : deg E (u j) = 2 := by
  rcases h.deg_two_or_three (S.u_verts j) with h2 | h3
  · exact h2
  exfalso
  obtain ⟨F, hF, huF, hgad⟩ := h.claim6 h3 huk S.htop (mem_top j) (mem_top k) (S.hE_del_u h h3)
  have hdu := S.deg_u_del hjk huk
  have hvk2 := S.v_deg_two h huk
  have hatv := eq_or_eq_of_deg_two hvk2 (S.he k) he' (Ne.symm hne) (v_ed k) hvk
  have hek := S.ed_mem_del (Ne.symm hjk)
  by_cases hj' : u j ∈ e'
  · have hdv : deg (del E {u j}) (v k) = 1 := by
      refine (deg_eq_one_iff hek (v_ed k)).2 fun g hg hvg => ?_
      rcases hatv g (del_subset _ _ hg) hvg with h' | h'
      · exact h'
      · exact absurd (h' ▸ hj') (Finset.disjoint_singleton_right.1 (mem_del.1 hg).2)
    have hekF : ed x u v k ∈ F :=
      hF.2 _ hek (Finset.not_disjoint_iff.2 ⟨u k, u_ed k, huF⟩)
    have hvF : v k ∈ verts F := subset_verts hekF (v_ed k)
    exact S.huv k k (gadget_one_leaf hF hgad huF hvF hdu hdv)
  · obtain ⟨-, -, c, hci, hce, hc3⟩ := gadget_leaf hF hgad huF hdu hek (u_ed k) (x_ed k)
      (v_ed k) (S.hxu k) (S.huv k k).symm (S.hxv k) (S.ed_mem_del hij) (x_ed i)
      (S.ed_ne hik) (mem_del_u he' hj') hvk hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hci
    rcases hci with rfl | rfl | rfl
    · obtain ⟨m, hm⟩ := S.atx e' he' hce
      have : m = k := (S.v_mem_ed.1 (by rw [hm] at hvk; exact hvk)).symm
      subst this; exact hne hm
    · have := deg_del_lt S.htop (mem_top i) (Finset.not_disjoint_iff.2
        ⟨u j, mem_top j, Finset.mem_singleton_self _⟩)
      have := h.claim5 (u i)
      omega
    · exact hvi hce

/-- **Claim 7.1, third step.** -/
lemma u_deg_two_of' (S : Star E x u v) (h : MinCex E) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (huj : deg E (u j) = 2) (huk : deg E (u k) = 2) : deg E (u i) = 2 := by
  rcases h.deg_two_or_three (S.u_verts i) with h2 | h3
  · exact h2
  exfalso
  obtain ⟨F, hF, huF, hgad⟩ := h.claim6 h3 huj S.htop (mem_top i) (mem_top j) (S.hE_del_u h h3)
  have hej := S.ed_mem_del (Ne.symm hij)
  have hek := S.ed_mem_del (Ne.symm hik)
  have hejF : ed x u v j ∈ F := hF.2 _ hej (Finset.not_disjoint_iff.2 ⟨u j, u_ed j, huF⟩)
  have hxF : x ∈ verts F := subset_verts hejF (x_ed j)
  have hekF : ed x u v k ∈ F := hF.2 _ hek (Finset.not_disjoint_iff.2 ⟨x, x_ed k, hxF⟩)
  exact S.hu.ne hjk (gadget_one_leaf hF hgad huF (subset_verts hekF (u_ed k))
    (S.deg_u_del hij huj) (S.deg_u_del hik huk))

/-- **Claim 7.1**: if one `uₖ` has degree 2, every vertex of `N(x)` has degree 2. -/
lemma all_deg_two (S : Star E x u v) (h : MinCex E) {k : Fin 3} (huk : deg E (u k) = 2) :
    ∀ t, deg E (u t) = 2 ∧ deg E (v t) = 2 := by
  obtain ⟨i, j, hki, hkj, hij⟩ := exists_others k
  have hvk2 := S.v_deg_two h huk
  obtain ⟨e', he', hne, hvk, -⟩ := exists_other_edge (S.he k) (v_ed k) hvk2
  have hui : deg E (u i) = 2 ∧ deg E (u j) = 2 := by
    by_cases hvi : v i ∈ e'
    · have hvj : v j ∉ e' := fun hvj => S.no_vvv h hij (Ne.symm hki) (Ne.symm hkj) he' hvi hvj hvk
      have hi := S.u_deg_two_of h (Ne.symm hij) (Ne.symm hkj) (Ne.symm hki) huk he' hvk hne hvj
      exact ⟨hi, S.u_deg_two_of' h (Ne.symm hij) (Ne.symm hkj) (Ne.symm hki) hi huk⟩
    · have hj := S.u_deg_two_of h hij (Ne.symm hki) (Ne.symm hkj) huk he' hvk hne hvi
      exact ⟨S.u_deg_two_of' h hij (Ne.symm hki) (Ne.symm hkj) hj huk, hj⟩
  intro t
  have hu : deg E (u t) = 2 := by
    rcases fin3_cases hki hkj hij t with rfl | rfl | rfl
    · exact huk
    · exact hui.1
    · exact hui.2
  exact ⟨hu, S.v_deg_two h hu⟩

end Star

end OpenProblemsLab.HY
