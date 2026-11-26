import Lab.HenningYeo.Star2

/-!
# Henning–Yeo Claim 7.3: the vertices of `S` have degree 2

We also build a star from an isolated edge of `H - s` (used again in Claim 8).
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

lemma exists_third_of_card3 {e : Finset α} (he : e.card = 3) {p q : α} (hp : p ∈ e) (hq : q ∈ e)
    (hpq : p ≠ q) : ∃ r, e = {p, q, r} ∧ r ≠ p ∧ r ≠ q := by
  have h2 : ({p, q} : Finset α) ⊆ e := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> assumption
  have : (e \ {p, q}).card = 1 := by
    rw [Finset.card_sdiff_of_subset h2, he, Finset.card_pair hpq]
  obtain ⟨r, hr⟩ := Finset.card_eq_one.1 this
  have hrf : r ∈ e \ {p, q} := hr ▸ Finset.mem_singleton_self r
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hrf
  refine ⟨r, ?_, hrf.2.1, hrf.2.2⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hrf.1
  · rw [he, Finset.card_eq_three.2 ⟨p, q, r, hpq, Ne.symm hrf.2.1, Ne.symm hrf.2.2, rfl⟩]

lemma deg_eq_two_of {E : Finset (Finset α)} {a : α} {e₁ e₂ : Finset α} (h1 : e₁ ∈ E) (h2 : e₂ ∈ E)
    (hne : e₁ ≠ e₂) (ha1 : a ∈ e₁) (ha2 : a ∈ e₂) (hall : ∀ g ∈ E, a ∈ g → g = e₁ ∨ g = e₂) :
    deg E a = 2 := by
  unfold deg
  rw [show E.filter (a ∈ ·) = {e₁, e₂} by
    ext g
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hg, hag⟩; exact hall g hg hag
    · rintro (rfl | rfl) <;> simp_all]
  exact Finset.card_pair hne

lemma deg_del_le (E : Finset (Finset α)) (X : Finset α) (w : α) : deg (del E X) w ≤ deg E w :=
  deg_mono (del_subset E X) w

namespace MinCex

variable {E : Finset (Finset α)}

/-- An isolated edge `w` of `H - s` with `deg s = 3` is the top edge of a star at `s`, and its
vertices have degree 2. -/
lemma star_of_iso (h : MinCex E) {s : α} (hs : deg E s = 3) {w : Finset α}
    (hw : w ∈ isoEdges (del E {s})) :
    ∃ u v : Fin 3 → α, Star E s u v ∧ Star.top u = w ∧ ∀ t, deg E (u t) = 2 := by
  have hwd := isoEdges_subset _ hw
  have hwE := del_subset _ _ hwd
  have hsw : s ∉ w := fun h' =>
    Finset.disjoint_left.1 (mem_del.1 hwd).2 h' (Finset.mem_singleton_self s)
  have hL := h.L
  obtain ⟨g, hginj, hg, hgall⟩ : ∃ g : Fin 3 → Finset α, Function.Injective g ∧
      (∀ t, g t ∈ E ∧ s ∈ g t) ∧ ∀ e ∈ E, s ∈ e → ∃ t, e = g t := by
    unfold deg at hs
    obtain ⟨g1, g2, g3, h12, h13, h23, heq⟩ := Finset.card_eq_three.1 hs
    have hmem : ∀ e, e ∈ E ∧ s ∈ e ↔ e = g1 ∨ e = g2 ∨ e = g3 := fun e => by
      rw [← Finset.mem_filter (p := (s ∈ ·)), heq]; simp
    refine ⟨![g1, g2, g3], ?_, ?_, ?_⟩
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · intro t; fin_cases t <;> simp [hmem]
    · intro e he hse
      rcases (hmem e).1 ⟨he, hse⟩ with rfl | rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hwg : ∀ t, w ≠ g t := fun t h' => hsw (h' ▸ (hg t).2)
  have hmeet : ∀ t, ∃ a, a ∈ w ∧ a ∈ g t := fun t =>
    Finset.not_disjoint_iff.1 (h.iso_meets_each hs hw (hg t).1 (hg t).2)
  choose a haw hag using hmeet
  have has : ∀ t, a t ≠ s := fun t h' => hsw (h' ▸ haw t)
  have hthird : ∀ t, ∃ b, g t = {s, a t, b} ∧ b ≠ s ∧ b ≠ a t := fun t =>
    exists_third_of_card3 (hL.card3 _ (hg t).1) (hg t).2 (hag t) (Ne.symm (has t))
  choose b hgb hbs hba using hthird
  have hainj : Function.Injective a := fun i j hij =>
    hginj (hL.eq_of_two (hg i).1 (hg j).1 (has i) (hag i) (hg i).2 (hij ▸ hag j) (hg j).2)
  have hbinj : Function.Injective b := by
    intro i j hij
    have hbi : b i ∈ g i := by rw [hgb i]; simp
    have hbj : b j ∈ g j := by rw [hgb j]; simp
    exact hginj (hL.eq_of_two (hg i).1 (hg j).1 (hbs i) hbi (hg i).2 (hij ▸ hbj) (hg j).2)
  have hab : ∀ i j, a i ≠ b j := by
    intro i j hij
    by_cases hij' : i = j
    · subst hij'; exact hba i hij.symm
    · have hbj : b j ∈ g j := by rw [hgb j]; simp
      exact hwg j (hL.eq_of_two hwE (hg j).1 (hainj.ne hij') (haw i) (haw j) (hij ▸ hbj) (hag j))
  have htop : ({a 0, a 1, a 2} : Finset α) = w := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc; simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl <;> exact haw _
    · rw [hL.card3 _ hwE, Finset.card_eq_three.2 ⟨a 0, a 1, a 2, hainj.ne (by decide),
        hainj.ne (by decide), hainj.ne (by decide), rfl⟩]
  have S : Star E s a b :=
    { hu := hainj
      hv := hbinj
      huv := hab
      hxu := fun t => (has t).symm
      hxv := fun t => (hbs t).symm
      he := fun t => hgb t ▸ (hg t).1
      htop := htop ▸ hwE
      atx := fun e he hse => by
        obtain ⟨t, rfl⟩ := hgall e he hse
        exact ⟨t, hgb t⟩ }
  refine ⟨a, b, S, htop, fun t => ?_⟩
  refine deg_eq_two_of hwE (hg t).1 (hwg t) (haw t) (hag t) fun e he hae => ?_
  by_cases hse : s ∈ e
  · obtain ⟨m, rfl⟩ := hgall e he hse
    by_cases hmt : m = t
    · exact Or.inr (hmt ▸ rfl)
    · exact absurd (hL.eq_of_two hwE (hg m).1 (hainj.ne (Ne.symm hmt)) (haw t) (haw m) hae
        (hag m)) (hwg m)
  · by_contra hne
    push Not at hne
    have hed : e ∈ del E {s} := mem_del.2 ⟨he, Finset.disjoint_singleton_right.2 hse⟩
    exact Finset.disjoint_left.1 ((Finset.mem_filter.1 hw).2 e hed hne.1) (haw t) hae

end MinCex

namespace Star2

open OpenProblemsLab.HY.Star

variable {E : Finset (Finset α)} {x : α} {u v : Fin 3 → α} {f : Fin 3 → Finset α}

/-- An edge avoiding `x` and different from `top` meets `N(x)` in at most one vertex. -/
lemma card_inter_nx_le (T : Star2 E x u v f) (h : MinCex E) {r : Finset α} (hr : r ∈ E)
    (hxr : x ∉ r) (hrt : r ≠ top u) : (r ∩ nx x u v).card ≤ 1 := by
  have key : ∀ c ∈ r ∩ nx x u v, ∃ m, c = v m ∧ r = f m := by
    intro c hc
    rw [Finset.mem_inter] at hc
    rcases mem_nx.1 hc.2 with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact absurd hc.1 hxr
    · rcases T.S.at_u (T.du m) r hr hc.1 with h' | h'
      · exact absurd h' hrt
      · exact absurd (h' ▸ x_ed m) hxr
    · rcases T.at_v m r hr hc.1 with h' | h'
      · exact absurd (h' ▸ x_ed m) hxr
      · exact ⟨m, rfl, h'⟩
  refine Finset.card_le_one.2 fun c hc c' hc' => ?_
  obtain ⟨m, rfl, hm⟩ := key c hc
  obtain ⟨m', rfl, hm'⟩ := key c' hc'
  rw [T.f_inj h (hm.symm.trans hm')]

lemma not_nx_of_f (T : Star2 E x u v f) (h : MinCex E) {t : Fin 3} {s : α} (hs : s ∈ f t)
    (hsv : s ≠ v t) : s ∉ nx x u v := fun hn => by
  obtain ⟨m, rfl, hm⟩ := T.f_inter_nx hs hn
  exact hsv (by rw [T.f_inj h hm])

lemma nbr_nx_sub (S : Star E x u v) {w : α} (hw : w ∈ verts (hit E {x})) : w ∈ nx x u v := by
  obtain ⟨g, hg, hwg⟩ := mem_verts.1 hw
  rw [mem_hit, Finset.disjoint_singleton_right, not_not] at hg
  obtain ⟨m, rfl⟩ := S.atx g hg.1 hg.2
  exact ed_sub_nx m hwg

/-- **Claim 7.3**: every vertex of `S = (f₀ ∪ f₁ ∪ f₂) \ {v₀, v₁, v₂}` has degree 2. -/
lemma deg_S (T : Star2 E x u v f) (h : MinCex E) {t : Fin 3} {s : α} (hs : s ∈ f t)
    (hsv : s ≠ v t) : deg E s = 2 := by
  have S := T.S
  have hsn := T.not_nx_of_f h hs hsv
  rcases h.deg_two_or_three (subset_verts (T.hf t) hs) with h2 | h3
  · exact h2
  exfalso
  have hmd : ∀ {g : Finset α}, g ⊆ nx x u v → g ∈ E → g ∈ del E {s} := fun hgn hg =>
    mem_del.2 ⟨hg, Finset.disjoint_singleton_right.2 fun h' => hsn (hgn h')⟩
  have hsx : s ≠ x := fun h' => hsn (h' ▸ x_nx)
  -- Step 1: `H - s` has an isolated edge.
  have hpos : hE (del E {s}) ≠ 0 := by
    intro h0
    obtain ⟨F, hF, hvF, hgad⟩ := h.claim6 h3 (T.dv t) (T.hf t) hs (T.vf t) h0
    have hdv : deg (del E {s}) (v t) = 1 := by
      refine (deg_eq_one_iff (hmd (ed_sub_nx t) (S.he t)) (v_ed t)).2 fun g hg hvg => ?_
      rcases T.at_v t g (del_subset _ _ hg) hvg with h' | h'
      · exact h'
      · exact absurd (h' ▸ hs) (Finset.disjoint_singleton_right.1 (mem_del.1 hg).2)
    obtain ⟨i, -, hti, -, -⟩ := exists_others t
    obtain ⟨-, -, c, hci, hct, hc3⟩ := gadget_leaf hF hgad hvF hdv (hmd (ed_sub_nx t) (S.he t))
      (v_ed t) (x_ed t) (u_ed t) (S.hxv t) (S.huv t t) (S.hxu t)
      (hmd (ed_sub_nx i) (S.he i)) (x_ed i) (S.ed_ne (Ne.symm hti)) (hmd top_sub_nx S.htop)
      (mem_top t) (S.top_ne t)
    obtain ⟨m, rfl⟩ := S.u_mem_top_iff.1 hct
    have := deg_del_le E {s} (u m)
    rw [T.du m] at this
    omega
  obtain ⟨w, hw⟩ : (isoEdges (del E {s})).Nonempty := Finset.card_pos.1 (Nat.pos_of_ne_zero hpos)
  -- Step 2: the star at `s`.
  obtain ⟨u', v', S', htw, hdu'⟩ := h.star_of_iso h3 hw
  obtain ⟨f', T'⟩ := S'.exists_star2 h (hdu' 0)
  -- Step 3: reduce by deleting `{x, s}`.
  set X : Finset α := {x, s} with hX
  have hedX : ∀ m, ¬ Disjoint (ed x u v m) X := fun m =>
    Finset.not_disjoint_iff.2 ⟨x, x_ed m, by simp [hX]⟩
  have hed'X : ∀ m, ¬ Disjoint (ed s u' v' m) X := fun m =>
    Finset.not_disjoint_iff.2 ⟨s, x_ed m, by simp [hX]⟩
  have hsed : ∀ m, s ∉ ed x u v m := fun m h' => hsn (ed_sub_nx m h')
  have hxed' : ∀ m, x ∉ ed s u' v' m := fun m h' => by
    obtain ⟨m', hm'⟩ := S.atx _ (S'.he m) h'
    exact hsed m' (show s ∈ ({x, u m', v m'} : Finset α) by rw [← hm']; simp)
  have hne : ∀ m m', ed x u v m ≠ ed s u' v' m' := fun m m' h' => hsed m (h' ▸ x_ed m')
  have hD := card_six (S.ed_ne (by decide : (0 : Fin 3) ≠ 1)) (S.ed_ne (by decide))
    (hne 0 0) (hne 0 1) (hne 0 2) (S.ed_ne (by decide)) (hne 1 0) (hne 1 1) (hne 1 2)
    (hne 2 0) (hne 2 1) (hne 2 2) (S'.ed_ne (by decide)) (S'.ed_ne (by decide))
    (S'.ed_ne (by decide))
  have hvt : v t ≠ s := Ne.symm hsv
  have hRd : Disjoint ({x, s, v t} : Finset α) (verts (del E X)) := by
    refine disjoint_verts_del fun c hc g hg hcg => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact Finset.not_disjoint_iff.2 ⟨c, hcg, by simp [hX]⟩
    · exact Finset.not_disjoint_iff.2 ⟨c, hcg, by simp [hX]⟩
    · rcases T.at_v t g hg hcg with rfl | rfl
      · exact hedX t
      · exact Finset.not_disjoint_iff.2 ⟨s, hs, by simp [hX]⟩
  have hk : hE (del E X) ≤ 2 := by
    by_contra hk
    push Not at hk
    obtain ⟨r, hr, hrn⟩ : ∃ r ∈ isoEdges (del E X), r ∉ ({top u, w} : Finset (Finset α)) := by
      by_contra hc
      push Not at hc
      have := Finset.card_le_card (show isoEdges (del E X) ⊆ {top u, w} from hc)
      have := Finset.card_le_two (a := top u) (b := w)
      unfold hE at hk
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrn
    have hrd := isoEdges_subset _ hr
    have hrE := del_subset _ _ hrd
    have hrX := (mem_del.1 hrd).2
    have hxr : x ∉ r := fun h' => Finset.disjoint_left.1 hrX h' (by simp [hX])
    have hsr : s ∉ r := fun h' => Finset.disjoint_left.1 hrX h' (by simp [hX])
    have c1 := T.card_inter_nx_le h hrE hxr hrn.1
    have c2 := T'.card_inter_nx_le h hrE hsr (htw ▸ hrn.2)
    have hsub : r ⊆ (r ∩ nx x u v) ∪ (r ∩ nx s u' v') := by
      intro c hc
      have hcn := h.iso_sub_nbr hr hc
      rw [nbr, Finset.mem_sdiff] at hcn
      obtain ⟨g, hg, hcg⟩ := mem_verts.1 hcn.1
      rw [mem_hit] at hg
      obtain ⟨d, hdg, hdX⟩ := Finset.not_disjoint_iff.1 hg.2
      simp only [hX, Finset.mem_insert, Finset.mem_singleton] at hdX
      rcases hdX with rfl | rfl
      · obtain ⟨m, rfl⟩ := S.atx g hg.1 hdg
        exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hc, ed_sub_nx m hcg⟩)
      · obtain ⟨m, rfl⟩ := S'.atx g hg.1 hdg
        exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hc, ed_sub_nx m hcg⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [h.L.card3 r hrE] at this
    omega
  refine h.no_good_del (X := X) (R := {x, s, v t})
    (D := {ed x u v 0, ed x u v 1, ed x u v 2, ed s u' v' 0, ed s u' v' 1, ed s u' v' 2}) 2
    ?_ hRd ?_ ⟨ed x u v 0, by simp⟩ hk ?_
  · intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact subset_verts (S.he 0) (x_ed 0)
    · exact subset_verts (T.hf t) hs
    · exact S.v_verts t
  · intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [mem_hit.2 ⟨S.he 0, hedX 0⟩, mem_hit.2 ⟨S.he 1, hedX 1⟩, mem_hit.2 ⟨S.he 2, hedX 2⟩,
      mem_hit.2 ⟨S'.he 0, hed'X 0⟩, mem_hit.2 ⟨S'.he 1, hed'X 1⟩, mem_hit.2 ⟨S'.he 2, hed'X 2⟩]
  · rw [hD, Finset.card_eq_three.2 ⟨x, s, v t, Ne.symm hsx, S.hxv t, hvt.symm, rfl⟩]
    have : X.card ≤ 2 := Finset.card_le_two
    omega

end Star2

end OpenProblemsLab.HY
