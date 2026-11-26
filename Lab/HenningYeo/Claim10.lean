import Lab.HenningYeo.Claim9
import Lab.HenningYeo.GadgetFacts3
import Lab.HenningYeo.GadgetFacts2

/-!
# Henning–Yeo Claim 10: the minimal counterexample is 3-regular
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-- In a closed copy of `H₁₀`/`H₁₀'`, the two other vertices of the leaf's edge have degree 2. -/
lemma gadget_leaf_mates {G F : Finset (Finset α)} (hF : IsClosed G F) (hgad : IsGadget F) {z : α}
    (hzF : z ∈ verts F) (hz : deg G z = 1) {f : Finset α} (hf : f ∈ G) (hzf : z ∈ f) {p : α}
    (hpf : p ∈ f) (hpz : p ≠ z) : deg G p = 2 := by
  obtain ⟨l, a, b, g, C, rfl⟩ := GCopy.of_gadget hF hgad
  have hv := C.valid
  obtain ⟨i, rfl⟩ := mem_verts_copy hzF
  have hi7 : i = 7 := gadget_leaf_unique l a b hv i (by rw [← C.deg_eq]; exact hz)
  subst hi7
  obtain ⟨f0, hf0, rfl⟩ := C.edge hf hzf
  have hf07 := gadget_edge7 l a b hv f0 hf0 ((image_mem_image_iff C.inj).1 hzf)
  subst hf07
  have h89 := gadget_deg89 l a b hv
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hpf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · exact absurd rfl hpz
  · rw [C.deg_eq]; exact h89.1
  · rw [C.deg_eq]; exact h89.2

/-- Degree before and after deleting a vertex `u`. -/
lemma deg_split {E : Finset (Finset α)} (hL : IsL3 E) {u w : α} (huw : u ≠ w) :
    deg E w = deg (del E {u}) w + if ∃ f ∈ E, u ∈ f ∧ w ∈ f then 1 else 0 := by
  unfold deg
  have hsplit : E.filter (w ∈ ·) = (del E {u}).filter (w ∈ ·) ∪
      E.filter (fun f => u ∈ f ∧ w ∈ f) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_union, mem_del, Finset.disjoint_singleton_right]
    tauto
  have hdisj : Disjoint ((del E {u}).filter (w ∈ ·)) (E.filter (fun f => u ∈ f ∧ w ∈ f)) := by
    rw [Finset.disjoint_left]
    intro f hf hf'
    simp only [Finset.mem_filter, mem_del, Finset.disjoint_singleton_right] at hf hf'
    exact hf.1.2 hf'.2.1
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  congr 1
  split_ifs with hex
  · obtain ⟨f, hf, huf, hwf⟩ := hex
    refine Finset.card_eq_one.2 ⟨f, ?_⟩
    ext f'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hf', hu', hw'⟩; exact hL.eq_of_two hf' hf huw hu' hw' huf hwf
    · rintro rfl; exact ⟨hf, huf, hwf⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro f hf ⟨hu, hw⟩; exact hex ⟨f, hf, hu, hw⟩

namespace MinCex

variable {E : Finset (Finset α)}

lemma star_of_meets (h : MinCex E) {s : α} (hs : deg E s = 3) {w : Finset α} (hwE : w ∈ E)
    (hsw : s ∉ w) (hmeet : ∀ g ∈ E, s ∈ g → ¬ Disjoint w g) :
    ∃ u v : Fin 3 → α, Star E s u v ∧ Star.top u = w := by
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
    Finset.not_disjoint_iff.1 (hmeet _ (hg t).1 (hg t).2)
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
  exact ⟨a, b, S, htop⟩

/-- **Claim 7**, in the form: an edge `w` inside `N(s)` has all its vertices of degree 3. -/
lemma claim7' (h : MinCex E) {s : α} {w : Finset α} (hwE : w ∈ E) (hsw : s ∉ w)
    (hsub : w ⊆ nbr E {s}) : ∀ c ∈ w, deg E c = 3 := by
  have hpick : ∀ c ∈ w, ∃ g, g ∈ E.filter (s ∈ ·) ∧ c ∈ g := fun c hc => by
    have := hsub hc
    rw [nbr, Finset.mem_sdiff] at this
    obtain ⟨g, hg, hcg⟩ := mem_verts.1 this.1
    rw [mem_hit, Finset.disjoint_singleton_right, not_not] at hg
    exact ⟨g, Finset.mem_filter.2 hg, hcg⟩
  choose! φ hφ hcφ using hpick
  have hinj : Set.InjOn φ w := by
    intro c hc c' hc' heq
    by_contra hne
    have hg := Finset.mem_filter.1 (hφ c hc)
    have : w = φ c := h.L.eq_of_two hwE hg.1 hne hc hc' (hcφ c hc) (heq ▸ hcφ c' hc')
    exact hsw (this ▸ hg.2)
  have hcard := Finset.card_le_card_of_injOn φ hφ hinj
  rw [h.L.card3 w hwE] at hcard
  have hs3 : deg E s = 3 := by have := h.claim5 s; unfold deg at *; omega
  have himg : w.image φ = E.filter (s ∈ ·) := by
    apply Finset.eq_of_subset_of_card_le
    · intro g hg; obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hg; exact hφ c hc
    · rw [Finset.card_image_of_injOn hinj, h.L.card3 w hwE]; unfold deg at hs3; omega
  have hmeet : ∀ g ∈ E, s ∈ g → ¬ Disjoint w g := by
    intro g hg hsg
    have : g ∈ w.image φ := himg ▸ Finset.mem_filter.2 ⟨hg, hsg⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 this
    exact Finset.not_disjoint_iff.2 ⟨c, hc, hcφ c hc⟩
  obtain ⟨u, v, S, htop⟩ := h.star_of_meets hs3 hwE hsw hmeet
  intro c hc
  rw [← htop] at hc
  obtain ⟨t, rfl⟩ := S.u_mem_top_iff.1 hc
  exact S.claim7 h t

/-- Some edge has a vertex of degree 3 and a vertex of degree 2 (unless `H` is 3-regular). -/
lemma exists_mixed (h : MinCex E) {y : α} (hy : y ∈ verts E) (hy2 : deg E y = 2) :
    ∃ e ∈ E, ∃ x ∈ e, ∃ z ∈ e, deg E x = 3 ∧ deg E z = 2 := by
  by_contra hno
  push Not at hno
  obtain ⟨v, hv, hv3⟩ := h.claim9
  set F := E.filter (fun e => ∀ c ∈ e, deg E c = 2) with hF
  have hclosed : IsClosed E F := by
    refine ⟨Finset.filter_subset _ _, fun e he hmeet => ?_⟩
    obtain ⟨c, hce, hcF⟩ := Finset.not_disjoint_iff.1 hmeet
    obtain ⟨f, hf, hcf⟩ := mem_verts.1 hcF
    have hc2 := (Finset.mem_filter.1 hf).2 c hcf
    refine Finset.mem_filter.2 ⟨he, fun d hd => ?_⟩
    rcases h.deg_two_or_three (subset_verts he hd) with h2 | h3
    · exact h2
    · exact (hno e he d hd c hce h3 hc2).elim
  obtain ⟨ey, hey, hyey⟩ := mem_verts.1 hy
  have hne : F.Nonempty := ⟨ey, Finset.mem_filter.2 ⟨hey, fun d hd => by
    rcases h.deg_two_or_three (subset_verts hey hd) with h2 | h3
    · exact h2
    · exact absurd hy2 (hno ey hey d hd y hyey h3)⟩⟩
  have := h.closed_eq hclosed hne
  obtain ⟨ev, hev, hvev⟩ := mem_verts.1 hv
  have : ev ∈ F := this ▸ hev
  have := (Finset.mem_filter.1 this).2 v hvev
  omega

lemma mem_nbr_of {f : Finset α} (hf : f ∈ E) {s c : α} (hs : s ∈ f) (hc : c ∈ f) (hcs : c ≠ s) :
    c ∈ nbr E {s} :=
  Finset.mem_sdiff.2 ⟨mem_verts.2 ⟨f, mem_hit.2 ⟨hf, Finset.not_disjoint_iff.2
    ⟨s, hs, Finset.mem_singleton_self s⟩⟩, hc⟩, by simpa using hcs⟩

lemma length_filter_finRange (n : Fin 10 → Bool) :
    ((List.finRange 10).filter n).length = (Finset.univ.filter (fun i => n i = true)).card := by
  rw [Fin.univ_def, Finset.card_def, Finset.filter_val]
  simp [Multiset.filter_coe]

/-- **Claim 10**: the minimal counterexample is 3-regular. -/
lemma claim10 (h : MinCex E) : ∀ v ∈ verts E, deg E v = 3 := by
  by_contra hno
  push Not at hno
  obtain ⟨y0, hy0, hy03⟩ := hno
  have hy02 : deg E y0 = 2 := (h.deg_two_or_three hy0).resolve_right hy03
  obtain ⟨e, he, x, hxe, y, hye, hx3, hy2⟩ := h.exists_mixed hy0 hy02
  have hL := h.L
  obtain ⟨F, hF, hyF, hgad⟩ := h.claim6 hx3 hy2 he hxe hye (h.claim8 x)
  obtain ⟨l, a, b, g, C, rfl⟩ := GCopy.of_gadget hF hgad
  have hv := C.valid
  have hinj := C.inj
  have hRdel : ∀ e0 ∈ gadget l a b, e0.image g ∈ del E {x} := fun e0 he0 =>
    hF.1 (Finset.mem_image_of_mem _ he0)
  have hRE : ∀ e0 ∈ gadget l a b, e0.image g ∈ E := fun e0 he0 => del_subset _ _ (hRdel e0 he0)
  have hgx : ∀ i, g i ≠ x := fun i h' => by
    obtain ⟨f, hf, hif⟩ := mem_verts.1 (C.verts_mem i)
    exact Finset.disjoint_left.1 (mem_del.1 (hF.1 hf)).2 hif (h' ▸ Finset.mem_singleton_self x)
  have hgE : ∀ i, g i ∈ verts E := fun i => by
    obtain ⟨f, hf, hif⟩ := mem_verts.1 (C.verts_mem i)
    exact mem_verts.2 ⟨f, del_subset _ _ (hF.1 hf), hif⟩
  have himg : ∀ {e0 : Finset (Fin 10)} {i : Fin 10}, g i ∈ e0.image g ↔ i ∈ e0 :=
    image_mem_image_iff hinj
  set n : Fin 10 → Bool := fun i => decide (∃ f ∈ E, x ∈ f ∧ g i ∈ f) with hn
  have hdeg : ∀ i, deg E (g i) = tD l a b n i := by
    intro i
    rw [deg_split hL (hgx i).symm, C.deg_eq i, deg_tdg l a b hv i]
    simp [tD, hn]
  -- an edge of `E` through `g v` and `g p`, when `v` is not adjacent to `x`, is a template edge
  have hR_of : ∀ {v p : Fin 10}, n v = false → v ≠ p → (∃ f ∈ E, g v ∈ f ∧ g p ∈ f) →
      tadj l a b v p := by
    intro v p hnv hvp ⟨f, hf, hvf, hpf⟩
    have hxf : x ∉ f := fun hxf => by
      have : n v = true := by simp only [hn, decide_eq_true_eq]; exact ⟨f, hf, hxf, hvf⟩
      rw [hnv] at this; exact absurd this (by decide)
    have hfd : f ∈ del E {x} := mem_del.2 ⟨hf, Finset.disjoint_singleton_right.2 hxf⟩
    obtain ⟨e0, he0, rfl⟩ := C.edge hfd hvf
    obtain ⟨k, hk⟩ := edge_tmem l a b hv e0 he0
    exact ⟨hvp, k, (hk v).1 (himg.1 hvf), (hk p).1 (himg.1 hpf)⟩
  have htadj : ∀ {v p : Fin 10}, tadj l a b v p → ∃ f ∈ E, g v ∈ f ∧ g p ∈ f := by
    rintro v p ⟨-, k, hkv, hkp⟩
    obtain ⟨e0, he0, hmem⟩ := tmem_edge l a b hv k
    exact ⟨e0.image g, hRE e0 he0, himg.2 ((hmem v).2 hkv), himg.2 ((hmem p).2 hkp)⟩
  refine no_P10 hv n ⟨fun i => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- degrees 2 or 3
    rw [← hdeg i]
    rcases h.deg_two_or_three (hgE i) with h2 | h3 <;> omega
  · -- `y = g 7` is adjacent to `x`
    obtain ⟨i, rfl⟩ := mem_verts_copy hyF
    have h1 : deg (del E {x}) (g i) = 1 := by
      have := deg_split hL (hgx i).symm (E := E)
      rw [if_pos ⟨e, he, hxe, hye⟩, hy2] at this
      omega
    have hi7 : i = 7 := gadget_leaf_unique l a b hv i (by rw [← C.deg_eq]; exact h1)
    subst hi7
    simp only [hn, decide_eq_true_eq]
    exact ⟨e, he, hxe, hye⟩
  · -- at most six neighbours
    rw [length_filter_finRange]
    have hsub : (Finset.univ.filter (fun i => n i = true)).image g ⊆ nbr E {x} := by
      intro c hc
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hn, decide_eq_true_eq] at hi
      obtain ⟨f, hf, hxf, hif⟩ := hi
      exact mem_nbr_of hf hxf hif (hgx i)
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at this
    have := card_nbr_singleton_le hL.card3 x
    omega
  · -- Claim 7 at `x`
    intro k hk i hi
    obtain ⟨e0, he0, hmem⟩ := tmem_edge l a b hv k
    rw [← hdeg i]
    refine h.claim7' (s := x) (hRE e0 he0) (fun hx => ?_) (fun c hc => ?_) (g i)
      (himg.2 ((hmem i).2 hi))
    · exact Finset.disjoint_left.1 (mem_del.1 (hRdel e0 he0)).2 hx (Finset.mem_singleton_self x)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hc
      have := hk j ((hmem j).1 hj)
      simp only [hn, decide_eq_true_eq] at this
      obtain ⟨f, hf, hxf, hjf⟩ := this
      exact mem_nbr_of hf hxf hjf (hgx j)
  · -- Claim 7 at template vertices
    intro v k hk i hi
    obtain ⟨e0, he0, hmem⟩ := tmem_edge l a b hv k
    rw [← hdeg i]
    refine h.claim7' (s := g v) (hRE e0 he0) (fun hx => ?_) (fun c hc => ?_) (g i)
      (himg.2 ((hmem i).2 hi))
    · have := hk v ((hmem v).1 (himg.1 hx))
      exact this.1 rfl
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hc
      have hvj := hk j ((hmem j).1 hj)
      obtain ⟨f, hf, hvf, hjf⟩ := htadj hvj
      exact mem_nbr_of hf hvf hjf (hinj.ne hvj.1).symm
  · -- Claim 6 at template vertices
    intro v hnv hv3 z hvz hnz hz2 k hkz hkv p hkp hpz
    have hgv3 : deg E (g v) = 3 := by rw [hdeg v]; exact hv3
    have hgz2 : deg E (g z) = 2 := by rw [hdeg z]; simp [tD, hnz, hz2]
    obtain ⟨f1, hf1, hvf1, hzf1⟩ := htadj hvz
    obtain ⟨F', hF', hzF', hgad'⟩ := h.claim6 hgv3 hgz2 hf1 hvf1 hzf1 (h.claim8 (g v))
    have hvz' : g v ≠ g z := hinj.ne hvz.1
    have hz1 : deg (del E {g v}) (g z) = 1 := by
      have := deg_split hL hvz'
      rw [if_pos ⟨f1, hf1, hvf1, hzf1⟩, hgz2] at this
      omega
    obtain ⟨e0, he0, hmem⟩ := tmem_edge l a b hv k
    have hvk : g v ∉ e0.image g := fun h' => by
      have := (hmem v).1 (himg.1 h'); rw [hkv] at this; exact absurd this (by decide)
    have hfd : e0.image g ∈ del E {g v} :=
      mem_del.2 ⟨hRE e0 he0, Finset.disjoint_singleton_right.2 hvk⟩
    have hp2 := gadget_leaf_mates hF' hgad' hzF' hz1 hfd (himg.2 ((hmem z).2 hkz))
      (himg.2 ((hmem p).2 hkp)) (hinj.ne hpz)
    have hvp : v ≠ p := fun h' => by rw [h', hkp] at hkv; exact absurd hkv (by decide)
    rw [← hdeg p, deg_split hL (hinj.ne hvp), hp2]
    congr 1
    by_cases hadj : tadj l a b v p
    · rw [if_pos hadj, if_pos (htadj hadj)]
    · rw [if_neg hadj, if_neg (fun h' => hadj (hR_of hnv hvp h'))]

end MinCex

end OpenProblemsLab.HY
