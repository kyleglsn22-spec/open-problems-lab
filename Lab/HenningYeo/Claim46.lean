import Lab.HenningYeo.F7Copy

/-!
# Henning–Yeo Claim 4.6 and the end of Claim 4

Here `H₃ = (H - {v₁, v₂}) + S₀` contains a copy `R` of `F₇` (lines `ln g k`) with `S₀ = ln g l`,
and `R` is not a union of components of `H₃` (Claim 4.5, proved separately). We show that
`H₃ - r` (`r` the centre of `R`) contains `F₇` (Claim 4.6) and then derive a contradiction.
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-- Pairwise disjoint sets all meeting `S` number at most `|S|`. -/
lemma card_le_of_disjoint_meet {I : Finset (Finset α)}
    (hI : ∀ a ∈ I, ∀ b ∈ I, a ≠ b → Disjoint a b) (S : Finset α)
    (hS : ∀ a ∈ I, (a ∩ S).Nonempty) : I.card ≤ S.card := by
  rcases isEmpty_or_nonempty α with hα | hα
  · rcases I.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp
    · obtain ⟨u, -⟩ := hS a ha; exact (IsEmpty.false u).elim
  choose! f hf using hS
  refine Finset.card_le_card_of_injOn f (fun a ha => (Finset.mem_inter.1 (hf a ha)).2) ?_
  intro a ha b hb hab
  by_contra hne
  have h1 := (Finset.mem_inter.1 (hf a ha)).1
  have h2 := (Finset.mem_inter.1 (hf b hb)).1
  rw [hab] at h1
  exact Finset.disjoint_left.1 (hI a ha b hb hne) h1 h2

/-- Isolated edges of `F - X` avoiding a set `C` of "covered" vertices number at most
`|N(X) \ C|`. -/
lemma hE_del_le {F : Finset (Finset α)} (h0 : hE F = 0) (X C : Finset α)
    (hC : ∀ u ∈ C, ∀ e ∈ isoEdges (del F X), u ∉ e) : hE (del F X) ≤ (nbr F X \ C).card := by
  refine card_le_of_disjoint_meet (fun a ha b hb hab => isoEdges_pairwise ha hb hab) _ ?_
  intro f hf
  obtain ⟨u, huf, hun⟩ := Finset.not_disjoint_iff.1 (iso_del_meets_nbr h0 hf)
  exact ⟨u, Finset.mem_inter.2 ⟨huf, Finset.mem_sdiff.2 ⟨hun, fun huC => hC u huC f hf huf⟩⟩⟩

/-- Counting neighbours of `s` not covered by `C`, when the edges in `B` have their other vertices
in `C`. -/
lemma card_nbr_sdiff_le {F : Finset (Finset α)} (h3 : ∀ e ∈ F, e.card = 3) (s : α)
    {B : Finset (Finset α)} (hB : B ⊆ hit F {s}) (C : Finset α)
    (hBC : ∀ f ∈ B, ∀ u ∈ f, u ≠ s → u ∈ C) :
    (nbr F {s} \ C).card + 2 * B.card ≤ 2 * deg F s := by
  have hsub : nbr F {s} \ C ⊆ (hit F {s} \ B).biUnion (fun f => f.erase s) := by
    intro w hw
    rw [Finset.mem_sdiff, nbr, Finset.mem_sdiff, Finset.mem_singleton] at hw
    obtain ⟨⟨hw1, hws⟩, hwC⟩ := hw
    obtain ⟨f, hf, hwf⟩ := mem_verts.1 hw1
    exact Finset.mem_biUnion.2 ⟨f, Finset.mem_sdiff.2 ⟨hf, fun hfB => hwC (hBC f hfB w hwf hws)⟩,
      Finset.mem_erase.2 ⟨hws, hwf⟩⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∑ f ∈ hit F {s} \ B, (f.erase s).card = ∑ _f ∈ hit F {s} \ B, 2 := by
    refine Finset.sum_congr rfl fun f hf => ?_
    have hf' := (Finset.mem_sdiff.1 hf).1
    rw [mem_hit, Finset.disjoint_singleton_right, not_not] at hf'
    rw [Finset.card_erase_of_mem hf'.2, h3 f hf'.1]
  rw [h2, Finset.sum_const, smul_eq_mul, Finset.card_sdiff_of_subset hB,
    card_hit_singleton] at h1
  have := Finset.card_le_card hB
  rw [card_hit_singleton] at this
  have : B.card * 2 ≤ deg F s * 2 := by omega
  rw [Nat.sub_mul] at h1
  omega

namespace MinCex

variable {E : Finset (Finset α)}

/-- A good hypergraph `E'` of smaller size whose transversals extend by `k` vertices. -/
lemma no_plus (h : MinCex E) {E' : Finset (Finset α)} (k : ℕ) (hs : sz E' < sz E)
    (hL : IsL3 E') (hF : F7Free E')
    (hT : ∀ T, IsTransversal E' T → ∃ T₀ : Finset α, T₀.card ≤ T.card + k ∧ IsTransversal E T₀)
    (hw : wt E' + 17 * k < wt E) : False := by
  obtain ⟨T, hT', hTw⟩ := (h.ih E' hs hL hF).1
  obtain ⟨T₀, hc, hT₀⟩ := hT T hT'
  exact h.no_strict hT₀ (by omega)

end MinCex


/-- The configuration of Claims 4.5–4.6. -/
structure FCfg (E : Finset (Finset α)) (x v₁ v₂ : α) (e₁ e₂ S₀ : Finset α) (g : Fin 7 → α)
    (l : Fin 5) : Prop where
  L : Leaf E x v₁ v₂ e₁ e₂
  h : MinCex E
  hS0 : S₀ ⊆ (e₁ ∪ e₂) \ {v₁, v₂}
  hc : S₀.card = 3
  hg : Function.Injective g
  hln : ∀ k, ln g k ∈ insert S₀ (del E {v₁, v₂})
  hl : ln g l = S₀

/-- The edges of the copy of `F₇` (irreducible: unfolding it makes elaboration compute with
`Finset.univ`). -/
@[irreducible] def cop (g : Fin 7 → α) : Finset (Finset α) := Finset.univ.image (ln g)

lemma mem_cop {g : Fin 7 → α} {f : Finset α} : f ∈ cop g ↔ ∃ k, ln g k = f := by simp [cop]

lemma mem_verts_cop {g : Fin 7 → α} {u : α} : u ∈ verts (cop g) ↔ ∃ i, g i = u := by
  rw [mem_verts]
  constructor
  · rintro ⟨f, hf, huf⟩
    obtain ⟨k, rfl⟩ := mem_cop.1 hf
    obtain ⟨i, -, rfl⟩ := mem_ln_iff.1 huf
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨k, -, hk⟩ := F7_centre_line i
    exact ⟨ln g k, mem_cop.2 ⟨k, rfl⟩, Finset.mem_image_of_mem g hk⟩

namespace FCfg

variable {E : Finset (Finset α)} {x v₁ v₂ : α} {e₁ e₂ S₀ : Finset α} {g : Fin 7 → α} {l : Fin 5}

set_option quotPrecheck false in
local notation "Hs" => del E ({v₁, v₂} : Finset _)
set_option quotPrecheck false in
local notation "H3" => insert S₀ (del E ({v₁, v₂} : Finset _))

lemma S0_not_Hs (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) : S₀ ∉ Hs := by
  intro hS
  have := C.L.claim43 C.h hS
  rw [Finset.inter_eq_left.2 C.hS0, C.hc] at this
  omega

lemma card_H3 (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) : (H3).card = (Hs).card + 1 :=
  Finset.card_insert_of_notMem C.S0_not_Hs

lemma ln_Hs (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) {k : Fin 5} (hk : k ≠ l) : ln g k ∈ Hs := by
  refine (Finset.mem_insert.1 (C.hln k)).resolve_left fun h' => hk ?_
  rw [← C.hl] at h'
  exact (ln_inj C.hg).1 h'

lemma F7_Hs (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) : F7Free (Hs) := C.h.F7.mono (del_subset _ _)

lemma hE_H3 (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) : hE (H3) = 0 := by
  have hsub : isoEdges (H3) ⊆ ∅ := by
    intro f hf
    have hf' := isoEdges_subset _ hf
    rcases Finset.mem_insert.1 hf' with rfl | hfs
    · obtain ⟨k, hkl, hmeet⟩ := F7_meet l
      exfalso; apply hmeet
      rw [← ln_disj C.hg, C.hl]
      exact ((Finset.mem_filter.1 hf).2 _ (C.hln k)
        (fun h' => hkl ((ln_inj C.hg).1 (h'.trans C.hl.symm)))).symm
    · have h0 := C.L.claim42 C.h
      rw [hE, Finset.card_eq_zero] at h0
      have : f ∈ isoEdges (Hs) := Finset.mem_filter.2 ⟨hfs, fun g' hg' hne =>
        (Finset.mem_filter.1 hf).2 g' (Finset.mem_insert_of_mem hg') hne⟩
      rw [h0] at this; exact this
  exact Finset.card_eq_zero.2 (Finset.subset_empty.1 hsub)

lemma L3_H3 (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) : IsL3 (H3) := C.L.H3_L3 C.h C.hS0 C.hc

lemma verts_H3 (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) :
    (verts (H3)).card + 3 ≤ (verts E).card := C.L.card_verts_H3 C.hS0

lemma card_Hs (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) : (Hs).card + 3 = E.card := C.L.card_del12 C.h.L

/-- A transversal of `H₃` containing a vertex of `S₀` extends to `H` by one vertex. -/
lemma cover3 (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) {T : Finset α} (hT : IsTransversal (H3) T)
    {s : α} (hs : s ∈ T) (hsS : s ∈ S₀) : ∃ v, IsTransversal E (insert v T) :=
  C.L.cover (fun f hf => hT f (Finset.mem_insert_of_mem hf)) hs (Finset.mem_sdiff.1 (C.hS0 hsS)).1

lemma wt_E (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) : wt E = 4 * (verts E).card + 4 * E.card :=
  Leaf.wt_eq C.h

lemma g_verts (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) (i : Fin 7) : g i ∈ verts (H3) :=
  mem_verts.2 (by
    obtain ⟨k, -, hk⟩ := F7_centre_line i
    exact ⟨ln g k, C.hln k, Finset.mem_image_of_mem g hk⟩)

lemma sz_lt (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) {F : Finset (Finset α)} (hF : F ⊆ H3) :
    sz F < sz E := by
  have h1 := Finset.card_le_card hF
  have h2 := Finset.card_le_card (verts_mono hF)
  have := C.verts_H3; have := C.card_H3; have := C.card_Hs
  unfold sz; omega


lemma ln_ne (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) {k k' : Fin 5} (h : k ≠ k') : ln g k ≠ ln g k' :=
  fun h' => h ((ln_inj C.hg).1 h')

/-- **Claim 4.6**: if `R` is not a union of components of `H₃`, then `H₃ - r` contains `F₇`. -/
lemma claim46 (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) (hnc : ¬ IsClosed (H3) (cop g)) :
    ¬ F7Free (del (H3) {g 0}) := by
  intro hF
  have hrv : g 0 ∈ verts (H3) := C.g_verts 0
  have hn : (verts (del (H3) {g 0})).card < (verts (H3)).card := card_verts_del_singleton_lt hrv
  have hcd : (del (H3) {g 0}).card + deg (H3) (g 0) = (H3).card := card_del_singleton _ _
  have hlines : ({ln g 0, ln g 1, ln g 2} : Finset (Finset α)) ⊆ (H3).filter (g 0 ∈ ·) := by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl <;>
      exact Finset.mem_filter.2 ⟨C.hln _, (mem_ln C.hg).2 (by decide)⟩
  have h3l : ({ln g 0, ln g 1, ln g 2} : Finset (Finset α)).card = 3 :=
    Finset.card_eq_three.2 ⟨_, _, _, C.ln_ne (by decide), C.ln_ne (by decide), C.ln_ne (by decide),
      rfl⟩
  have hd3 : 3 ≤ deg (H3) (g 0) := by
    unfold deg; rw [← h3l]; exact Finset.card_le_card hlines
  have hl34 : ∀ k : Fin 5, (k = 3 ∨ k = 4) → ln g k ∈ del (H3) {g 0} := by
    rintro k hk
    refine mem_del.2 ⟨C.hln k, Finset.disjoint_singleton_right.2 fun h' => ?_⟩
    rw [mem_ln C.hg] at h'
    rcases hk with rfl | rfl <;> revert h' <;> decide
  set I := isoEdges (del (H3) {g 0}) with hI
  -- an isolated edge meeting `ln g 3 ∪ ln g 4` is one of these lines
  have hsplit : I ⊆ I.filter (fun e => e = ln g 3 ∨ e = ln g 4) ∪
      I.filter (fun e => Disjoint e (ln g 3 ∪ ln g 4)) := by
    intro e he
    by_cases hd : Disjoint e (ln g 3 ∪ ln g 4)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨he, hd⟩)
    · refine Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, ?_⟩)
      obtain ⟨u, hue, hu⟩ := Finset.not_disjoint_iff.1 hd
      have key : ∀ k : Fin 5, (k = 3 ∨ k = 4) → u ∈ ln g k → e = ln g k := by
        intro k hk huk
        by_contra hne
        exact Finset.disjoint_left.1 ((Finset.mem_filter.1 he).2 _ (hl34 k hk) (Ne.symm hne))
          hue huk
      rcases Finset.mem_union.1 hu with hu | hu
      · exact Or.inl (key 3 (Or.inl rfl) hu)
      · exact Or.inr (key 4 (Or.inr rfl) hu)
  have hB : (nbr (H3) {g 0} \ (ln g 3 ∪ ln g 4)).card + 2 * 3 ≤ 2 * deg (H3) (g 0) := by
    rw [← h3l]
    refine card_nbr_sdiff_le C.L3_H3.card3 (g 0) (fun f hf => ?_) _ ?_
    · have := hlines hf
      rw [Finset.mem_filter] at this
      exact mem_hit.2 ⟨this.1, Finset.not_disjoint_iff.2 ⟨g 0, this.2, Finset.mem_singleton_self _⟩⟩
    · intro f hf u huf hu0
      have hf' := hlines hf
      have : ∃ k, f = ln g k := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hf
        rcases hf with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
      obtain ⟨k, rfl⟩ := this
      obtain ⟨i, -, rfl⟩ := mem_ln_iff.1 huf
      have hi : i ≠ 0 := fun h' => hu0 (h' ▸ rfl)
      rcases F7_noncentre i hi with h' | h'
      · exact Finset.mem_union_left _ ((mem_ln C.hg).2 h')
      · exact Finset.mem_union_right _ ((mem_ln C.hg).2 h')
  have h2 : (I.filter (fun e => Disjoint e (ln g 3 ∪ ln g 4))).card ≤
      (nbr (H3) {g 0} \ (ln g 3 ∪ ln g 4)).card := by
    refine card_le_of_disjoint_meet (fun a ha b hb hab =>
      isoEdges_pairwise (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 hb).1 hab) _ ?_
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨u, hue, hun⟩ := Finset.not_disjoint_iff.1 (iso_del_meets_nbr C.hE_H3 he.1)
    exact ⟨u, Finset.mem_inter.2 ⟨hue, Finset.mem_sdiff.2 ⟨hun, Finset.disjoint_left.1 he.2 hue⟩⟩⟩
  -- if both lines `3, 4` are isolated, then `deg r ≥ 4` (else `R` is closed)
  have hboth : ln g 3 ∈ I → ln g 4 ∈ I → 4 ≤ deg (H3) (g 0) := by
    intro h3 h4
    by_contra hlt
    have hfilt : (H3).filter (g 0 ∈ ·) = {ln g 0, ln g 1, ln g 2} := by
      symm; refine Finset.eq_of_subset_of_card_le hlines ?_
      rw [h3l]; unfold deg at hlt; omega
    apply hnc
    refine ⟨fun f hf => ?_, fun f hf hmeet => ?_⟩
    · obtain ⟨k, rfl⟩ := mem_cop.1 hf; exact C.hln k
    obtain ⟨u, huf, hu⟩ := Finset.not_disjoint_iff.1 hmeet
    obtain ⟨i, rfl⟩ := mem_verts_cop.1 hu
    by_cases hr : g 0 ∈ f
    · have : f ∈ (H3).filter (g 0 ∈ ·) := Finset.mem_filter.2 ⟨hf, hr⟩
      rw [hfilt] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl | rfl <;> exact mem_cop.2 ⟨_, rfl⟩
    · have hfr : f ∈ del (H3) {g 0} := mem_del.2 ⟨hf, Finset.disjoint_singleton_right.2 hr⟩
      have hi : i ≠ 0 := fun h' => hr (h' ▸ huf)
      have key : ∀ k : Fin 5, ln g k ∈ I → i ∈ F7L k → f ∈ cop g := by
        intro k hk hik
        by_contra hfc
        have hne : f ≠ ln g k := fun h' => hfc (h' ▸ mem_cop.2 ⟨k, rfl⟩)
        exact Finset.disjoint_left.1 ((Finset.mem_filter.1 hk).2 f hfr hne)
          ((mem_ln C.hg).2 hik) huf
      rcases F7_noncentre i hi with h' | h'
      · exact key 3 h3 h'
      · exact key 4 h4 h'
  have hbound : hE (del (H3) {g 0}) + 10 < 4 * deg (H3) (g 0) := by
    have hle := Finset.card_le_card hsplit
    have hu := Finset.card_union_le (I.filter (fun e => e = ln g 3 ∨ e = ln g 4))
      (I.filter (fun e => Disjoint e (ln g 3 ∪ ln g 4)))
    have hI' : hE (del (H3) {g 0}) = I.card := rfl
    by_cases hb : ln g 3 ∈ I ∧ ln g 4 ∈ I
    · have h1 : (I.filter (fun e => e = ln g 3 ∨ e = ln g 4)).card ≤ 2 := by
        refine (Finset.card_le_card (fun e he => ?_)).trans (Finset.card_le_two (a := ln g 3)
          (b := ln g 4))
        rw [Finset.mem_filter] at he
        rcases he.2 with rfl | rfl <;> simp
      have := hboth hb.1 hb.2
      omega
    · have h1 : (I.filter (fun e => e = ln g 3 ∨ e = ln g 4)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb'
        rw [Finset.mem_filter] at ha hb'
        rcases ha.2 with rfl | rfl <;> rcases hb'.2 with rfl | rfl
        · rfl
        · exact absurd ⟨ha.1, hb'.1⟩ hb
        · exact absurd ⟨hb'.1, ha.1⟩ hb
        · rfl
      omega
  refine C.h.no_plus (E' := del (H3) {g 0}) 2 (C.sz_lt (del_subset _ _))
    (C.L3_H3.mono (del_subset _ _)) hF ?_ ?_
  · intro T hT
    have hT' := hT.of_del
    obtain ⟨s, hsT, hsS⟩ : ∃ s ∈ T ∪ {g 0}, s ∈ S₀ := by
      by_cases hr : g 0 ∈ S₀
      · exact ⟨g 0, Finset.mem_union_right _ (Finset.mem_singleton_self _), hr⟩
      · obtain ⟨s, hs⟩ := hT S₀ (mem_del.2 ⟨Finset.mem_insert_self _ _,
          Finset.disjoint_singleton_right.2 hr⟩)
        rw [Finset.mem_inter] at hs
        exact ⟨s, Finset.mem_union_left _ hs.2, hs.1⟩
    obtain ⟨v, hv⟩ := C.cover3 hT' hsT hsS
    refine ⟨insert v (T ∪ {g 0}), ?_, hv⟩
    have := Finset.card_union_le T {g 0}
    have := Finset.card_insert_le v (T ∪ {g 0})
    simp only [Finset.card_singleton] at *
    omega
  · have := C.verts_H3; have := C.card_H3; have := C.card_Hs; have := C.wt_E
    unfold wt; omega


lemma F7_third : ∀ a b : Fin 5, a ≠ b → 0 ∈ F7L a → 0 ∈ F7L b →
    ∃ c : Fin 5, c ≠ a ∧ c ≠ b ∧ 0 ∈ F7L c := by decide +kernel

/-- In `F - s`, the vertices of a copy of `F₇` other than `s` (when `s` is not the centre) lie in
no isolated edge. -/
lemma cov_copy {F : Finset (Finset α)} {g : Fin 7 → α} (hg : Function.Injective g)
    (hln : ∀ k, ln g k ∈ F) {i : Fin 7} (hi : i ≠ 0) :
    ∀ u ∈ (Finset.univ.image g).erase (g i), ∀ e ∈ isoEdges (del F {g i}), u ∉ e := by
  intro u hu
  obtain ⟨hui, hu⟩ := Finset.mem_erase.1 hu
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hu
  have hji : j ≠ i := fun h' => hui (h' ▸ rfl)
  obtain ⟨k, k', hkk, hik, hik', hjk, hmeet⟩ := F7_cov i hi j hji
  have hdel : ∀ k, i ∉ F7L k → ln g k ∈ del F {g i} := fun k hk =>
    mem_del.2 ⟨hln k, Finset.disjoint_singleton_right.2 fun h' => hk ((mem_ln hg).1 h')⟩
  exact not_mem_iso_of_meet (hdel k hik) (hdel k' hik') (fun h' => hkk ((ln_inj hg).1 h'))
    (by rwa [ln_disj hg]) ((mem_ln hg).2 hjk)

/-- **End of Claim 4**: the configuration is impossible once `R` is not closed. -/
lemma claim4_end (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) (hnc : ¬ IsClosed (H3) (cop g)) : False := by
  have h46 := C.claim46 hnc
  rw [F7Free_iff] at h46
  push Not at h46
  obtain ⟨g', hg', hall⟩ := h46
  change ∀ j, ln g' j ∈ del (H3) {g 0} at hall
  have hall3 : ∀ j, ln g' j ∈ H3 := fun j => del_subset _ _ (hall j)
  obtain ⟨l', hl'⟩ : ∃ l', ln g' l' = S₀ := by
    by_contra hne
    push Not at hne
    have := C.F7_Hs
    rw [F7Free_iff] at this
    exact this g' hg' fun j => (Finset.mem_insert.1 (hall3 j)).resolve_left (hne j)
  have hS0r : g 0 ∉ S₀ := by
    have := hall l'
    rw [hl', mem_del, Finset.disjoint_singleton_right] at this
    exact this.2
  -- a vertex `s₀ = g i = g' i'` of `S₀`
  obtain ⟨s₀, hs0⟩ : S₀.Nonempty := Finset.card_pos.1 (by rw [C.hc]; norm_num)
  obtain ⟨i, hil, rfl⟩ := mem_ln_iff.1 (C.hl ▸ hs0 : s₀ ∈ ln g l)
  have hi0 : i ≠ 0 := fun h' => hS0r (h' ▸ hs0)
  obtain ⟨i', hil', hgi'⟩ := mem_ln_iff.1 (hl' ▸ hs0 : g i ∈ ln g' l')
  obtain ⟨k0, hk00, hik0⟩ := F7_centre_line i
  obtain ⟨k', hk'l', hik'⟩ := F7L_two l' i' hil'
  have hCl : ln g k0 ∈ H3 := C.hln k0
  have hF0 : ln g' k' ∈ H3 := hall3 k'
  have hs_S0 : g i ∈ S₀ := hs0
  have hs_Cl : g i ∈ ln g k0 := (mem_ln C.hg).2 hik0
  have hs_F0 : g i ∈ ln g' k' := hgi' ▸ (mem_ln hg').2 hik'
  have hr_Cl : g 0 ∈ ln g k0 := (mem_ln C.hg).2 hk00
  have hr_F0 : g 0 ∉ ln g' k' := by
    have := hall k'; rw [mem_del, Finset.disjoint_singleton_right] at this; exact this.2
  have n1 : S₀ ≠ ln g k0 := fun h' => hS0r (h' ▸ hr_Cl)
  have n2 : S₀ ≠ ln g' k' := by rw [← hl']; exact fun h' => hk'l' ((ln_inj hg').1 h').symm
  have n3 : ln g k0 ≠ ln g' k' := fun h' => hr_F0 (h' ▸ hr_Cl)
  -- `H' = H₃ - s₀`
  have hsv : g i ∈ verts (H3) := C.g_verts i
  have hn : (verts (del (H3) {g i})).card < (verts (H3)).card := card_verts_del_singleton_lt hsv
  have hcd : (del (H3) {g i}).card + deg (H3) (g i) = (H3).card := card_del_singleton _ _
  have hF : F7Free (del (H3) {g i}) := by
    refine C.F7_Hs.mono fun f hf => ?_
    rw [mem_del, Finset.disjoint_singleton_right] at hf
    exact (Finset.mem_insert.1 hf.1).resolve_left fun h' => hf.2 (h' ▸ hs_S0)
  have hhit : ∀ f ∈ H3, g i ∈ f → f ∈ hit (H3) {g i} := fun f hf hsf =>
    mem_hit.2 ⟨hf, Finset.not_disjoint_iff.2 ⟨g i, hsf, Finset.mem_singleton_self _⟩⟩
  have hCR := cov_copy C.hg C.hln hi0
  have hbound : hE (del (H3) {g i}) + 10 < 4 * deg (H3) (g i) := by
    by_cases hi' : i' = 0
    · -- `s₀` is the centre of the second copy: degree at least 4
      subst hi'
      obtain ⟨k'', h1, h2, hk''⟩ := F7_third l' k' hk'l'.symm hil' hik'
      have hF1 : ln g' k'' ∈ H3 := hall3 k''
      have hs_F1 : g i ∈ ln g' k'' := hgi' ▸ (mem_ln hg').2 hk''
      have hr_F1 : g 0 ∉ ln g' k'' := by
        have := hall k''; rw [mem_del, Finset.disjoint_singleton_right] at this; exact this.2
      have n4 : S₀ ≠ ln g' k'' := by rw [← hl']; exact fun h' => h1 ((ln_inj hg').1 h').symm
      have n5 : ln g k0 ≠ ln g' k'' := fun h' => hr_F1 (h' ▸ hr_Cl)
      have n6 : ln g' k' ≠ ln g' k'' := fun h' => h2 ((ln_inj hg').1 h').symm
      have hd4 : 4 ≤ deg (H3) (g i) := by
        have hsub : ({S₀, ln g k0, ln g' k', ln g' k''} : Finset (Finset α)) ⊆
            (H3).filter (g i ∈ ·) := by
          intro f hf
          simp only [Finset.mem_insert, Finset.mem_singleton] at hf
          rcases hf with rfl | rfl | rfl | rfl
          · exact Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, hs_S0⟩
          · exact Finset.mem_filter.2 ⟨hCl, hs_Cl⟩
          · exact Finset.mem_filter.2 ⟨hF0, hs_F0⟩
          · exact Finset.mem_filter.2 ⟨hF1, hs_F1⟩
        have hc4 : ({S₀, ln g k0, ln g' k', ln g' k''} : Finset (Finset α)).card = 4 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair n6]
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨n3, n5⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨n1, n2, n4⟩
        unfold deg; rw [← hc4]; exact Finset.card_le_card hsub
      have hh := hE_del_le C.hE_H3 {g i} _ hCR
      have hc := card_nbr_sdiff_le C.L3_H3.card3 (g i) (B := {S₀, ln g k0})
        (fun f hf => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hf
          rcases hf with rfl | rfl
          · exact hhit _ (Finset.mem_insert_self _ _) hs_S0
          · exact hhit _ hCl hs_Cl) ((Finset.univ.image g).erase (g i)) (by
          intro f hf u huf hus
          refine Finset.mem_erase.2 ⟨hus, ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hf
          rcases hf with rfl | rfl
          · rw [← C.hl] at huf; obtain ⟨j, -, rfl⟩ := mem_ln_iff.1 huf; simp
          · obtain ⟨j, -, rfl⟩ := mem_ln_iff.1 huf; simp)
      rw [Finset.card_pair n1] at hc
      omega
    · have hCR0 := cov_copy hg' hall3 hi'
      rw [hgi'] at hCR0
      have hh := hE_del_le C.hE_H3 {g i} (((Finset.univ.image g).erase (g i)) ∪
        ((Finset.univ.image g').erase (g i))) (fun u hu => by
          rcases Finset.mem_union.1 hu with hu | hu
          · exact hCR u hu
          · exact hCR0 u hu)
      have hc := card_nbr_sdiff_le C.L3_H3.card3 (g i) (B := {S₀, ln g k0, ln g' k'})
        (fun f hf => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hf
          rcases hf with rfl | rfl | rfl
          · exact hhit _ (Finset.mem_insert_self _ _) hs_S0
          · exact hhit _ hCl hs_Cl
          · exact hhit _ hF0 hs_F0) (((Finset.univ.image g).erase (g i)) ∪
            ((Finset.univ.image g').erase (g i))) (by
          intro f hf u huf hus
          simp only [Finset.mem_insert, Finset.mem_singleton] at hf
          rcases hf with hf | hf | hf <;> rw [hf] at huf
          · rw [← C.hl] at huf; obtain ⟨j, -, rfl⟩ := mem_ln_iff.1 huf
            exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hus, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
          · obtain ⟨j, -, rfl⟩ := mem_ln_iff.1 huf
            exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hus, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
          · obtain ⟨j, -, rfl⟩ := mem_ln_iff.1 huf
            exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hus, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩))
      rw [Finset.card_eq_three.2 ⟨_, _, _, n1, n2, n3, rfl⟩] at hc
      omega
  refine C.h.no_plus (E' := del (H3) {g i}) 2 (C.sz_lt (del_subset _ _))
    (C.L3_H3.mono (del_subset _ _)) hF ?_ ?_
  · intro T hT
    obtain ⟨v, hv⟩ := C.cover3 hT.of_del (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      hs_S0
    refine ⟨insert v (T ∪ {g i}), ?_, hv⟩
    have := Finset.card_union_le T {g i}
    have := Finset.card_insert_le v (T ∪ {g i})
    simp only [Finset.card_singleton] at *
    omega
  · have := C.verts_H3; have := C.card_H3; have := C.card_Hs; have := C.wt_E
    unfold wt; omega

end FCfg

end OpenProblemsLab.HY
