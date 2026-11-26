import Lab.HenningYeo.Theorem7

/-!
# Henning–Yeo Theorem 6: the minimal-counterexample framework

The statement we prove by induction (`Goal6`) is Theorem 6 of Henning–Yeo with the strict part
restricted to hypergraphs that have a vertex of degree 1 (see `ledger/henning-yeo-plan.md` for
why: this is all the induction uses, and it closes a gap in the published argument).
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-- `17 τ ≤ w`. -/
def Good (E : Finset (Finset α)) : Prop := ∃ T : Finset α, IsTransversal E T ∧ 17 * T.card ≤ wt E

/-- `17 τ < w`. -/
def Strict (E : Finset (Finset α)) : Prop := ∃ T : Finset α, IsTransversal E T ∧ 17 * T.card < wt E

/-- `F` is a union of components of `E`: no edge of `E` outside `F` meets a vertex of `F`. -/
def IsClosed (E F : Finset (Finset α)) : Prop :=
  F ⊆ E ∧ ∀ e ∈ E, ¬ Disjoint e (verts F) → e ∈ F

/-- `F` is a copy of the template `K` (a hypergraph on `Fin k`). -/
def IsCopy {k : ℕ} (K : Finset (Finset (Fin k))) (F : Finset (Finset α)) : Prop :=
  ∃ g : Fin k → α, Function.Injective g ∧ F = K.image (fun e => e.image g)

/-- The five lines of the template `F₇` (centre `0`), as in `F7Free`. -/
def F7L : Fin 5 → Finset (Fin 7) := ![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {2, 4, 6}]

/-- `Fin 7 ↪ Fin 10`. -/
def emb7 : Fin 7 → Fin 10 := Fin.castLE (by norm_num)

/-- The templates `H₁₀`, `H₁₀'`: delete line `l` of `F₇` and add new vertices `7, 8, 9` with
edges `{7,8,9}`, `{8} ∪ (l \ {b})`, `{9} ∪ (l \ {a})` (`a ≠ b ∈ l`; the two new edges share the
third point of `l`). Henning–Yeo do not fix which point of `l` is shared; every choice gives a
tight graph (`τ = 4`, `w = 68`), so we take the whole family (see `ledger/henning-yeo-plan.md`). -/
def gadget (l : Fin 5) (a b : Fin 7) : Finset (Finset (Fin 10)) :=
  ((Finset.univ.erase l).image (fun i => (F7L i).image emb7)) ∪
    {{7, 8, 9}, insert 8 (((F7L l).erase b).image emb7), insert 9 (((F7L l).erase a).image emb7)}

/-- `F` is a copy of one of the hypergraphs `H₁₀`, `H₁₀'`. -/
def IsGadget (F : Finset (Finset α)) : Prop :=
  ∃ l a b, a ∈ F7L l ∧ b ∈ F7L l ∧ a ≠ b ∧ IsCopy (gadget l a b) F

/-- An exceptional vertex: a vertex of degree 1 in an isolated edge or in a component that is a
copy of `H₁₀` or `H₁₀'`. -/
def HasExc (E : Finset (Finset α)) : Prop :=
  ∃ x, deg E x = 1 ∧ (x ∈ verts (isoEdges E) ∨
    ∃ F, IsClosed E F ∧ x ∈ verts F ∧ IsGadget F)

/-- Theorem 6 (with the strict part for hypergraphs that have a vertex of degree 1). -/
def Goal6 (E : Finset (Finset α)) : Prop :=
  Good E ∧ ((∃ x, deg E x = 1) → ¬ HasExc E → Strict E)

/-- Size used for the induction: `n + m`. -/
def sz (E : Finset (Finset α)) : ℕ := (verts E).card + E.card


/-! ### Splitting along a closed set of edges -/

section Split

variable {E F : Finset (Finset α)}

lemma IsClosed.disjoint_sdiff (hF : IsClosed E F) {e : Finset α} (he : e ∈ E \ F) :
    Disjoint e (verts F) := by
  by_contra h
  exact (Finset.mem_sdiff.1 he).2 (hF.2 e (Finset.mem_sdiff.1 he).1 h)

lemma IsClosed.disjoint_verts (hF : IsClosed E F) : Disjoint (verts F) (verts (E \ F)) := by
  rw [Finset.disjoint_right]
  intro x hx hxF
  obtain ⟨e, he, hxe⟩ := mem_verts.1 hx
  exact Finset.disjoint_left.1 (hF.disjoint_sdiff he) hxe hxF

lemma IsClosed.compl (hF : IsClosed E F) : IsClosed E (E \ F) := by
  refine ⟨Finset.sdiff_subset, fun e he hne => ?_⟩
  refine Finset.mem_sdiff.2 ⟨he, fun heF => hne ?_⟩
  rw [Finset.disjoint_left]
  intro x hxe hx
  exact Finset.disjoint_left.1 hF.disjoint_verts (subset_verts heF hxe) hx

lemma IsClosed.trans {G : Finset (Finset α)} (hF : IsClosed E F) (hG : IsClosed F G) :
    IsClosed E G := by
  refine ⟨hG.1.trans hF.1, fun e he hne => hG.2 e (hF.2 e he ?_) hne⟩
  intro hd
  exact hne (Finset.disjoint_of_subset_right (verts_mono hG.1) hd)

lemma IsClosed.deg_eq (hF : IsClosed E F) {x : α} (hx : x ∈ verts F) : deg F x = deg E x := by
  unfold deg
  congr 1
  ext e
  simp only [Finset.mem_filter]
  refine ⟨fun h => ⟨hF.1 h.1, h.2⟩, fun h => ⟨hF.2 e h.1 ?_, h.2⟩⟩
  exact Finset.not_disjoint_iff.2 ⟨x, h.2, hx⟩

lemma IsClosed.isoEdges (hF : IsClosed E F) :
    isoEdges E = isoEdges F ∪ isoEdges (E \ F) := by
  ext e
  simp only [OpenProblemsLab.HY.isoEdges, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨he, hiso⟩
    by_cases heF : e ∈ F
    · exact Or.inl ⟨heF, fun f hf hne => hiso f (hF.1 hf) hne⟩
    · exact Or.inr ⟨⟨he, heF⟩, fun f hf hne => hiso f hf.1 hne⟩
  · rintro (⟨heF, hiso⟩ | ⟨⟨he, heF⟩, hiso⟩)
    · refine ⟨hF.1 heF, fun f hf hne => ?_⟩
      by_cases hfF : f ∈ F
      · exact hiso f hfF hne
      · exact Finset.disjoint_of_subset_left (subset_verts heF)
          (hF.disjoint_sdiff (Finset.mem_sdiff.2 ⟨hf, hfF⟩)).symm
    · refine ⟨he, fun f hf hne => ?_⟩
      by_cases hfF : f ∈ F
      · exact Finset.disjoint_of_subset_right (subset_verts hfF)
          (hF.disjoint_sdiff (Finset.mem_sdiff.2 ⟨he, heF⟩))
      · exact hiso f ⟨hf, hfF⟩ hne

lemma IsClosed.wt_eq (hF : IsClosed E F) : wt E = wt F + wt (E \ F) := by
  have hEF : E = F ∪ (E \ F) := (Finset.union_sdiff_of_subset hF.1).symm
  have h1 : E.card = F.card + (E \ F).card := by
    rw [hEF, Finset.card_union_of_disjoint Finset.disjoint_sdiff]
    simp [Finset.union_sdiff_left]
  have h2 : (verts E).card = (verts F).card + (verts (E \ F)).card := by
    conv_lhs => rw [hEF]
    rw [verts_union, Finset.card_union_of_disjoint hF.disjoint_verts]
  have h3 : hE E = hE F + hE (E \ F) := by
    unfold hE
    rw [hF.isoEdges, Finset.card_union_of_disjoint]
    exact Finset.disjoint_of_subset_left (isoEdges_subset F)
      (Finset.disjoint_of_subset_right (isoEdges_subset _) Finset.disjoint_sdiff)
  unfold wt
  omega

lemma IsClosed.hasExc (hF : IsClosed E F) (h : HasExc F) : HasExc E := by
  obtain ⟨x, hx1, hx⟩ := h
  have hxF : x ∈ verts F := by
    rcases hx with hx | ⟨G, hG, hxG, _⟩
    · exact verts_mono (isoEdges_subset F) hx
    · exact verts_mono hG.1 hxG
  refine ⟨x, (hF.deg_eq hxF) ▸ hx1, ?_⟩
  rcases hx with hx | ⟨G, hG, hxG, hc⟩
  · left; rw [hF.isoEdges]; exact verts_mono Finset.subset_union_left hx
  · exact Or.inr ⟨G, hF.trans hG, hxG, hc⟩

lemma IsTransversal.split (hF : F ⊆ E) {T U : Finset α} (hT : IsTransversal F T)
    (hU : IsTransversal (E \ F) U) : IsTransversal E (T ∪ U) := by
  have := hT.union hU
  rwa [Finset.union_sdiff_of_subset hF] at this

lemma deg_eq_zero_of_not_mem {E : Finset (Finset α)} {x : α} (hx : x ∉ verts E) : deg E x = 0 := by
  unfold deg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hxe
  exact hx (subset_verts he hxe)

lemma mem_verts_of_deg_pos {E : Finset (Finset α)} {x : α} (hx : 0 < deg E x) : x ∈ verts E := by
  by_contra h; rw [deg_eq_zero_of_not_mem h] at hx; omega

/-- `Goal6` is preserved by gluing a closed set to its complement. -/
lemma goal6_of_split (hF : IsClosed E F) (h1 : Goal6 F) (h2 : Goal6 (E \ F)) :
    Goal6 E := by
  have hw := hF.wt_eq
  obtain ⟨⟨T, hT, hTw⟩, hs1⟩ := h1
  obtain ⟨⟨U, hU, hUw⟩, hs2⟩ := h2
  have hc := Finset.card_union_le T U
  refine ⟨⟨T ∪ U, hT.split hF.1 hU, by omega⟩, fun ⟨x, hx⟩ hexc => ?_⟩
  have hxE := mem_verts_of_deg_pos (show 0 < deg E x by omega)
  have hEF : E = F ∪ (E \ F) := (Finset.union_sdiff_of_subset hF.1).symm
  rw [hEF, verts_union, Finset.mem_union] at hxE
  rcases hxE with hxF | hxG
  · obtain ⟨T', hT', hT'w⟩ := hs1 ⟨x, (hF.deg_eq hxF).trans hx⟩ (fun h => hexc (hF.hasExc h))
    have hc' := Finset.card_union_le T' U
    exact ⟨T' ∪ U, hT'.split hF.1 hU, by omega⟩
  · have hG := hF.compl
    obtain ⟨U', hU', hU'w⟩ := hs2 ⟨x, (hG.deg_eq hxG).trans hx⟩ (fun h => hexc (hG.hasExc h))
    have hc' := Finset.card_union_le T U'
    exact ⟨T ∪ U', hT.split hF.1 hU', by omega⟩

end Split

/-- A minimal counterexample. -/
structure MinCex (E : Finset (Finset α)) : Prop where
  L : IsL3 E
  F7 : F7Free E
  ih : ∀ E' : Finset (Finset α), sz E' < sz E → IsL3 E' → F7Free E' → Goal6 E'
  bad : ¬ Goal6 E

namespace MinCex

variable {E : Finset (Finset α)}

/-- Type 1: `17 τ > w`. -/
def Type1 (E : Finset (Finset α)) : Prop := ¬ Good E

lemma good_or {h : MinCex E} : ¬ Good E ∨
    (Good E ∧ (∃ x, deg E x = 1) ∧ ¬ HasExc E ∧ ¬ Strict E) := by
  by_cases hg : Good E
  · right
    refine ⟨hg, ?_⟩
    by_contra hc
    exact h.bad ⟨hg, fun hx hex => by by_contra hs; exact hc ⟨hx, hex, hs⟩⟩
  · exact Or.inl hg

/-- A favorable reduction: `H' ⊆`-smaller, with `w(H') + 17|X| < w(H)` and `X ∪ T'` a
transversal for every transversal `T'` of `H'`. -/
lemma no_favorable (h : MinCex E) {E' : Finset (Finset α)} {X : Finset α}
    (hs : sz E' < sz E) (hL : IsL3 E') (hF : F7Free E')
    (hT : ∀ T, IsTransversal E' T → IsTransversal E (T ∪ X))
    (hw : wt E' + 17 * X.card < wt E) : False := by
  obtain ⟨T, hT', hTw⟩ := (h.ih E' hs hL hF).1
  have hU := hT T hT'
  have hc := Finset.card_union_le T X
  have hs' : Strict E := ⟨T ∪ X, hU, by omega⟩
  exact h.bad ⟨⟨T ∪ X, hU, by omega⟩, fun _ _ => hs'⟩

/-- A good reduction (`w(H') + 17|X| ≤ w(H)`) gives `Good E`. -/
lemma good_of_reduction (h : MinCex E) {E' : Finset (Finset α)} {X : Finset α}
    (hs : sz E' < sz E) (hL : IsL3 E') (hF : F7Free E')
    (hT : ∀ T, IsTransversal E' T → IsTransversal E (T ∪ X))
    (hw : wt E' + 17 * X.card ≤ wt E) : Good E := by
  obtain ⟨T, hT', hTw⟩ := (h.ih E' hs hL hF).1
  have hc := Finset.card_union_le T X
  exact ⟨T ∪ X, hT T hT', by omega⟩


/-! ### Claim 1: a minimal counterexample is connected, nonempty, and has no isolated edge -/

lemma sz_lt_of_ssubset {E F : Finset (Finset α)} (h : F ⊂ E) : sz F < sz E := by
  unfold sz
  have h1 := Finset.card_lt_card h
  have h2 := Finset.card_le_card (verts_mono h.subset)
  omega

lemma nonempty (h : MinCex E) : E.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  refine h.bad ⟨⟨∅, fun e he => absurd he (Finset.notMem_empty e), by simp⟩, ?_⟩
  rintro ⟨x, hx⟩
  simp [deg] at hx

/-- Claim 1(a): no proper nonempty closed subset (connectivity). -/
lemma closed_eq (h : MinCex E) {F : Finset (Finset α)} (hF : IsClosed E F) (hne : F.Nonempty) :
    F = E := by
  by_contra hFE
  have hss : F ⊂ E := Finset.ssubset_iff_subset_ne.2 ⟨hF.1, hFE⟩
  have hne2 : (E \ F).Nonempty := Finset.sdiff_nonempty.2 (fun h' => hFE (subset_antisymm hF.1 h'))
  have hss2 : E \ F ⊂ E := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.sdiff_subset, fun h' => ?_⟩
    obtain ⟨e, he⟩ := hne
    have : e ∈ E \ F := by rw [h']; exact hF.1 he
    exact (Finset.mem_sdiff.1 this).2 he
  exact h.bad (goal6_of_split hF
    (h.ih F (sz_lt_of_ssubset hss) (h.L.mono hF.1) (h.F7.mono hF.1))
    (h.ih (E \ F) (sz_lt_of_ssubset hss2) (h.L.mono Finset.sdiff_subset)
      (h.F7.mono Finset.sdiff_subset)))

/-- Claim 1(b): no isolated edge. -/
lemma hE_eq_zero (h : MinCex E) : hE E = 0 := by
  by_contra h0
  obtain ⟨e, he⟩ : (isoEdges E).Nonempty := Finset.card_pos.1 (Nat.pos_of_ne_zero h0)
  have heE := isoEdges_subset E he
  have hcl : IsClosed E {e} := by
    refine ⟨Finset.singleton_subset_iff.2 heE, fun f hf hne => ?_⟩
    by_contra hfe
    rw [Finset.mem_singleton] at hfe
    apply hne
    simp only [verts, Finset.singleton_biUnion, id]
    exact ((Finset.mem_filter.1 he).2 f hf hfe).symm
  have hE1 : E = {e} := (h.closed_eq hcl (Finset.singleton_nonempty e)).symm
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 (h.L.card3 e heE)
  have hiso : isoEdges E = E := by
    rw [hE1]; ext f
    simp only [OpenProblemsLab.HY.isoEdges, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, fun g hg hgf => absurd hg hgf⟩
  refine h.bad ⟨⟨{a}, fun f hf => ?_, ?_⟩, fun _ hexc => ?_⟩
  · rw [hE1, Finset.mem_singleton] at hf; subst hf; exact ⟨a, by simp⟩
  · unfold wt hE; rw [hiso, hE1]
    simp [verts, Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩]
  · exfalso; apply hexc
    refine ⟨a, ?_, Or.inl ?_⟩
    · rw [hE1]; unfold deg; rw [Finset.filter_singleton]; simp
    · rw [hiso, hE1]; simp [verts]

end MinCex

end OpenProblemsLab.HY
