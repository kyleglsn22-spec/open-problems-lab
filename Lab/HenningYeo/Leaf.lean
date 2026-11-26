import Lab.HenningYeo.Claim4

/-!
# Henning–Yeo Claim 4: the configuration around a vertex of degree 1

In a minimal counterexample, a leaf `x` lies in an edge `e = {x, v₁, v₂}` with `deg v₁ = deg v₂ = 2`
(Claim 4.1). We record this configuration in `Leaf` and prove Claim 4.2: `h(H - {v₁, v₂}) = 0`.
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-- The configuration of Claim 4: `e = {x, v₁, v₂}`, `deg x = 1`, and the edges at `vᵢ` are `e`
and `eᵢ`. -/
structure Leaf (E : Finset (Finset α)) (x v₁ v₂ : α) (e₁ e₂ : Finset α) : Prop where
  he : ({x, v₁, v₂} : Finset α) ∈ E
  x1 : x ≠ v₁
  x2 : x ≠ v₂
  v12 : v₁ ≠ v₂
  dx : deg E x = 1
  e1E : e₁ ∈ E
  e2E : e₂ ∈ E
  v1e1 : v₁ ∈ e₁
  v2e2 : v₂ ∈ e₂
  e1ne : e₁ ≠ {x, v₁, v₂}
  e2ne : e₂ ≠ {x, v₁, v₂}
  at1 : ∀ g ∈ E, v₁ ∈ g → g = {x, v₁, v₂} ∨ g = e₁
  at2 : ∀ g ∈ E, v₂ ∈ g → g = {x, v₁, v₂} ∨ g = e₂

namespace Leaf

variable {E : Finset (Finset α)} {x v₁ v₂ : α} {e₁ e₂ : Finset α}

lemma pair_comm (a b c : α) : ({a, b, c} : Finset α) = {a, c, b} := by
  ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-- The configuration is symmetric in `(v₁, e₁)` and `(v₂, e₂)`. -/
lemma swap (L : Leaf E x v₁ v₂ e₁ e₂) : Leaf E x v₂ v₁ e₂ e₁ := by
  have hp := pair_comm x v₁ v₂
  exact ⟨hp ▸ L.he, L.x2, L.x1, L.v12.symm, L.dx, L.e2E, L.e1E, L.v2e2, L.v1e1, hp ▸ L.e2ne,
    hp ▸ L.e1ne, hp ▸ L.at2, hp ▸ L.at1⟩

lemma x_e : x ∈ ({x, v₁, v₂} : Finset α) := by simp
lemma v1_e : v₁ ∈ ({x, v₁, v₂} : Finset α) := by simp
lemma v2_e : v₂ ∈ ({x, v₁, v₂} : Finset α) := by simp

lemma x_not_e1 (L : Leaf E x v₁ v₂ e₁ e₂) : x ∉ e₁ := fun h =>
  L.e1ne (eq_of_deg_one L.dx L.he x_e L.e1E h)

lemma x_not_e2 (L : Leaf E x v₁ v₂ e₁ e₂) : x ∉ e₂ := L.swap.x_not_e1

lemma v2_not_e1 (L : Leaf E x v₁ v₂ e₁ e₂) (hL : IsL3 E) : v₂ ∉ e₁ := fun h =>
  L.e1ne (hL.eq_of_two L.e1E L.he L.v12 L.v1e1 h v1_e v2_e)

lemma v1_not_e2 (L : Leaf E x v₁ v₂ e₁ e₂) (hL : IsL3 E) : v₁ ∉ e₂ := L.swap.v2_not_e1 hL

lemma e12 (L : Leaf E x v₁ v₂ e₁ e₂) (hL : IsL3 E) : e₁ ≠ e₂ := fun h =>
  L.v1_not_e2 hL (h ▸ L.v1e1)

/-- An edge outside `{e, e₁, e₂}` avoids `x, v₁, v₂`. -/
lemma avoid (L : Leaf E x v₁ v₂ e₁ e₂) {g : Finset α} (hg : g ∈ E) (h0 : g ≠ {x, v₁, v₂})
    (h1 : g ≠ e₁) (h2 : g ≠ e₂) : x ∉ g ∧ v₁ ∉ g ∧ v₂ ∉ g := by
  refine ⟨fun h => h0 (eq_of_deg_one L.dx L.he x_e hg h), fun h => ?_, fun h => ?_⟩
  · rcases L.at1 g hg h with h' | h' <;> contradiction
  · rcases L.at2 g hg h with h' | h' <;> contradiction

lemma mem_del12 (L : Leaf E x v₁ v₂ e₁ e₂) {g : Finset α} :
    g ∈ del E {v₁, v₂} ↔ g ∈ E ∧ g ≠ {x, v₁, v₂} ∧ g ≠ e₁ ∧ g ≠ e₂ := by
  rw [mem_del]
  constructor
  · rintro ⟨hg, hd⟩
    refine ⟨hg, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · exact Finset.disjoint_left.1 hd (h ▸ v1_e) (by simp)
    · exact Finset.disjoint_left.1 hd (h ▸ L.v1e1) (by simp)
    · exact Finset.disjoint_left.1 hd (h ▸ L.v2e2) (by simp)
  · rintro ⟨hg, h0, h1, h2⟩
    have := L.avoid hg h0 h1 h2
    refine ⟨hg, Finset.disjoint_left.2 fun w hw hw' => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
    rcases hw' with rfl | rfl
    · exact this.2.1 hw
    · exact this.2.2 hw

lemma x_not_verts_del12 (L : Leaf E x v₁ v₂ e₁ e₂) : x ∉ verts (del E {v₁, v₂}) := by
  intro h
  obtain ⟨g, hg, hxg⟩ := mem_verts.1 h
  exact ((L.mem_del12.1 hg).2.1) (eq_of_deg_one L.dx L.he x_e (del_subset _ _ hg) hxg)

/-- The neighbourhood of `{v₁, v₂}`: `x` and `S = (e₁ ∪ e₂) \ {v₁, v₂}`. -/
lemma mem_nbr12 (L : Leaf E x v₁ v₂ e₁ e₂) {w : α} (hw : w ∈ nbr E {v₁, v₂}) :
    w = x ∨ w ∈ (e₁ ∪ e₂) \ {v₁, v₂} := by
  rw [nbr, Finset.mem_sdiff] at hw
  obtain ⟨g, hg, hwg⟩ := mem_verts.1 hw.1
  rw [mem_hit] at hg
  obtain ⟨u, hug, hu⟩ := Finset.not_disjoint_iff.1 hg.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  have key : g = {x, v₁, v₂} ∨ g = e₁ ∨ g = e₂ := by
    rcases hu with rfl | rfl
    · rcases L.at1 g hg.1 hug with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases L.at2 g hg.1 hug with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  rcases key with rfl | rfl | rfl
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hwg hw
    rcases hwg with h | h | h
    · exact Or.inl h
    · exact absurd (Or.inl h) hw.2
    · exact absurd (Or.inr h) hw.2
  · exact Or.inr (Finset.mem_sdiff.2 ⟨Finset.mem_union_left _ hwg, hw.2⟩)
  · exact Or.inr (Finset.mem_sdiff.2 ⟨Finset.mem_union_right _ hwg, hw.2⟩)

/-- An isolated edge of `H - {v₁, v₂}` meets `S` in at least two vertices. -/
lemma two_le_inter_S (L : Leaf E x v₁ v₂ e₁ e₂) (h : MinCex E) {R : Finset α}
    (hR : R ∈ isoEdges (del E {v₁, v₂})) : 2 ≤ (R ∩ ((e₁ ∪ e₂) \ {v₁, v₂})).card := by
  refine (h.two_le_inter_nbr hR).trans (Finset.card_le_card fun w hw => ?_)
  rw [Finset.mem_inter] at hw ⊢
  refine ⟨hw.1, ?_⟩
  rcases L.mem_nbr12 hw.2 with rfl | h'
  · exact absurd (subset_verts (isoEdges_subset _ hR) hw.1) L.x_not_verts_del12
  · exact h'


/-- Claim 4.2, main step: an isolated edge `R` of `H - {v₁, v₂}` through `r ∈ e₂ \ e₁` and
`p ∈ e₁` gives the favourable reduction `X = {r, v₁}`. -/
lemma claim42_aux (L : Leaf E x v₁ v₂ e₁ e₂) (h : MinCex E) {R : Finset α}
    (hR : R ∈ isoEdges (del E {v₁, v₂})) {r p : α} (hr : r ∈ R) (hre2 : r ∈ e₂) (hre1 : r ∉ e₁)
    (hp : p ∈ R) (hpe1 : p ∈ e₁) : False := by
  have hRs := isoEdges_subset _ hR
  obtain ⟨hRE, hRe, hR1, hR2⟩ := L.mem_del12.1 hRs
  obtain ⟨hxR, hv1R, hv2R⟩ := L.avoid hRE hRe hR1 hR2
  have hiso : ∀ g ∈ del E {v₁, v₂}, g ≠ R → Disjoint R g := fun g hg hne =>
    (Finset.mem_filter.1 hR).2 g hg hne
  have hrv1 : r ≠ v₁ := fun h' => hv1R (h' ▸ hr)
  have hrv2 : r ≠ v₂ := fun h' => hv2R (h' ▸ hr)
  have hrx : r ≠ x := fun h' => hxR (h' ▸ hr)
  have hpr : p ≠ r := fun h' => hre1 (h' ▸ hpe1)
  -- the edges at `r` are `R` and `e₂`
  have hat_r : ∀ g ∈ E, r ∈ g → g = R ∨ g = e₂ := by
    intro g hg hrg
    by_cases hgs : g ∈ del E {v₁, v₂}
    · left; by_contra hne
      exact Finset.disjoint_left.1 (hiso g hgs hne) hr hrg
    · rw [L.mem_del12] at hgs; push Not at hgs
      by_cases h0 : g = {x, v₁, v₂}
      · subst h0; simp only [Finset.mem_insert, Finset.mem_singleton] at hrg
        rcases hrg with h' | h' | h' <;> contradiction
      by_cases h1 : g = e₁
      · subst h1; contradiction
      exact Or.inr (hgs hg h0 h1)
  set X : Finset α := {r, v₁} with hX
  have hrX : r ∈ X := by simp [hX]
  have hv1X : v₁ ∈ X := by simp [hX]
  have hblock : ∀ y ∈ ({x, v₁, v₂} : Finset α) ∪ R, ∀ f ∈ E, y ∈ f → ¬ Disjoint f X := by
    intro y hy f hf hyf hd
    have nr : r ∉ f := fun h' => Finset.disjoint_left.1 hd h' hrX
    have nv : v₁ ∉ f := fun h' => Finset.disjoint_left.1 hd h' hv1X
    have ne0 : f ≠ {x, v₁, v₂} := fun h' => nv (h' ▸ v1_e)
    have ne1 : f ≠ e₁ := fun h' => nv (h' ▸ L.v1e1)
    have ne2 : f ≠ e₂ := fun h' => nr (h' ▸ hre2)
    have hfR : f ≠ R := fun h' => nr (h' ▸ hr)
    obtain ⟨a1, a2, a3⟩ := L.avoid hf ne0 ne1 ne2
    rw [Finset.mem_union] at hy
    rcases hy with hy | hy
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> contradiction
    · exact Finset.disjoint_left.1 (hiso f (L.mem_del12.2 ⟨hf, ne0, ne1, ne2⟩) hfR) hy hyf
  have hhit : ∀ g ∈ E, ¬ Disjoint g X → g = {x, v₁, v₂} ∨ g = e₁ ∨ g = e₂ ∨ g = R := by
    intro g hg hgX
    obtain ⟨u, hug, huX⟩ := Finset.not_disjoint_iff.1 hgX
    simp only [hX, Finset.mem_insert, Finset.mem_singleton] at huX
    rcases huX with rfl | rfl
    · rcases hat_r g hg hug with h' | h'
      · exact Or.inr (Or.inr (Or.inr h'))
      · exact Or.inr (Or.inr (Or.inl h'))
    · rcases L.at1 g hg hug with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
  have hS4 : ((e₁ ∪ e₂) \ {v₁, v₂}).card ≤ 4 := by
    have hsub : (e₁ ∪ e₂) \ {v₁, v₂} ⊆ e₁.erase v₁ ∪ e₂.erase v₂ := by
      intro w hw
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        not_or] at hw
      rcases hw.1 with h' | h'
      · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hw.2.1, h'⟩)
      · exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hw.2.2, h'⟩)
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    rw [Finset.card_erase_of_mem L.v1e1, Finset.card_erase_of_mem L.v2e2,
      h.L.card3 _ L.e1E, h.L.card3 _ L.e2E]
  have hpv : p ≠ v₁ := fun h' => hv1R (h' ▸ hp)
  have hpv2 : p ≠ v₂ := fun h' => hv2R (h' ▸ hp)
  have hSR : 2 ≤ (((e₁ ∪ e₂) \ {v₁, v₂}) ∩ R).card := by
    have : ({r, p} : Finset α) ⊆ ((e₁ ∪ e₂) \ {v₁, v₂}) ∩ R := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · simp [hre2, hr, hrv1, hrv2]
      · simp [hpe1, hp, hpv, hpv2]
    have := Finset.card_le_card this
    rwa [Finset.card_pair hpr.symm] at this
  have hk : hE (del E X) ≤ 1 := by
    have h2 := h.two_mul_hE_del_le X
    have hsub : nbr E X ∩ verts (del E X) ⊆ ((e₁ ∪ e₂) \ {v₁, v₂}) \ R := by
      intro w hw
      rw [Finset.mem_inter, nbr, Finset.mem_sdiff] at hw
      obtain ⟨⟨hw1, hwX⟩, hw2⟩ := hw
      have nb : ∀ y ∈ ({x, v₁, v₂} : Finset α) ∪ R, y ≠ w := fun y hy hyw =>
        not_mem_verts_del (hblock y hy) (hyw ▸ hw2)
      obtain ⟨g, hg, hwg⟩ := mem_verts.1 hw1
      rw [mem_hit] at hg
      have hwR : w ∉ R := fun h' => nb w (Finset.mem_union_right _ h') rfl
      have hwv2 : w ≠ v₂ := fun h' => nb v₂ (by simp) h'.symm
      have hwv1 : w ≠ v₁ := fun h' => hwX (h' ▸ hv1X)
      rcases hhit g hg.1 hg.2 with rfl | rfl | rfl | rfl
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hwg
        rcases hwg with h' | h' | h'
        · exact absurd h'.symm (nb x (by simp))
        · exact absurd h' hwv1
        · exact absurd h' hwv2
      · simp [hwg, hwv1, hwv2, hwR]
      · simp [hwg, hwv1, hwv2, hwR]
      · exact absurd hwg hwR
    have := Finset.card_le_card hsub
    have := Finset.card_sdiff_add_card_inter ((e₁ ∪ e₂) \ {v₁, v₂}) R
    omega
  have hD : ({{x, v₁, v₂}, e₁, e₂, R} : Finset (Finset α)) ⊆ hit E X := by
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rw [mem_hit, Finset.not_disjoint_iff]
    rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨L.he, v₁, v1_e, hv1X⟩
    · exact ⟨L.e1E, v₁, L.v1e1, hv1X⟩
    · exact ⟨L.e2E, r, hre2, hrX⟩
    · exact ⟨hRE, r, hr, hrX⟩
  have hDcard : ({{x, v₁, v₂}, e₁, e₂, R} : Finset (Finset α)).card = 4 := by
    have h12 := L.e12 h.L
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hR2)]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h12, Ne.symm hR1⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm L.e1ne, Ne.symm L.e2ne, Ne.symm hRe⟩
  have hRcard : (({x, v₁, v₂} : Finset α) ∪ R).card = 6 := by
    rw [Finset.card_union_of_disjoint, h.L.card3 R hRE, h.L.card3 _ L.he]
    rw [Finset.disjoint_left]; intro y hy hyR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> contradiction
  refine h.no_fav_del (X := X) (R := {x, v₁, v₂} ∪ R) (D := {{x, v₁, v₂}, e₁, e₂, R}) 1 ?_ ?_ hD
    ⟨R, by simp⟩ hk ?_
  · exact Finset.union_subset (subset_verts L.he) (subset_verts hRE)
  · rw [Finset.disjoint_left]
    exact fun y hy => not_mem_verts_del (hblock y hy)
  · rw [hRcard, hDcard, hX, Finset.card_pair hrv1]; norm_num

/-- **Claim 4.2**: `h(H - {v₁, v₂}) = 0`. -/
lemma claim42 (L : Leaf E x v₁ v₂ e₁ e₂) (h : MinCex E) : hE (del E {v₁, v₂}) = 0 := by
  by_contra h0
  obtain ⟨R, hR⟩ : (isoEdges (del E {v₁, v₂})).Nonempty :=
    Finset.card_pos.1 (Nat.pos_of_ne_zero h0)
  have hRE := del_subset _ _ (isoEdges_subset _ hR)
  obtain ⟨_, hRe, hR1, hR2⟩ := L.mem_del12.1 (isoEdges_subset _ hR)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (show 1 < _ from L.two_le_inter_S h hR)
  simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union] at ha hb
  have hv : v₁ ≠ v₂ := L.v12
  have two1 : ¬ (a ∈ e₁ ∧ b ∈ e₁) := fun ⟨h1, h2⟩ =>
    hR1 (h.L.eq_of_two hRE L.e1E hab ha.1 hb.1 h1 h2)
  have two2 : ¬ (a ∈ e₂ ∧ b ∈ e₂) := fun ⟨h1, h2⟩ =>
    hR2 (h.L.eq_of_two hRE L.e2E hab ha.1 hb.1 h1 h2)
  by_cases ha1 : a ∈ e₁
  · have hb1 : b ∉ e₁ := fun h' => two1 ⟨ha1, h'⟩
    have hb2 : b ∈ e₂ := hb.2.1.resolve_left hb1
    exact L.claim42_aux h hR hb.1 hb2 hb1 ha.1 ha1
  · have ha2 : a ∈ e₂ := ha.2.1.resolve_left ha1
    by_cases hb1 : b ∈ e₁
    · exact L.claim42_aux h hR ha.1 ha2 ha1 hb.1 hb1
    · exact two2 ⟨ha2, hb.2.1.resolve_left hb1⟩

end Leaf

end OpenProblemsLab.HY
