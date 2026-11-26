import Lab.HenningYeo.Claim46

/-!
# Henning–Yeo Claim 4.5

The copy `R` of `F₇` in `H₃` is not a union of components of `H₃`. If `|S| = 3` this would make
`H` itself a copy of `H₁₀` or `H₁₀'` (so `H` satisfies Theorem 6, as `x` is exceptional); if
`|S| = 4` a second choice of `S₀` leads to a contradiction.
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

set_option linter.unusedSectionVars false

/-- Extend `g : Fin 7 → α` by `7 ↦ x`, `8 ↦ v₁`, `9 ↦ v₂`. -/
def ext10 (g : Fin 7 → α) (x v₁ v₂ : α) (i : Fin 10) : α :=
  if h : (i : ℕ) < 7 then g ⟨i, h⟩ else if (i : ℕ) = 7 then x else if (i : ℕ) = 8 then v₁ else v₂

lemma ext10_emb (g : Fin 7 → α) (x v₁ v₂ : α) (i : Fin 7) : ext10 g x v₁ v₂ (emb7 i) = g i := by
  simp [ext10, emb7, i.isLt]

lemma ext10_comp (g : Fin 7 → α) (x v₁ v₂ : α) : ext10 g x v₁ v₂ ∘ emb7 = g :=
  funext (ext10_emb g x v₁ v₂)

@[simp] lemma ext10_7 (g : Fin 7 → α) (x v₁ v₂ : α) : ext10 g x v₁ v₂ 7 = x := by simp [ext10]
@[simp] lemma ext10_8 (g : Fin 7 → α) (x v₁ v₂ : α) : ext10 g x v₁ v₂ 8 = v₁ := by simp [ext10]
@[simp] lemma ext10_9 (g : Fin 7 → α) (x v₁ v₂ : α) : ext10 g x v₁ v₂ 9 = v₂ := by simp [ext10]

lemma ext10_injective {g : Fin 7 → α} (hg : Function.Injective g) {x v₁ v₂ : α}
    (h1 : x ≠ v₁) (h2 : x ≠ v₂) (h12 : v₁ ≠ v₂) (hx : ∀ i, g i ≠ x) (hv1 : ∀ i, g i ≠ v₁)
    (hv2 : ∀ i, g i ≠ v₂) : Function.Injective (ext10 g x v₁ v₂) := by
  intro i j hij
  have hi := i.isLt; have hj := j.isLt
  unfold ext10 at hij
  apply Fin.ext
  split_ifs at hij <;>
    first
    | omega
    | exact Fin.mk.inj_iff.1 (hg hij)
    | exact absurd hij (hx _)
    | exact absurd hij.symm (hx _)
    | exact absurd hij (hv1 _)
    | exact absurd hij.symm (hv1 _)
    | exact absurd hij (hv2 _)
    | exact absurd hij.symm (hv2 _)
    | exact absurd hij h1
    | exact absurd hij.symm h1
    | exact absurd hij h2
    | exact absurd hij.symm h2
    | exact absurd hij h12
    | exact absurd hij.symm h12

/-- A transversal of size 3 of `F₇` minus line `l`, meeting `l \ {a}`. -/
lemma F7_tr3 : ∀ l : Fin 5, ∀ a ∈ F7L l, ∃ T ∈ ([{0, 1, 4}, {1, 3, 6}] : List (Finset (Fin 7))),
    (∀ k, k ≠ l → ¬ Disjoint (F7L k) T) ∧ ¬ Disjoint ((F7L l).erase a) T := by decide +kernel


lemma gadget_image {g : Fin 7 → α} (hg : Function.Injective g) (x v₁ v₂ : α) (l : Fin 5)
    (a b : Fin 7) :
    (gadget l a b).image (fun e => e.image (ext10 g x v₁ v₂)) =
      (Finset.univ.erase l).image (ln g) ∪
        {{x, v₁, v₂}, insert v₁ ((ln g l).erase (g b)), insert v₂ ((ln g l).erase (g a))} := by
  unfold gadget
  rw [Finset.image_union, Finset.image_image]
  congr 1
  · refine Finset.image_congr fun i _ => ?_
    simp only [Function.comp, ln, Finset.image_image, ext10_comp]
  · simp only [Finset.image_insert, Finset.image_singleton, Finset.image_image, ext10_comp,
      ext10_7, ext10_8, ext10_9, ln, Finset.image_erase hg]


/-- An edge `f ∋ v` with `f \ {v} ⊆ S₀`, `|S₀| = 3`, `v ∉ S₀` is `{v} ∪ (S₀ \ {b})`. -/
lemma edge_form {S₀ f : Finset α} {v : α} (hf3 : f.card = 3) (hv : v ∈ f)
    (hsub : f.erase v ⊆ S₀) (hS03 : S₀.card = 3) (hvS : v ∉ S₀) :
    ∃ b ∈ S₀, f = insert v (S₀.erase b) ∧ b ∉ f := by
  have hc : (S₀ \ f.erase v).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_erase_of_mem hv, hf3, hS03]
  obtain ⟨b, hb⟩ := Finset.card_eq_one.1 hc
  have hbS : b ∈ S₀ \ f.erase v := hb ▸ Finset.mem_singleton_self b
  rw [Finset.mem_sdiff] at hbS
  have hbf : b ∉ f := fun h' => hbS.2 (Finset.mem_erase.2 ⟨fun hbv => hvS (hbv ▸ hbS.1), h'⟩)
  refine ⟨b, hbS.1, ?_, hbf⟩
  have heq : f.erase v = S₀.erase b := by
    refine Finset.eq_of_subset_of_card_le (fun w hw => Finset.mem_erase.2 ⟨fun hwb => ?_, hsub hw⟩)
      ?_
    · exact hbS.2 (hwb ▸ hw)
    · rw [Finset.card_erase_of_mem hbS.1, Finset.card_erase_of_mem hv, hf3, hS03]
  rw [← heq, Finset.insert_erase hv]

namespace FCfg

variable {E : Finset (Finset α)} {x v₁ v₂ : α} {e₁ e₂ S₀ : Finset α} {g : Fin 7 → α} {l : Fin 5}

set_option quotPrecheck false in
local notation "Hs" => del E ({v₁, v₂} : Finset _)
set_option quotPrecheck false in
local notation "H3" => insert S₀ (del E ({v₁, v₂} : Finset _))

lemma verts_H3_ne (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) {w : α} (hw : w ∈ verts (H3)) :
    w ∈ verts E ∧ w ≠ x ∧ w ≠ v₁ ∧ w ≠ v₂ := by
  rw [verts_insert, Finset.mem_union] at hw
  rcases hw with hw | hw
  · exact C.L.S_sub (C.hS0 hw)
  · exact C.L.verts_del12_sub hw

lemma S0_verts_cop (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) : S₀ ⊆ verts (cop g) := by
  rw [← C.hl]; exact subset_verts (mem_cop.2 ⟨l, rfl⟩)

/-- Claim 4.5 when `S ⊄ S₀` (`|S| = 4`). -/
lemma claim45B (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) (hcl : IsClosed (H3) (cop g)) {t : α}
    (ht : t ∈ (e₁ ∪ e₂) \ {v₁, v₂}) (htS : t ∉ S₀) : False := by
  obtain ⟨u, hu⟩ : S₀.Nonempty := Finset.card_pos.1 (by rw [C.hc]; norm_num)
  obtain ⟨S₁, hS1⟩ : ∃ S₁, S₁ = insert t (S₀.erase u) := ⟨_, rfl⟩
  have hS1S : S₁ ⊆ (e₁ ∪ e₂) \ {v₁, v₂} := hS1 ▸
    Finset.insert_subset ht ((Finset.erase_subset _ _).trans C.hS0)
  have hS1c : S₁.card = 3 := by
    rw [hS1, Finset.card_insert_of_notMem (fun h' => htS (Finset.mem_of_mem_erase h')),
      Finset.card_erase_of_mem hu, C.hc]
  have h44 := C.L.claim44 C.h hS1S hS1c
  rw [F7Free_iff] at h44
  push Not at h44
  obtain ⟨g', hg', hall⟩ := h44
  change ∀ j, ln g' j ∈ insert S₁ (Hs) at hall
  obtain ⟨l', hl'⟩ : ∃ l', ln g' l' = S₁ := by
    by_contra hne
    push Not at hne
    have := C.F7_Hs
    rw [F7Free_iff] at this
    exact this g' hg' fun j => (Finset.mem_insert.1 (hall j)).resolve_left (hne j)
  have hlnHs : ∀ k, k ≠ l' → ln g' k ∈ H3 := fun k hk =>
    Finset.mem_insert_of_mem ((Finset.mem_insert.1 (hall k)).resolve_left fun h' =>
      hk ((ln_inj hg').1 (h'.trans hl'.symm)))
  -- `t` is not a vertex of `R`
  have htR : t ∉ verts (cop g) := by
    intro htv
    obtain ⟨i, rfl⟩ := mem_verts_cop.1 htv
    have hil : i ∉ F7L l := fun h' => htS (by rw [← C.hl]; exact (mem_ln C.hg).2 h')
    obtain ⟨k, hik, hmeet⟩ := F7_off l i hil
    have hkl : k ≠ l := fun h' => hil (h' ▸ hik)
    rw [← ln_disj C.hg, C.hl] at hmeet
    obtain ⟨p, hpk, hpS⟩ := Finset.not_disjoint_iff.1 hmeet
    have hpt : p ≠ g i := fun h' => htS (h' ▸ hpS)
    have := C.L.claim43 C.h (C.ln_Hs hkl)
    have h2 : ({g i, p} : Finset α) ⊆ ln g k ∩ ((e₁ ∪ e₂) \ {v₁, v₂}) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_inter.2 ⟨(mem_ln C.hg).2 hik, ht⟩
      · exact Finset.mem_inter.2 ⟨hpk, C.hS0 hpS⟩
    have := Finset.card_le_card h2
    rw [Finset.card_pair hpt.symm] at this
    omega
  have htl : t ∈ ln g' l' := by rw [hl', hS1]; exact Finset.mem_insert_self t _
  obtain ⟨i, hil', hgt⟩ := mem_ln_iff.1 htl
  obtain ⟨k₁, k₂, i', y, hk1, hk2, hik1, hil'', hii, hik2, hy1, hy2⟩ := F7_caseB l' i hil'
  have hgi' : g' i' ∈ S₀ := by
    have h1 : g' i' ∈ S₁ := by rw [← hl']; exact (mem_ln hg').2 hil''
    rw [hS1, Finset.mem_insert] at h1
    rcases h1 with h1 | h1
    · exact absurd (hg' (h1.trans hgt.symm)) hii
    · exact Finset.mem_of_mem_erase h1
  have hc2 : ¬ Disjoint (ln g' k₂) (verts (cop g)) :=
    Finset.not_disjoint_iff.2 ⟨g' i', (mem_ln hg').2 hik2, C.S0_verts_cop hgi'⟩
  have m2 : ln g' k₂ ∈ cop g := hcl.2 (ln g' k₂) (hlnHs k₂ hk2) hc2
  have hy : g' y ∈ verts (cop g) := subset_verts m2 ((mem_ln hg').2 hy2)
  have hc1 : ¬ Disjoint (ln g' k₁) (verts (cop g)) :=
    Finset.not_disjoint_iff.2 ⟨g' y, (mem_ln hg').2 hy1, hy⟩
  have m1 : ln g' k₁ ∈ cop g := hcl.2 (ln g' k₁) (hlnHs k₁ hk1) hc1
  have := subset_verts m1 ((mem_ln hg').2 hik1)
  rw [hgt] at this
  exact htR this

/-- Claim 4.5 when `S = S₀` (`|S| = 3`): then `H` is a copy of `H₁₀` or `H₁₀'`, which satisfies
Theorem 6 (its leaf `x` is exceptional). -/
lemma claim45A (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) (hcl : IsClosed (H3) (cop g))
    (hS : (e₁ ∪ e₂) \ {v₁, v₂} ⊆ S₀) : False := by
  have L := C.L
  have h := C.h
  set F : Finset (Finset α) := (Finset.univ.erase l).image (ln g) ∪ {{x, v₁, v₂}, e₁, e₂}
    with hFdef
  have hFE : F ⊆ E := by
    intro f hf
    rcases Finset.mem_union.1 hf with hf | hf
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hf
      exact del_subset _ _ (C.ln_Hs (Finset.ne_of_mem_erase hk))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl | rfl
      exacts [L.he, L.e1E, L.e2E]
  have hFcl : IsClosed E F := by
    refine ⟨hFE, fun f hf hmeet => ?_⟩
    by_cases h0 : f = {x, v₁, v₂} ∨ f = e₁ ∨ f = e₂
    · refine Finset.mem_union_right _ ?_
      simp only [Finset.mem_insert, Finset.mem_singleton]; exact h0
    push Not at h0
    have hfs : f ∈ Hs := L.mem_del12.2 ⟨hf, h0.1, h0.2.1, h0.2.2⟩
    obtain ⟨ax, av1, av2⟩ := L.avoid hf h0.1 h0.2.1 h0.2.2
    obtain ⟨u, huf, huF⟩ := Finset.not_disjoint_iff.1 hmeet
    obtain ⟨f', hf', huf'⟩ := mem_verts.1 huF
    have hux : u ≠ x := fun h' => ax (h' ▸ huf)
    have hu1 : u ≠ v₁ := fun h' => av1 (h' ▸ huf)
    have hu2 : u ≠ v₂ := fun h' => av2 (h' ▸ huf)
    have hu : u ∈ verts (cop g) := by
      rcases Finset.mem_union.1 hf' with hf' | hf'
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hf'
        exact subset_verts (mem_cop.2 ⟨k, rfl⟩) huf'
      · have hS' : u ∈ (e₁ ∪ e₂) \ {v₁, v₂} → u ∈ verts (cop g) := fun h' =>
          C.S0_verts_cop (hS h')
        simp only [Finset.mem_insert, Finset.mem_singleton] at hf'
        rcases hf' with rfl | rfl | rfl
        · simp only [Finset.mem_insert, Finset.mem_singleton] at huf'
          rcases huf' with h' | h' | h' <;> contradiction
        · exact hS' (by simp [huf', hu1, hu2])
        · exact hS' (by simp [huf', hu1, hu2])
    have hfc := hcl.2 f (Finset.mem_insert_of_mem hfs) (Finset.not_disjoint_iff.2 ⟨u, huf, hu⟩)
    obtain ⟨k, rfl⟩ := mem_cop.1 hfc
    have hk : k ≠ l := fun h' => C.S0_not_Hs (by rw [← C.hl, ← h']; exact hfs)
    exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨k, Finset.mem_erase.2 ⟨hk,
      Finset.mem_univ _⟩, rfl⟩)
  have hEF : F = E := h.closed_eq hFcl ⟨_, Finset.mem_union_right _ (Finset.mem_insert_self _ _)⟩
  -- the shape of `e₁`, `e₂`
  have hvS0 : ∀ v, (v = v₁ ∨ v = v₂) → v ∉ S₀ := by
    rintro v hv h'
    have := (Finset.mem_sdiff.1 (C.hS0 h')).2
    rcases hv with rfl | rfl <;> simp at this
  have sub1 : e₁.erase v₁ ⊆ S₀ := fun w hw => hS (Finset.mem_sdiff.2
    ⟨Finset.mem_union_left _ (Finset.mem_of_mem_erase hw), by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Finset.ne_of_mem_erase hw, fun h' => L.v2_not_e1 h.L (h' ▸ Finset.mem_of_mem_erase hw)⟩⟩)
  have sub2 : e₂.erase v₂ ⊆ S₀ := fun w hw => hS (Finset.mem_sdiff.2
    ⟨Finset.mem_union_right _ (Finset.mem_of_mem_erase hw), by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h' => L.v1_not_e2 h.L (h' ▸ Finset.mem_of_mem_erase hw), Finset.ne_of_mem_erase hw⟩⟩)
  obtain ⟨bα, hbS, he1, -⟩ := edge_form (h.L.card3 _ L.e1E) L.v1e1 sub1 C.hc (hvS0 v₁ (Or.inl rfl))
  obtain ⟨aα, haS, he2, -⟩ := edge_form (h.L.card3 _ L.e2E) L.v2e2 sub2 C.hc (hvS0 v₂ (Or.inr rfl))
  have hab : aα ≠ bα := by
    rintro rfl
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1
      (by rw [Finset.card_erase_of_mem haS, C.hc]; norm_num : 1 < (S₀.erase aα).card)
    have hp1 : p ∈ e₁ := by rw [he1]; exact Finset.mem_insert_of_mem hp
    have hq1 : q ∈ e₁ := by rw [he1]; exact Finset.mem_insert_of_mem hq
    have hp2 : p ∈ e₂ := by rw [he2]; exact Finset.mem_insert_of_mem hp
    have hq2 : q ∈ e₂ := by rw [he2]; exact Finset.mem_insert_of_mem hq
    exact L.e12 h.L (h.L.eq_of_two L.e1E L.e2E hpq hp1 hq1 hp2 hq2)
  have haS' : aα ∈ ln g l := by rw [C.hl]; exact haS
  have hbS' : bα ∈ ln g l := by rw [C.hl]; exact hbS
  obtain ⟨a', ha', rfl⟩ := mem_ln_iff.1 haS'
  obtain ⟨b', hb', rfl⟩ := mem_ln_iff.1 hbS'
  have hab' : a' ≠ b' := fun h' => hab (h' ▸ rfl)
  have hne : ∀ i, g i ≠ x ∧ g i ≠ v₁ ∧ g i ≠ v₂ := fun i => (C.verts_H3_ne (C.g_verts i)).2
  have hinj := ext10_injective C.hg L.x1 L.x2 L.v12 (fun i => (hne i).1) (fun i => (hne i).2.1)
    (fun i => (hne i).2.2)
  have hEq : E = (gadget l a' b').image (fun e => e.image (ext10 g x v₁ v₂)) := by
    rw [gadget_image C.hg, ← hEF, C.hl, ← he1, ← he2]
  apply h.bad
  refine ⟨?_, fun _ hne' => absurd ⟨x, L.dx, Or.inr ⟨E, ⟨subset_rfl, fun f hf _ => hf⟩,
    L.x_verts, l, a', b', ha', hb', hab', ext10 g x v₁ v₂, hinj, hEq⟩⟩ hne'⟩
  -- `τ(H) ≤ 4 = w(H) / 17`
  obtain ⟨T7, hT7, hcov, hcl'⟩ := F7_tr3 l a' ha'
  have hT7c : T7.card = 3 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT7
    rcases hT7 with rfl | rfl <;> rfl
  refine ⟨insert v₁ (T7.image g), fun f hf => ?_, ?_⟩
  · rw [← hEF] at hf
    rcases Finset.mem_union.1 hf with hf | hf
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hf
      obtain ⟨j, hjk, hjT⟩ := Finset.not_disjoint_iff.1 (hcov k (Finset.ne_of_mem_erase hk))
      exact ⟨g j, Finset.mem_inter.2 ⟨Finset.mem_image_of_mem g hjk,
        Finset.mem_insert_of_mem (Finset.mem_image_of_mem g hjT)⟩⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl | rfl
      · exact ⟨v₁, by simp⟩
      · exact ⟨v₁, Finset.mem_inter.2 ⟨L.v1e1, Finset.mem_insert_self _ _⟩⟩
      · obtain ⟨j, hjl, hjT⟩ := Finset.not_disjoint_iff.1 hcl'
        obtain ⟨hja, hjl⟩ := Finset.mem_erase.1 hjl
        refine ⟨g j, Finset.mem_inter.2 ⟨?_, Finset.mem_insert_of_mem (Finset.mem_image_of_mem g hjT)⟩⟩
        rw [he2]
        refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨fun h' => hja (C.hg h'), ?_⟩)
        rw [← C.hl]; exact Finset.mem_image_of_mem g hjl
  · have hTc : (insert v₁ (T7.image g)).card ≤ 4 := by
      have := Finset.card_insert_le v₁ (T7.image g)
      have := Finset.card_image_le (s := T7) (f := g)
      omega
    have hn : 10 ≤ (verts E).card := by
      have hsub : Finset.univ.image (ext10 g x v₁ v₂) ⊆ verts E := by
        intro w hw
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw
        unfold ext10
        split_ifs
        · exact (C.verts_H3_ne (C.g_verts _)).1
        · exact L.x_verts
        · exact L.v1_verts
        · exact L.v2_verts
      have := Finset.card_le_card hsub
      rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at this
    have hm : 7 ≤ E.card := by
      have hsub : (Finset.univ.erase l).image (ln g) ⊆ Hs := by
        intro f hf
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hf
        exact C.ln_Hs (Finset.ne_of_mem_erase hk)
      have := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ (fun a b h' => (ln_inj C.hg).1 h'),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
      have := C.card_Hs
      omega
    rw [C.wt_E]
    omega

/-- **Claim 4.5**: `R` is not a union of components of `H₃`. -/
lemma claim45 (C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l) (hcl : IsClosed (H3) (cop g)) : False := by
  by_cases hS : (e₁ ∪ e₂) \ {v₁, v₂} ⊆ S₀
  · exact C.claim45A hcl hS
  · rw [Finset.not_subset] at hS
    obtain ⟨t, ht, htS⟩ := hS
    exact C.claim45B hcl ht htS

end FCfg

namespace MinCex

variable {E : Finset (Finset α)}

/-- **Claim 4**: a minimal counterexample has no vertex of degree 1. -/
lemma claim4 (h : MinCex E) (x : α) : deg E x ≠ 1 := by
  intro hx
  obtain ⟨v₁, v₂, e₁, e₂, L⟩ := Leaf.exists_of_leaf h hx
  have hS3 : 3 ≤ ((e₁ ∪ e₂) \ {v₁, v₂}).card := by
    have hsub : e₁.erase v₁ ∪ e₂.erase v₂ ⊆ (e₁ ∪ e₂) \ {v₁, v₂} := by
      intro w hw
      simp only [Finset.mem_union, Finset.mem_erase] at hw
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        not_or]
      rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨Or.inl h2, h1, fun h' => L.v2_not_e1 h.L (h' ▸ h2)⟩
      · exact ⟨Or.inr h2, fun h' => L.v1_not_e2 h.L (h' ▸ h2), h1⟩
    have h1 := Finset.card_union_add_card_inter (e₁.erase v₁) (e₂.erase v₂)
    have h2 : (e₁.erase v₁ ∩ e₂.erase v₂).card ≤ 1 :=
      (Finset.card_le_card (Finset.inter_subset_inter (Finset.erase_subset _ _)
        (Finset.erase_subset _ _))).trans (h.L.linear _ L.e1E _ L.e2E (L.e12 h.L))
    rw [Finset.card_erase_of_mem L.v1e1, Finset.card_erase_of_mem L.v2e2,
      h.L.card3 _ L.e1E, h.L.card3 _ L.e2E] at h1
    have := Finset.card_le_card hsub
    omega
  obtain ⟨S₀, hS0, hc⟩ := Finset.exists_subset_card_eq hS3
  have h44 := L.claim44 h hS0 hc
  rw [F7Free_iff] at h44
  push Not at h44
  obtain ⟨g, hg, hall⟩ := h44
  change ∀ j, ln g j ∈ insert S₀ (del E {v₁, v₂}) at hall
  obtain ⟨l, hl⟩ : ∃ l, ln g l = S₀ := by
    by_contra hne
    push Not at hne
    have := h.F7.mono (del_subset E {v₁, v₂})
    rw [F7Free_iff] at this
    exact this g hg fun j => (Finset.mem_insert.1 (hall j)).resolve_left (hne j)
  have C : FCfg E x v₁ v₂ e₁ e₂ S₀ g l := ⟨L, h, hS0, hc, hg, hall, hl⟩
  by_cases hcl : IsClosed (insert S₀ (del E {v₁, v₂})) (cop g)
  · exact C.claim45 hcl
  · exact C.claim4_end hcl

end MinCex

end OpenProblemsLab.HY
