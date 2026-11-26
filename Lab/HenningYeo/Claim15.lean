import Lab.HenningYeo.Claim13

/-!
# Henning–Yeo Claim 15: no edge lies inside a neighbourhood `N(x)`

We name the three edges at a vertex `x` as `{x, u t, v t}` (`t : Fin 3`); see `Nx3`.
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-- The three edges `{x, u t, v t}` at `x`. -/
structure Nx3 (E : Finset (Finset α)) (x : α) (u v : Fin 3 → α) : Prop where
  m : ∀ t, ({x, u t, v t} : Finset α) ∈ E
  n : ∀ s t, s ≠ t → ({x, u s, v s} : Finset α) ≠ {x, u t, v t}

lemma fin3_cover {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∀ t, t = i ∨ t = j ∨ t = k := by
  revert i j k; decide

lemma fin3_third (i j : Fin 3) : ∃ k, k ≠ i ∧ k ≠ j := by
  fin_cases i <;> fin_cases j <;> decide

namespace Nx3

variable {E : Finset (Finset α)} {x : α} {u v : Fin 3 → α}
set_option linter.unusedSectionVars false

variable (N : Nx3 E x u v) (hL : IsL3 E)
include N hL

lemma xu (t : Fin 3) : x ≠ u t := (ne_of_card3 (hL.card3 _ (N.m t))).1
lemma xv (t : Fin 3) : x ≠ v t := (ne_of_card3 (hL.card3 _ (N.m t))).2.1
lemma uv (t : Fin 3) : u t ≠ v t := (ne_of_card3 (hL.card3 _ (N.m t))).2.2

lemma u_not {s t : Fin 3} (hst : s ≠ t) : u s ∉ ({x, u t, v t} : Finset α) := fun h' =>
  N.n s t hst (hL.eq_of_two (N.m s) (N.m t) (N.xu hL s) (by simp) (by simp) (by simp) h')

lemma v_not {s t : Fin 3} (hst : s ≠ t) : v s ∉ ({x, u t, v t} : Finset α) := fun h' =>
  N.n s t hst (hL.eq_of_two (N.m s) (N.m t) (N.xv hL s) (by simp) (by simp) (by simp) h')

lemma uu {s t : Fin 3} (hst : s ≠ t) : u s ≠ u t := fun h' => N.u_not hL hst (by simp [h'])
lemma uv' {s t : Fin 3} (hst : s ≠ t) : u s ≠ v t := fun h' => N.u_not hL hst (by simp [h'])
lemma vu {s t : Fin 3} (hst : s ≠ t) : v s ≠ u t := fun h' => N.v_not hL hst (by simp [h'])
lemma vv {s t : Fin 3} (hst : s ≠ t) : v s ≠ v t := fun h' => N.v_not hL hst (by simp [h'])

lemma hall (hx : deg E x = 3) : ∀ f ∈ E, x ∈ f → ∃ t, f = {x, u t, v t} := by
  intro f hf hxf
  rcases all3 hx (N.m 0) (N.m 1) (N.m 2) (by simp) (by simp) (by simp) (N.n 0 1 (by decide))
    (N.n 0 2 (by decide)) (N.n 1 2 (by decide)) f hf hxf with h' | h' | h'
  · exact ⟨0, h'⟩
  · exact ⟨1, h'⟩
  · exact ⟨2, h'⟩

lemma nbr_cases (hx : deg E x = 3) {a : α} (ha : a ∈ nbr E {x}) : ∃ t, a = u t ∨ a = v t := by
  obtain ⟨hax, f, hf, hxf, haf⟩ := mem_nbr_singleton.1 ha
  obtain ⟨t, rfl⟩ := N.hall hL hx f hf hxf
  simp only [Finset.mem_insert, Finset.mem_singleton] at haf
  rcases haf with h' | h' | h'
  · exact absurd h' hax
  · exact ⟨t, Or.inl h'⟩
  · exact ⟨t, Or.inr h'⟩

lemma u_nbr (t : Fin 3) : u t ∈ nbr E {x} :=
  MinCex.mem_nbr_of (N.m t) (by simp) (by simp) (Ne.symm (N.xu hL t))
lemma v_nbr (t : Fin 3) : v t ∈ nbr E {x} :=
  MinCex.mem_nbr_of (N.m t) (by simp) (by simp) (Ne.symm (N.xv hL t))

lemma x_verts : x ∈ verts E := subset_verts (N.m 0) (by simp)
lemma u_verts (t : Fin 3) : u t ∈ verts E := subset_verts (N.m t) (by simp)
lemma v_verts (t : Fin 3) : v t ∈ verts E := subset_verts (N.m t) (by simp)

/-- `x` together with an edge through `u 0, u 1, u 2` and an edge through `v 0, v 1, v 2` would
form a copy of `F₇`. -/
lemma noF7 (hF : F7Free E) {e : Finset α} (he : e ∈ E) (hue : ∀ t, u t ∈ e) {f : Finset α}
    (hf : f ∈ E) (hvf : ∀ t, v t ∈ f) : False := by
  have hd := fun {s t : Fin 3} (h : s ≠ t) =>
    (⟨N.uu hL h, N.uv' hL h, N.vu hL h, N.vv hL h⟩ : _ ∧ _ ∧ _ ∧ _)
  have he' : e = {u 0, u 1, u 2} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> exact hue _
    · rw [hL.card3 e he, Finset.card_insert_of_notMem (by simp [(hd (by decide : (0 : Fin 3) ≠ 1)).1,
        (hd (by decide : (0 : Fin 3) ≠ 2)).1]), Finset.card_pair (hd (by decide : (1 : Fin 3) ≠ 2)).1]
  have hf' : f = {v 0, v 1, v 2} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> exact hvf _
    · rw [hL.card3 f hf, Finset.card_insert_of_notMem (by
        simp [(hd (by decide : (0 : Fin 3) ≠ 1)).2.2.2, (hd (by decide : (0 : Fin 3) ≠ 2)).2.2.2]),
        Finset.card_pair (hd (by decide : (1 : Fin 3) ≠ 2)).2.2.2]
  refine hF ![x, u 0, v 0, u 1, v 1, u 2, v 2] ?_ ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hd (by decide : (0 : Fin 3) ≠ 1)
    obtain ⟨b1, b2, b3, b4⟩ := hd (by decide : (0 : Fin 3) ≠ 2)
    obtain ⟨c1, c2, c3, c4⟩ := hd (by decide : (1 : Fin 3) ≠ 2)
    have x0 := N.xu hL 0; have x1 := N.xu hL 1; have x2 := N.xu hL 2
    have y0 := N.xv hL 0; have y1 := N.xv hL 1; have y2 := N.xv hL 2
    have z0 := N.uv hL 0; have z1 := N.uv hL 1; have z2 := N.uv hL 2
    intro a b hab
    fin_cases a <;> fin_cases b <;> first
      | rfl
      | (simp at hab; first | exact absurd hab (by assumption) | exact absurd hab.symm (by assumption))
  · simpa using N.m 0
  · simpa using N.m 1
  · simpa using N.m 2
  · simpa [he'] using he
  · simpa [hf'] using hf

end Nx3

namespace MinCex

variable {E : Finset (Finset α)}

/-- Case A of Claim 15: the `v`'s are pairwise adjacent. -/
lemma caseA (h : MinCex E) {x : α} {u v : Fin 3 → α} (N : Nx3 E x u v) {e : Finset α}
    (he : e ∈ E) (hue : ∀ t, u t ∈ e) (tri : ∀ s t, s ≠ t → Adj E (v s) (v t)) {i j : Fin 3}
    (hij : i ≠ j) (hn : ¬ Adj E (u i) (v j)) : False := by
  have hL := h.L
  have hreg := h.claim10
  obtain ⟨k, hki, hkj⟩ := fin3_third i j
  have cov := fin3_cover hij (Ne.symm hki) (Ne.symm hkj)
  have hx3 := hreg x (N.x_verts hL)
  have allv : ∀ {f : Finset α}, f ∈ E → v i ∈ f → v j ∈ f → v k ∈ f → False := by
    intro f hf hi hj hk
    refine N.noF7 hL h.F7 he hue hf fun t => ?_
    rcases cov t with rfl | rfl | rfl <;> assumption
  obtain ⟨fji, hfji, hj1, hi1⟩ := tri j i (Ne.symm hij)
  obtain ⟨fjk, hfjk, hj2, hk2⟩ := tri j k (Ne.symm hkj)
  obtain ⟨fik, hfik, hi3, hk3⟩ := tri i k (Ne.symm hki)
  have d1 : fji ≠ fjk := fun h' => allv hfji hi1 hj1 (h' ▸ hk2)
  have d2 : fji ≠ fik := fun h' => allv hfji hi1 hj1 (h' ▸ hk3)
  have d3 : fjk ≠ fik := fun h' => allv hfjk (h' ▸ hi3) hj2 hk2
  -- the edges at `v i` and at `v k`
  have alli := all3 (hreg _ (N.v_verts hL i)) (N.m i) hfji hfik (by simp) hi1 hi3
    (fun h' => N.v_not hL (Ne.symm hij) (by rw [h']; exact hj1))
    (fun h' => N.v_not hL hki (by rw [h']; exact hk3)) d2
  have allk := all3 (hreg _ (N.v_verts hL k)) (N.m k) hfjk hfik (by simp) hk2 hk3
    (fun h' => N.v_not hL (Ne.symm hkj) (by rw [h']; exact hj2))
    (fun h' => N.v_not hL (Ne.symm hki) (by rw [h']; exact hi3)) d3
  have nik : ¬ Adj E (u i) (v k) := by
    rintro ⟨g, hg, hug, hvg⟩
    rcases allk g hg hvg with h' | h' | h'
    · rw [h'] at hug; exact N.u_not hL (Ne.symm hki) hug
    · rw [h'] at hug; exact hn ⟨fjk, hfjk, hug, hj2⟩
    · rw [h'] at hug
      have : fik = {x, u i, v i} :=
        hL.eq_of_two hfik (N.m i) (N.uv hL i) hug hi3 (by simp) (by simp)
      exact N.v_not hL hki (this ▸ hk3)
  refine h.claim13' (a := v j) (b := v k) (c := u i) (N.v_verts hL j) (N.v_verts hL k)
    (N.u_verts hL i) (N.vv hL (Ne.symm hkj)) (fun h' => hn h'.symm) (fun h' => nik h'.symm)
    (N.xv hL i) ⟨N.xv hL j, N.xv hL k, N.xu hL i⟩
    ⟨N.vv hL hij, N.vv hL (Ne.symm hki), (N.uv hL i).symm⟩
    (N.x_verts hL) (N.v_verts hL i) ?_ ?_
  · intro f hf hxf
    obtain ⟨t, rfl⟩ := N.hall hL hx3 f hf hxf
    rcases cov t with rfl | rfl | rfl
    · exact Or.inr (Or.inr (by simp))
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl (by simp))
  · intro f hf hvf
    rcases alli f hf hvf with rfl | rfl | rfl
    · exact Or.inr (Or.inr (by simp))
    · exact Or.inl hj1
    · exact Or.inr (Or.inl hk3)

end MinCex

end OpenProblemsLab.HY
