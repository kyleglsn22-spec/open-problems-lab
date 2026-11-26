import Lab.HenningYeo.Claim15b
import Lab.HenningYeo.Theorem7

/-!
# Henning–Yeo Theorem 6

Claim 15 and the final contradiction: a minimal counterexample cannot exist, so every linear
3-uniform `F₇`-free hypergraph satisfies `17 τ ≤ 4n + 4m + h` (`theorem6`).
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

lemma Nx3.mk7 {E : Finset (Finset α)} {x a₀ b₀ a₁ b₁ a₂ b₂ : α}
    (h0 : ({x, a₀, b₀} : Finset α) ∈ E) (h1 : ({x, a₁, b₁} : Finset α) ∈ E)
    (h2 : ({x, a₂, b₂} : Finset α) ∈ E) (d01 : ({x, a₀, b₀} : Finset α) ≠ {x, a₁, b₁})
    (d02 : ({x, a₀, b₀} : Finset α) ≠ {x, a₂, b₂}) (d12 : ({x, a₁, b₁} : Finset α) ≠ {x, a₂, b₂}) :
    Nx3 E x ![a₀, a₁, a₂] ![b₀, b₁, b₂] := by
  refine ⟨fun t => ?_, fun s t hst => ?_⟩
  · fin_cases t
    · exact h0
    · exact h1
    · exact h2
  · fin_cases s <;> fin_cases t
    all_goals first
      | exact absurd rfl hst
      | exact d01 | exact d02 | exact d12 | exact d01.symm | exact d02.symm | exact d12.symm

namespace MinCex

variable {E : Finset (Finset α)}

/-- **Claim 15**: no edge lies inside the neighbourhood of a vertex. -/
lemma claim15 (h : MinCex E) {y a b c : α} (he : ({a, b, c} : Finset α) ∈ E) (hya : y ≠ a)
    (hyb : y ≠ b) (hyc : y ≠ c) (ha : Adj E y a) (hb : Adj E y b) (hc : Adj E y c) : False := by
  have hL := h.L
  have hreg := h.claim10
  obtain ⟨hab, hac, hbc⟩ := ne_of_card3 (hL.card3 _ he)
  have third : ∀ {w}, y ≠ w → Adj E y w → ∃ w', ({y, w, w'} : Finset α) ∈ E := by
    rintro w hyw ⟨f, hf, hyf, hwf⟩
    obtain ⟨r, hr, -, -⟩ := exists_third_of_card3 (hL.card3 f hf) hyf hwf hyw
    exact ⟨r, hr ▸ hf⟩
  obtain ⟨a', ha'⟩ := third hya ha
  obtain ⟨b', hb'⟩ := third hyb hb
  obtain ⟨c', hc'⟩ := third hyc hc
  have hy : y ∉ ({a, b, c} : Finset α) := by simp [hya, hyb, hyc]
  have key : ∀ {p q p' q' : α}, p ∈ ({a, b, c} : Finset α) → q ∈ ({a, b, c} : Finset α) →
      p ≠ q → ({y, p, p'} : Finset α) ∈ E → ({y, p, p'} : Finset α) ≠ {y, q, q'} := by
    intro p q p' q' hp hq hpq hpE heq
    have : ({y, p, p'} : Finset α) = {a, b, c} :=
      hL.eq_of_two hpE he hpq (by simp) (by rw [heq]; simp) hp hq
    exact hy (this ▸ by simp)
  have N : Nx3 E y ![a, b, c] ![a', b', c'] := Nx3.mk7 ha' hb' hc'
    (key (by simp) (by simp) hab ha') (key (by simp) (by simp) hac ha')
    (key (by simp) (by simp) hbc hb')
  set u : Fin 3 → α := ![a, b, c]
  set v : Fin 3 → α := ![a', b', c']
  have hue : ∀ t, u t ∈ ({a, b, c} : Finset α) := by
    intro t; fin_cases t <;> simp [u]
  have hy3 := hreg y (N.x_verts hL)
  by_cases tri : ∀ s t, s ≠ t → Adj E (v s) (v t)
  · obtain ⟨p, hp, q, hq, hpq, hnpq⟩ := h.claim12 (N.x_verts hL)
    obtain ⟨s, hs⟩ := N.nbr_cases hL hy3 hp
    obtain ⟨t, ht⟩ := N.nbr_cases hL hy3 hq
    by_cases hst : s = t
    · subst hst
      apply hnpq
      refine ⟨_, N.m s, ?_, ?_⟩
      · rcases hs with rfl | rfl <;> simp
      · rcases ht with rfl | rfl <;> simp
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact hnpq ⟨_, he, hue s, hue t⟩
    · exact h.caseA N he hue tri hst hnpq
    · exact h.caseA N he hue tri (Ne.symm hst) (fun h' => hnpq h'.symm)
    · exact hnpq (tri s t hst)
  · push Not at tri
    obtain ⟨j, k, hjk, hn⟩ := tri
    obtain ⟨i, hij, hik⟩ := fin3_third j k
    by_cases h1 : Adj E (u i) (v j)
    · exact h.caseB N he hue hij hik hjk hn h1
    by_cases h2 : Adj E (u i) (v k)
    · exact h.caseB N he hue hik hij (Ne.symm hjk) (fun h' => hn h'.symm) h2
    exact h.claim11' (N.u_nbr hL i) (N.v_nbr hL j) (N.v_nbr hL k) (N.uv' hL hij) (N.uv' hL hik)
      (N.vv hL hjk) h1 h2 hn

/-- The final step of Theorem 6. -/
lemma finalF (h : MinCex E) {x : α} {u v : Fin 3 → α} (N : Nx3 E x u v) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hn : ¬ Adj E (v j) (u k))
    (ha : Adj E (u i) (u k)) : False := by
  have hL := h.L
  have hreg := h.claim10
  have cov := fin3_cover hij hik hjk
  have hx3 := hreg x (N.x_verts hL)
  have axu : ∀ t, Adj E (u t) x := fun t => adj_of_mem (N.m t) (by simp) (by simp)
  have axv : ∀ t, Adj E (v t) x := fun t => adj_of_mem (N.m t) (by simp) (by simp)
  have nvik : ¬ Adj E (v i) (u k) := fun h' => h.claim15 (y := u k) (N.m i) (N.xu hL k).symm
    (N.uu hL (Ne.symm hik)) (N.uv' hL (Ne.symm hik)) (axu k) ha.symm h'.symm
  have nuivk : ¬ Adj E (u i) (v k) := fun h' => h.claim15 (y := u i) (N.m k) (N.xu hL i).symm
    (N.uu hL hik) (N.uv' hL hik) (axu i) ha h'
  have avij : Adj E (v i) (v j) := by
    by_contra h'
    exact h.claim11' (N.v_nbr hL i) (N.v_nbr hL j) (N.u_nbr hL k) (N.vv hL hij) (N.vu hL hik)
      (N.vu hL hjk) h' nvik hn
  have nviuj : ¬ Adj E (v i) (u j) := fun h' => h.claim15 (y := v i) (N.m j) (N.xv hL i).symm
    (N.vu hL hij) (N.vv hL hij) (axv i) h' avij
  have nuivj : ¬ Adj E (u i) (v j) := fun h' => h.claim15 (y := v j) (N.m i) (N.xv hL j).symm
    (N.vu hL (Ne.symm hij)) (N.vv hL (Ne.symm hij)) (axv j) h'.symm avij.symm
  have avjk : Adj E (v j) (v k) := by
    by_contra h'
    exact h.claim11' (N.u_nbr hL i) (N.v_nbr hL j) (N.v_nbr hL k) (N.uv' hL hij) (N.uv' hL hik)
      (N.vv hL hjk) nuivj nuivk h'
  have nujvk : ¬ Adj E (u j) (v k) := fun h' => h.claim15 (y := v k) (N.m j) (N.xv hL k).symm
    (N.vu hL (Ne.symm hjk)) (N.vv hL (Ne.symm hjk)) (axv k) h'.symm avjk.symm
  have avik : Adj E (v i) (v k) := by
    by_contra h'
    exact h.claim11' (N.v_nbr hL i) (N.u_nbr hL j) (N.v_nbr hL k) (N.vu hL hij) (N.vv hL hik)
      (N.uv' hL hjk) nviuj h' nujvk
  obtain ⟨fij, hfij, hi1, hj1⟩ := avij
  obtain ⟨fjk, hfjk, hj2, hk2⟩ := avjk
  have hd : fij ≠ fjk := by
    intro h'
    have hk1 : v k ∈ fij := h' ▸ hk2
    have hf : fij = {v i, v j, v k} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> assumption
      · rw [hL.card3 fij hfij, Finset.card_insert_of_notMem (by
          simp [N.vv hL hij, N.vv hL hik]), Finset.card_pair (N.vv hL hjk)]
    exact h.claim15 (y := x) (hf ▸ hfij) (N.xv hL i) (N.xv hL j) (N.xv hL k) (axv i).symm
      (axv j).symm (axv k).symm
  have allvj := all3 (hreg _ (N.v_verts hL j)) (N.m j) hfij hfjk (by simp) hj1 hj2
    (fun h' => N.v_not hL hij (by rw [h']; exact hi1))
    (fun h' => N.v_not hL (Ne.symm hjk) (by rw [h']; exact hk2)) hd
  refine h.claim13' (a := v i) (b := v k) (c := u j) (N.v_verts hL i) (N.v_verts hL k)
    (N.u_verts hL j) (N.vv hL hik) nviuj (fun h' => nujvk h'.symm) (N.xv hL j)
    ⟨N.xv hL i, N.xv hL k, N.xu hL j⟩
    ⟨N.vv hL (Ne.symm hij), N.vv hL hjk, (N.uv hL j).symm⟩ (N.x_verts hL) (N.v_verts hL j) ?_ ?_
  · intro f hf hxf
    obtain ⟨t, rfl⟩ := N.hall hL hx3 f hf hxf
    rcases cov t with rfl | rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inr (by simp))
    · exact Or.inr (Or.inl (by simp))
  · intro f hf hvf
    rcases allvj f hf hvf with rfl | rfl | rfl
    · exact Or.inr (Or.inr (by simp))
    · exact Or.inl hi1
    · exact Or.inr (Or.inl hk2)

/-- A minimal counterexample does not exist. -/
lemma false (h : MinCex E) : False := by
  have hL := h.L
  have hreg := h.claim10
  obtain ⟨e₀, he₀⟩ := h.nonempty
  obtain ⟨x, hx⟩ : e₀.Nonempty := Finset.card_pos.1 (by rw [hL.card3 e₀ he₀]; omega)
  have hxE : x ∈ verts E := subset_verts he₀ hx
  have hx3 := hreg x hxE
  obtain ⟨p, hp, q, hq, hpq, hnpq⟩ := h.claim12 hxE
  obtain ⟨hpx, fp, hfp, hxfp, hpfp⟩ := mem_nbr_singleton.1 hp
  obtain ⟨hqx, fq, hfq, hxfq, hqfq⟩ := mem_nbr_singleton.1 hq
  have hfpq : fq ≠ fp := fun h' => hnpq ⟨fp, hfp, hpfp, h' ▸ hqfq⟩
  obtain ⟨fr, hfr, hxfr, hrp, hrq, -⟩ := other_two hx3 hfp hfq hxfp hxfq hfpq
  obtain ⟨p', hp', -, -⟩ := exists_third_of_card3 (hL.card3 fp hfp) hxfp hpfp (Ne.symm hpx)
  obtain ⟨q', hq', -, -⟩ := exists_third_of_card3 (hL.card3 fq hfq) hxfq hqfq (Ne.symm hqx)
  obtain ⟨r, hr⟩ : (fr.erase x).Nonempty :=
    Finset.card_pos.1 (by rw [Finset.card_erase_of_mem hxfr, hL.card3 fr hfr]; omega)
  obtain ⟨hrx, hrfr⟩ := Finset.mem_erase.1 hr
  obtain ⟨r', hr', -, -⟩ := exists_third_of_card3 (hL.card3 fr hfr) hxfr hrfr (Ne.symm hrx)
  have hp'' : ({x, p', p} : Finset α) = fp := by rw [Finset.pair_comm]; exact hp'.symm
  have hq'' : ({x, q', q} : Finset α) = fq := by rw [Finset.pair_comm]; exact hq'.symm
  have N₁ : Nx3 E x ![r, p', q] ![r', p, q'] := Nx3.mk7 (hr' ▸ hfr) (hp'' ▸ hfp) (hq' ▸ hfq)
    (by rw [← hr', hp'']; exact hrp) (by rw [← hr', ← hq']; exact hrq)
    (by rw [hp'', ← hq']; exact hfpq.symm)
  have N₂ : Nx3 E x ![r, p, q'] ![r', p', q] := Nx3.mk7 (hr' ▸ hfr) (hp' ▸ hfp) (hq'' ▸ hfq)
    (by rw [← hr', ← hp']; exact hrp) (by rw [← hr', hq'']; exact hrq)
    (by rw [← hp', hq'']; exact hfpq.symm)
  by_cases A1 : Adj E r q
  · exact h.finalF N₁ (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide) hnpq A1
  by_cases A2 : Adj E r p
  · exact h.finalF N₂ (i := 0) (j := 2) (k := 1) (by decide) (by decide) (by decide)
      (fun h' => hnpq h'.symm) A2
  exact h.claim11' (a := r) (b := p) (c := q) (N₁.u_nbr hL 0) hp hq
    (N₁.uv' hL (s := 0) (t := 1) (by decide)) (N₁.uu hL (s := 0) (t := 2) (by decide)) hpq A2 A1
    hnpq

end MinCex

/-- Every linear 3-uniform `F₇`-free hypergraph satisfies Theorem 6 (`Goal6`). -/
theorem goal6_all : ∀ E : Finset (Finset α), IsL3 E → F7Free E → Goal6 E := by
  intro E
  induction hn : sz E using Nat.strong_induction_on generalizing E with
  | _ n ih =>
    intro hL hF
    by_contra hbad
    exact MinCex.false ⟨hL, hF, fun E' hlt hL' hF' => ih (sz E') (hn ▸ hlt) E' rfl hL' hF', hbad⟩

/-- **Henning–Yeo Theorem 6** (first half): `17 τ(H) ≤ 4n + 4m + h` for every linear 3-uniform
hypergraph `H` without a copy of `F₇`. -/
theorem theorem6 : Theorem6Bound α := fun E hL hF => (goal6_all E hL hF).1

end OpenProblemsLab.HY
