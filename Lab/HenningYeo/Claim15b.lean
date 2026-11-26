import Lab.HenningYeo.Claim15

/-!
# Henning–Yeo Claim 15, case B, and Claim 15
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

namespace MinCex

variable {E : Finset (Finset α)}

/-- The edges at a vertex of degree 3 other than a given one, as a pair. -/
lemma other_two {y : α} (hy : deg E y = 3) {e₀ f : Finset α} (he₀ : e₀ ∈ E) (hf : f ∈ E)
    (hye : y ∈ e₀) (hyf : y ∈ f) (hfe : f ≠ e₀) :
    ∃ g ∈ E, y ∈ g ∧ g ≠ e₀ ∧ g ≠ f ∧ ∀ k ∈ E, y ∈ k → k = e₀ ∨ k = f ∨ k = g := by
  obtain ⟨f₂, f₃, hf2, hf3, hy2, hy3, h2, h3, h23, hall⟩ := edges_three hy he₀ hye
  rcases hall f hf hyf with h' | rfl | rfl
  · exact absurd h' hfe
  · exact ⟨f₃, hf3, hy3, h3, Ne.symm h23, fun k hk hyk => by
      rcases hall k hk hyk with h' | h' | h' <;> simp [h']⟩
  · exact ⟨f₂, hf2, hy2, h2, h23, fun k hk hyk => by
      rcases hall k hk hyk with h' | h' | h' <;> simp [h']⟩

/-- Case B of Claim 15: `v j, v k` are not adjacent and `u i` is adjacent to `v j`. -/
lemma caseB (h : MinCex E) {x : α} {u v : Fin 3 → α} (N : Nx3 E x u v) {e : Finset α}
    (he : e ∈ E) (hue : ∀ t, u t ∈ e) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (nvv : ¬ Adj E (v j) (v k)) (hadj : Adj E (u i) (v j)) : False := by
  have hL := h.L
  have hreg := h.claim10
  have cov := fin3_cover hij hik hjk
  have hx3 := hreg x (N.x_verts hL)
  -- basic facts about `e`
  have hxe : x ∉ e := fun hx => N.u_not hL (by decide : (1 : Fin 3) ≠ 0)
    ((hL.eq_of_two he (N.m 0) (N.xu hL 0) hx (hue 0) (by simp) (by simp)) ▸ hue 1)
  have hve : ∀ t, v t ∉ e := fun t hvt => by
    obtain ⟨s, hst⟩ := fin3_third t t
    exact N.u_not hL hst.1 ((hL.eq_of_two he (N.m t) (N.uv hL t) (hue t) hvt (by simp)
      (by simp)) ▸ hue s)
  have hee : ∀ t, e ≠ {x, u t, v t} := fun t h' => hxe (h' ▸ by simp)
  obtain ⟨f, hf, huf, hvf⟩ := hadj
  have hkf : v k ∉ f := fun h' => nvv ⟨f, hf, hvf, h'⟩
  have allui := all3 (hreg _ (N.u_verts hL i)) he (N.m i) hf (hue i) (by simp) huf (hee i)
    (fun h' => hve j (h' ▸ hvf)) (fun h' => N.v_not hL (Ne.symm hij) (by rw [h']; exact hvf))
  have nik : ¬ Adj E (u i) (v k) := by
    rintro ⟨g, hg, hug, hvg⟩
    rcases allui g hg hug with rfl | rfl | rfl
    · exact hve k hvg
    · exact N.v_not hL (Ne.symm hik) hvg
    · exact hkf hvg
  have njk : ¬ Adj E (u j) (v k) := by
    rintro ⟨g, hg, hug, hvg⟩
    obtain ⟨gv, hgv, hvgv, hgv1, hgv2, -⟩ := other_two (hreg _ (N.v_verts hL j)) (N.m j) hf
      (by simp) hvf (fun h' => N.u_not hL hij (h' ▸ huf))
    have alluj := all3 (hreg _ (N.u_verts hL j)) (N.m j) he hg (by simp) (hue j) hug
      (fun h' => hee j h'.symm) (fun h' => N.v_not hL (Ne.symm hjk) (by rw [h']; exact hvg))
      (fun h' => hve k (h' ▸ hvg))
    have hugv : u i ∉ gv := fun h' => by
      rcases allui gv hgv h' with rfl | rfl | rfl
      · exact hve j hvgv
      · exact N.v_not hL (Ne.symm hij) hvgv
      · exact hgv2 rfl
    have hvgv' : v k ∉ gv := fun h' => nvv ⟨gv, hgv, hvgv, h'⟩
    refine h.claim14 (s₁ := u i) (s₂ := v k) (N.uv' hL hik) (N.u_verts hL i) (N.v_verts hL k)
      nik (N.m j) (N.u_not hL hij) (N.v_not hL (Ne.symm hjk)) ?_ ?_ hgv hgv1 hvgv hugv hvgv'
    · intro f' hf' hxf' hne
      obtain ⟨t, rfl⟩ := N.hall hL hx3 f' hf' hxf'
      rcases cov t with rfl | rfl | rfl
      · exact Or.inl (by simp)
      · exact absurd rfl hne
      · exact Or.inr (by simp)
    · intro f' hf' huf' hne
      rcases alluj f' hf' huf' with h' | h' | h'
      · exact absurd h' hne
      · exact Or.inl (h' ▸ hue i)
      · exact Or.inr (h' ▸ hvg)
  have hkj : Adj E (u k) (v j) := by
    by_contra hn2
    -- every edge at `v i` other than `e_i` meets `{u k, v j}`
    have hvi : ∀ g ∈ E, v i ∈ g → g ≠ {x, u i, v i} → u k ∈ g ∨ v j ∈ g := by
      intro g hg hvg hne
      by_contra hc
      push Not at hc
      refine h.claim14 (s₁ := u k) (s₂ := v j) (N.uv' hL hjk.symm) (N.u_verts hL k)
        (N.v_verts hL j) hn2 (N.m i) (N.u_not hL (Ne.symm hik)) (N.v_not hL (Ne.symm hij)) ?_ ?_ hg
        hne hvg hc.1 hc.2
      · intro f' hf' hxf' hne'
        obtain ⟨t, rfl⟩ := N.hall hL hx3 f' hf' hxf'
        rcases cov t with rfl | rfl | rfl
        · exact absurd rfl hne'
        · exact Or.inr (by simp)
        · exact Or.inl (by simp)
      · intro f' hf' huf' hne'
        rcases allui f' hf' huf' with h' | h' | h'
        · exact Or.inl (h' ▸ hue k)
        · exact absurd h' hne'
        · exact Or.inr (h' ▸ hvf)
    obtain ⟨f₂, f₃, hf2, hf3, hv2, hv3, h2, h3, h23, hallv⟩ :=
      edges_three (hreg _ (N.v_verts hL i)) (N.m i) (by simp)
    have hik' : u k ≠ v i := N.uv' hL (Ne.symm hik)
    have hjv : v j ≠ v i := N.vv hL (Ne.symm hij)
    -- one of `f₂, f₃` contains `u k`, the other `v j`
    obtain ⟨f', f'', hf', hf'', hvf', hvf'', hukf', hvjf'', hf'1, hf''1, hallv'⟩ :
        ∃ f' f'', f' ∈ E ∧ f'' ∈ E ∧ v i ∈ f' ∧ v i ∈ f'' ∧ u k ∈ f' ∧ v j ∈ f'' ∧
          f' ≠ {x, u i, v i} ∧ f'' ≠ {x, u i, v i} ∧
          ∀ g ∈ E, v i ∈ g → g = {x, u i, v i} ∨ g = f' ∨ g = f'' := by
      rcases hvi f₂ hf2 hv2 h2 with a2 | a2 <;> rcases hvi f₃ hf3 hv3 h3 with a3 | a3
      · exact absurd (hL.eq_of_two hf2 hf3 hik' a2 hv2 a3 hv3) h23
      · exact ⟨f₂, f₃, hf2, hf3, hv2, hv3, a2, a3, h2, h3, hallv⟩
      · exact ⟨f₃, f₂, hf3, hf2, hv3, hv2, a3, a2, h3, h2, fun g hg hvg => by
          rcases hallv g hg hvg with h' | h' | h' <;> simp [h']⟩
      · exact absurd (hL.eq_of_two hf2 hf3 hjv a2 hv2 a3 hv3) h23
    have nij : ¬ Adj E (v i) (u j) := by
      rintro ⟨g, hg, hvg, hug⟩
      rcases hallv' g hg hvg with rfl | rfl | rfl
      · exact N.u_not hL hij.symm hug
      · have : g = e := hL.eq_of_two hg he (N.uu hL hjk.symm) hukf' hug (hue k) (hue j)
        exact hve i (this ▸ hvg)
      · have : g = {x, u j, v j} := hL.eq_of_two hg (N.m j) (N.uv hL j) hug hvjf'' (by simp)
          (by simp)
        exact N.v_not hL hij (this ▸ hvg)
    have alluk := all3 (hreg _ (N.u_verts hL k)) (N.m k) he hf' (by simp) (hue k) hukf'
      (fun h' => hee k h'.symm) (fun h' => N.v_not hL hik (by rw [h']; exact hvf'))
      (fun h' => hve i (h' ▸ hvf'))
    obtain ⟨g, -, hg, -, hvkg, -, hg1, -, -, -⟩ :=
      edges_three (hreg _ (N.v_verts hL k)) (N.m k) (by simp)
    have hvig : v i ∉ g := fun h' => by
      rcases hallv' g hg h' with h'' | h'' | h''
      · exact N.v_not hL (Ne.symm hik) (h'' ▸ hvkg)
      · have : f' = {x, u k, v k} := hL.eq_of_two hf' (N.m k) (N.uv hL k) hukf' (h'' ▸ hvkg)
          (by simp) (by simp)
        exact N.v_not hL hik (this ▸ hvf')
      · exact nvv ⟨f'', hf'', hvjf'', h'' ▸ hvkg⟩
    have hujg : u j ∉ g := fun h' => njk ⟨g, hg, h', hvkg⟩
    refine h.claim14 (s₁ := v i) (s₂ := u j) (N.vu hL hij) (N.v_verts hL i) (N.u_verts hL j) nij
      (N.m k) (N.v_not hL hik) (N.u_not hL hjk) ?_ ?_ hg hg1 hvkg hvig hujg
    · intro f₀ hf₀ hxf₀ hne
      obtain ⟨t, rfl⟩ := N.hall hL hx3 f₀ hf₀ hxf₀
      rcases cov t with rfl | rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr (by simp)
      · exact absurd rfl hne
    · intro f₀ hf₀ huf₀ hne
      rcases alluk f₀ hf₀ huf₀ with h' | h' | h'
      · exact absurd h' hne
      · exact Or.inr (h' ▸ hue j)
      · exact Or.inl (h' ▸ hvf')
  obtain ⟨g', hg', hukg', hvjg'⟩ := hkj
  have alluk := all3 (hreg _ (N.u_verts hL k)) he (N.m k) hg' (hue k) (by simp) hukg' (hee k)
    (fun h' => hve j (h' ▸ hvjg')) (fun h' => N.v_not hL hjk (by rw [h']; exact hvjg'))
  refine h.claim13' (a := u i) (b := v j) (c := v k) (N.u_verts hL i) (N.v_verts hL j)
    (N.v_verts hL k) (N.uv' hL hij) nik nvv (N.xu hL k) ⟨N.xu hL i, N.xv hL j, N.xv hL k⟩
    ⟨N.uu hL (Ne.symm hik), N.uv' hL (Ne.symm hjk), N.uv hL k⟩ (N.x_verts hL) (N.u_verts hL k)
    ?_ ?_
  · intro f₀ hf₀ hxf₀
    obtain ⟨t, rfl⟩ := N.hall hL hx3 f₀ hf₀ hxf₀
    rcases cov t with rfl | rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl (by simp))
    · exact Or.inr (Or.inr (by simp))
  · intro f₀ hf₀ huf₀
    rcases alluk f₀ hf₀ huf₀ with h' | h' | h'
    · exact Or.inl (h' ▸ hue i)
    · exact Or.inr (Or.inr (h' ▸ by simp))
    · exact Or.inr (Or.inl (h' ▸ hvjg'))

end MinCex

end OpenProblemsLab.HY
