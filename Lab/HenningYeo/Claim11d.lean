import Lab.HenningYeo.Claim11c

/-!
# Henning–Yeo Claim 11, part 4: Claims 11.2, 11.3 and Claim 11

**Claim 11**: in a minimal counterexample, no vertex has three pairwise non-adjacent neighbours.
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-- Double counting: if every `t ∈ T` lies in at least two of the sets `N s ∩ T` (`s ∈ S`). -/
lemma two_card_le_sum {S T : Finset α} (N : α → Finset α)
    (h : ∀ t ∈ T, 2 ≤ (S.filter (fun s => t ∈ N s)).card) :
    2 * T.card ≤ ∑ s ∈ S, (N s ∩ T).card := by
  have heq : ∑ s ∈ S, (N s ∩ T).card = ∑ t ∈ T, (S.filter (fun s => t ∈ N s)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
  rw [heq]
  calc 2 * T.card = ∑ _t ∈ T, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ _ := Finset.sum_le_sum h

namespace C11

variable {E : Finset (Finset α)} {x : α} {S e₁ e₂ : Finset α}
variable (C : C11 E x S e₁ e₂)
include C

lemma s_not_T {s : α} (hs : s ∈ S) : s ∉ e₁ ∪ e₂ := fun h' => C.S_gone hs (C.T_verts h')

lemma deg_s {s : α} (hs : s ∈ S) : deg E s = 3 :=
  C.reg s (C.xS_verts (Finset.mem_insert_of_mem hs))

lemma inter_e_le {s : α} (hs : s ∈ S) {f : Finset α} (hf : f ∈ E) (hsf : s ∈ f) :
    (f ∩ e₁).card ≤ 1 ∧ (f ∩ e₂).card ≤ 1 := by
  refine ⟨C.h.L.linear f hf e₁ C.mem1 fun h' => C.s_not_T hs ?_,
    C.h.L.linear f hf e₂ C.mem2 fun h' => C.s_not_T hs ?_⟩
  · exact Finset.mem_union_left _ (h' ▸ hsf)
  · exact Finset.mem_union_right _ (h' ▸ hsf)

/-- The vertices of an edge meeting `S` lie in `R ∪ Q`. -/
lemma mem_RQ' {g : Finset α} (hg : g ∈ hit E S) {v : α} (hv : v ∈ g) :
    v ∈ R11 x S e₁ e₂ ∨ v ∈ Q11 E S e₁ e₂ := by
  rcases C.verts_cases (subset_verts (mem_hit.1 hg).1 hv) with h' | h'
  · exact Or.inl (Finset.mem_union_left _ h')
  · by_cases hT : v ∈ e₁ ∪ e₂
    · exact Or.inl (Finset.mem_union_right _ hT)
    · exact Or.inr (mem_Q.2 ⟨h', hT, Finset.card_pos.2 ⟨g, Finset.mem_filter.2 ⟨hg, hv⟩⟩⟩)

lemma mem_RQ {s : α} (hs : s ∈ S) {g : Finset α} (hg : g ∈ E) (hsg : s ∈ g) {v : α}
    (hv : v ∈ g) : v ∈ R11 x S e₁ e₂ ∨ v ∈ Q11 E S e₁ e₂ :=
  C.mem_RQ' (mem_hit.2 ⟨hg, Finset.not_disjoint_iff.2 ⟨s, hsg, hs⟩⟩) hv

/-- An edge at `s` that contains a vertex of `Q` in at most one place has a vertex of `R` other
than `s`. -/
lemma exists_R {s : α} (hs : s ∈ S) {g : Finset α} (hg : g ∈ E) (hsg : s ∈ g)
    (hc : ((g.erase s) ∩ Q11 E S e₁ e₂).card ≤ 1) : ∃ a ∈ g, a ≠ s ∧ a ∈ R11 x S e₁ e₂ := by
  have h2 : (g.erase s).card = 2 := by rw [Finset.card_erase_of_mem hsg, C.h.L.card3 g hg]
  have := Finset.card_sdiff_add_card_inter (g.erase s) (Q11 E S e₁ e₂)
  obtain ⟨a, ha⟩ : ((g.erase s) \ Q11 E S e₁ e₂).Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨ha1, ha2⟩ := Finset.mem_sdiff.1 ha
  obtain ⟨has, hag⟩ := Finset.mem_erase.1 ha1
  exact ⟨a, hag, has, (C.mem_RQ hs hg hsg hag).resolve_right ha2⟩

/-- The key step of Claim 11.2: if the three edges at `s` are hit by `q ∈ Q`, `r₁ ∈ e₁` and
`r₂ ∈ e₂`, deleting `{q, r₁, r₂} ∪ (S - s)` is a good reduction. -/
lemma key112 {s : α} (hs : s ∈ S) {q r₁ r₂ : α} (hq : q ∈ Q11 E S e₁ e₂) (hr₁ : r₁ ∈ e₁)
    (hr₂ : r₂ ∈ e₂) (hall : ∀ g ∈ E, s ∈ g → q ∈ g ∨ r₁ ∈ g ∨ r₂ ∈ g) : False := by
  have h1 := Finset.card_insert_le q (insert r₁ (insert r₂ (S.erase s)))
  have h2 := Finset.card_insert_le r₁ (insert r₂ (S.erase s))
  have h3 := Finset.card_insert_le r₂ (S.erase s)
  have h4 := Finset.card_erase_of_mem hs
  rw [C.card] at h4
  set X := insert q (insert r₁ (insert r₂ (S.erase s))) with hX
  have hXc : X.card ≤ 5 := by omega
  refine C.red5 hq (Finset.mem_insert_self _ _) ?_ hXc ?_
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_erase] at hv
    rcases hv with rfl | rfl | rfl | ⟨-, hv⟩
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    · exact Finset.mem_union_left _ (mem_R.2 (Or.inr (Or.inr (Finset.mem_union_left _ hr₁))))
    · exact Finset.mem_union_left _ (mem_R.2 (Or.inr (Or.inr (Finset.mem_union_right _ hr₂))))
    · exact Finset.mem_union_left _ (mem_R.2 (Or.inr (Or.inl hv)))
  · intro f hf
    rw [Finset.not_disjoint_iff]
    rcases mem_B.1 hf with hf | rfl | rfl
    · obtain ⟨hfE, hfS⟩ := mem_hit.1 hf
      obtain ⟨y, hyf, hyS⟩ := Finset.not_disjoint_iff.1 hfS
      by_cases hys : y = s
      · subst hys
        rcases hall f hfE hyf with h' | h' | h'
        · exact ⟨q, h', by simp⟩
        · exact ⟨r₁, h', by simp⟩
        · exact ⟨r₂, h', by simp⟩
      · exact ⟨y, hyf, by simp [hys, hyS]⟩
    · exact ⟨r₁, hr₁, by simp⟩
    · exact ⟨r₂, hr₂, by simp⟩

/-- **Claim 11.2**: if `s ∈ S` has a neighbour in `Q`, then `|N(s) ∩ T| ≤ 3`. -/
lemma claim112 {s q : α} (hs : s ∈ S) (hq : q ∈ Q11 E S e₁ e₂) (hqs : q ∈ nbr E {s}) :
    (nbr E {s} ∩ (e₁ ∪ e₂)).card ≤ 3 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨hqs', fq, hfq, hsfq, hqfq⟩ := mem_nbr_singleton.1 hqs
  obtain ⟨f₂, f₃, hf2, hf3, hs2, hs3, -, -, -, hall⟩ := edges_three (C.deg_s hs) hfq hsfq
  have hqT := (mem_Q.1 hq).2.1
  have hsub : nbr E {s} ∩ (e₁ ∪ e₂) ⊆ (fq \ {s, q}) ∪ ((f₂ ∩ e₁) ∪ (f₂ ∩ e₂)) ∪
      ((f₃ ∩ e₁) ∪ (f₃ ∩ e₂)) := by
    intro c hc
    obtain ⟨hcn, hcT⟩ := Finset.mem_inter.1 hc
    obtain ⟨hcs, g, hg, hsg, hcg⟩ := mem_nbr_singleton.1 hcn
    have hcT' := Finset.mem_union.1 hcT
    rcases hall g hg hsg with rfl | rfl | rfl
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hcg, ?_⟩))
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hcs, fun h' => hqT (h' ▸ hcT)⟩
    · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      rcases hcT' with h' | h'
      · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hcg, h'⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hcg, h'⟩)
    · refine Finset.mem_union_right _ ?_
      rcases hcT' with h' | h'
      · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hcg, h'⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hcg, h'⟩)
  have hfq1 : (fq \ {s, q}).card = 1 := by
    have hsq : ({s, q} : Finset α) ⊆ fq := by
      intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> assumption
    rw [Finset.card_sdiff_of_subset hsq, C.h.L.card3 fq hfq, Finset.card_pair (Ne.symm hqs')]
  have hc := Finset.card_le_card hsub
  have u1 := Finset.card_union_le (fq \ {s, q} ∪ ((f₂ ∩ e₁) ∪ (f₂ ∩ e₂))) ((f₃ ∩ e₁) ∪ (f₃ ∩ e₂))
  have u2 := Finset.card_union_le (fq \ {s, q}) ((f₂ ∩ e₁) ∪ (f₂ ∩ e₂))
  have u3 := Finset.card_union_le (f₂ ∩ e₁) (f₂ ∩ e₂)
  have u4 := Finset.card_union_le (f₃ ∩ e₁) (f₃ ∩ e₂)
  obtain ⟨b21, b22⟩ := C.inter_e_le hs hf2 hs2
  obtain ⟨b31, b32⟩ := C.inter_e_le hs hf3 hs3
  have hall' : ∀ g ∈ E, s ∈ g → q ∈ g ∨ g = f₂ ∨ g = f₃ := fun g hg hsg => by
    rcases hall g hg hsg with rfl | h' | h'
    · exact Or.inl hqfq
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')
  by_cases hA : (f₂ ∩ e₁).Nonempty ∧ (f₃ ∩ e₂).Nonempty
  · obtain ⟨⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩⟩ := hA
    rw [Finset.mem_inter] at hr₁ hr₂
    refine C.key112 hs hq hr₁.2 hr₂.2 fun g hg hsg => ?_
    rcases hall' g hg hsg with h' | rfl | rfl
    · exact Or.inl h'
    · exact Or.inr (Or.inl hr₁.1)
    · exact Or.inr (Or.inr hr₂.1)
  · by_cases hB : (f₃ ∩ e₁).Nonempty ∧ (f₂ ∩ e₂).Nonempty
    · obtain ⟨⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩⟩ := hB
      rw [Finset.mem_inter] at hr₁ hr₂
      refine C.key112 hs hq hr₁.2 hr₂.2 fun g hg hsg => ?_
      rcases hall' g hg hsg with h' | rfl | rfl
      · exact Or.inl h'
      · exact Or.inr (Or.inr hr₂.1)
      · exact Or.inr (Or.inl hr₁.1)
    · simp only [← Finset.card_pos, not_and_or, not_lt, Nat.le_zero] at hA hB
      omega

/-- Each vertex of `T` is adjacent to two vertices of `S`. -/
lemma two_le_filter {t : α} (ht : t ∈ e₁ ∪ e₂) :
    2 ≤ (S.filter (fun s => t ∈ nbr E {s})).card := by
  have h2 := C.deg_hit_T ht
  unfold deg at h2
  obtain ⟨g₁, g₂, hne, heq⟩ := Finset.card_eq_two.1 h2
  have hg₁ : g₁ ∈ (hit E S).filter (t ∈ ·) := by rw [heq]; simp
  have hg₂ : g₂ ∈ (hit E S).filter (t ∈ ·) := by rw [heq]; simp
  rw [Finset.mem_filter] at hg₁ hg₂
  obtain ⟨y₁, hy₁g, hy₁S⟩ := Finset.not_disjoint_iff.1 (mem_hit.1 hg₁.1).2
  obtain ⟨y₂, hy₂g, hy₂S⟩ := Finset.not_disjoint_iff.1 (mem_hit.1 hg₂.1).2
  have hty : ∀ {y}, y ∈ S → t ≠ y := fun hy h' => C.s_not_T hy (h' ▸ ht)
  have hy12 : y₁ ≠ y₂ := by
    rintro rfl
    exact hne (C.h.L.eq_of_two (mem_hit.1 hg₁.1).1 (mem_hit.1 hg₂.1).1 (hty hy₁S) hg₁.2 hy₁g
      hg₂.2 hy₂g)
  have hsub : ({y₁, y₂} : Finset α) ⊆ S.filter (fun s => t ∈ nbr E {s}) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_filter.2 ⟨hy₁S, MinCex.mem_nbr_of (mem_hit.1 hg₁.1).1 hy₁g hg₁.2 (hty hy₁S)⟩
    · exact Finset.mem_filter.2 ⟨hy₂S, MinCex.mem_nbr_of (mem_hit.1 hg₂.1).1 hy₂g hg₂.2 (hty hy₂S)⟩
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair hy12] at this

/-- **Claim 11.3** (first half): two vertices of `S` cannot both have neighbours in `Q`. -/
lemma claim113 {s s' q q' : α} (hs : s ∈ S) (hs' : s' ∈ S) (hne : s ≠ s')
    (hq : q ∈ Q11 E S e₁ e₂) (hq' : q' ∈ Q11 E S e₁ e₂) (hqs : q ∈ nbr E {s})
    (hq's : q' ∈ nbr E {s'}) : False := by
  obtain ⟨s'', hs''⟩ : (S \ {s, s'}).Nonempty := by
    apply Finset.card_pos.1
    have := Finset.card_le_card_sdiff_add_card (s := S) (t := {s, s'})
    rw [C.card, Finset.card_pair hne] at this
    omega
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hs''
  obtain ⟨hs''S, h1, h2⟩ := hs''
  have hSeq : S = {s, s', s''} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    · rw [C.card, Finset.card_insert_of_notMem (by simp [hne, Ne.symm h1]),
        Finset.card_pair (Ne.symm h2)]
  have hsum := two_card_le_sum (fun s => nbr E {s}) (fun t ht => C.two_le_filter ht)
  rw [C.card_T, hSeq, Finset.sum_insert (by simp [hne, Ne.symm h1]),
    Finset.sum_pair (Ne.symm h2)] at hsum
  have ha := C.claim112 hs hq hqs
  have hb := C.claim112 hs' hq' hq's
  -- `N(s'')` contains six vertices of `T` and also `x`
  have hx : x ∈ nbr E {s''} := by
    obtain ⟨hxs, f, hf, hxf, hsf⟩ := mem_nbr_singleton.1 (C.hS hs''S)
    exact MinCex.mem_nbr_of hf hsf hxf (Ne.symm hxs)
  have hsub : insert x (nbr E {s''} ∩ (e₁ ∪ e₂)) ⊆ nbr E {s''} :=
    Finset.insert_subset hx Finset.inter_subset_left
  have hxT : x ∉ nbr E {s''} ∩ (e₁ ∪ e₂) := fun h' =>
    C.x_gone (C.T_verts (Finset.mem_inter.1 h').2)
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxT] at this
  have := card_nbr_singleton_le C.h.L.card3 s''
  rw [C.deg_s hs''S] at this
  omega

/-- The final step of Claim 11 (`s` is the only vertex of `S` with neighbours in `Q`). -/
lemma final_core {s : α} (hs : s ∈ S)
    (huniq : ∀ s' ∈ S, s' ≠ s → ∀ q' ∈ Q11 E S e₁ e₂, q' ∉ nbr E {s'})
    {A B D : Finset α} (hA : A ∈ E) (hB : B ∈ E) (hsA : s ∈ A) (hsB : s ∈ B) (hAB : A ≠ B)
    (hall : ∀ g ∈ E, s ∈ g → g = A ∨ g = B ∨ g = D)
    {a₁ a₂ q : α} (ha₁ : a₁ ∈ A) (ha₁s : a₁ ≠ s) (ha₁R : a₁ ∈ R11 x S e₁ e₂)
    (ha₂ : a₂ ∈ B) (ha₂s : a₂ ≠ s) (ha₂R : a₂ ∈ R11 x S e₁ e₂)
    (hqD : q ∈ D) (hq : q ∈ Q11 E S e₁ e₂) : False := by
  have hL := C.h.L
  have ha₁₂ : a₁ ≠ a₂ := by
    rintro rfl
    exact hAB (hL.eq_of_two hA hB ha₁s ha₁ hsA ha₂ hsB)
  have hsR : s ∈ R11 x S e₁ e₂ := mem_R.2 (Or.inr (Or.inl hs))
  set Rs := E.filter (fun f => f ⊆ R11 x S e₁ e₂ ∧ s ∉ f ∧ a₁ ∉ f ∧ a₂ ∉ f) with hRs
  have hRsE : Rs ⊂ E := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, fun h' => ?_⟩
    have : A ∈ Rs := h' ▸ hA
    exact (Finset.mem_filter.1 this).2.2.1 hsA
  -- `R*` has at most 7 vertices and 5 edges
  have hV : verts Rs ⊆ (((R11 x S e₁ e₂).erase s).erase a₁).erase a₂ := by
    intro v hv
    obtain ⟨f, hf, hvf⟩ := mem_verts.1 hv
    obtain ⟨-, hfR, hsf, ha₁f, ha₂f⟩ := Finset.mem_filter.1 hf
    refine Finset.mem_erase.2 ⟨fun h' => ha₂f (h' ▸ hvf), Finset.mem_erase.2
      ⟨fun h' => ha₁f (h' ▸ hvf), Finset.mem_erase.2 ⟨fun h' => hsf (h' ▸ hvf), hfR hvf⟩⟩⟩
  have hVc : (verts Rs).card ≤ 7 := by
    have := Finset.card_le_card hV
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm ha₁₂, Finset.mem_erase.2 ⟨ha₂s, ha₂R⟩⟩),
      Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨ha₁s, ha₁R⟩), Finset.card_erase_of_mem hsR,
      C.card_R] at this
    omega
  set Fs := E.filter (s ∈ ·)
  set F₁ := E.filter (a₁ ∈ ·)
  set F₂ := E.filter (a₂ ∈ ·)
  have hFs : Fs.card = 3 := C.reg s (C.R_verts hsR)
  have hF₁ : F₁.card = 3 := C.reg a₁ (C.R_verts ha₁R)
  have hF₂ : F₂.card = 3 := C.reg a₂ (C.R_verts ha₂R)
  have hi1 : (Fs ∩ F₁).card ≤ 1 := by
    refine (Finset.card_le_card fun f hf => ?_).trans (card_le_one_two hL (Ne.symm ha₁s))
    simp only [Fs, F₁, Finset.mem_inter, Finset.mem_filter] at hf ⊢
    exact ⟨hf.1.1, hf.1.2, hf.2.2⟩
  have hi2 : ((Fs ∪ F₁) ∩ F₂).card ≤ 2 := by
    have hsub : (Fs ∪ F₁) ∩ F₂ ⊆ E.filter (fun f => s ∈ f ∧ a₂ ∈ f) ∪
        E.filter (fun f => a₁ ∈ f ∧ a₂ ∈ f) := by
      intro f hf
      simp only [Fs, F₁, F₂, Finset.mem_inter, Finset.mem_union, Finset.mem_filter] at hf ⊢
      rcases hf.1 with h' | h'
      · exact Or.inl ⟨h'.1, h'.2, hf.2.2⟩
      · exact Or.inr ⟨h'.1, h'.2, hf.2.2⟩
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (by have := card_le_one_two hL (Ne.symm ha₂s); have := card_le_one_two hL ha₁₂; omega))
  have hU6 : 6 ≤ (Fs ∪ F₁ ∪ F₂).card := by
    have e1 := Finset.card_union_add_card_inter Fs F₁
    have e2 := Finset.card_union_add_card_inter (Fs ∪ F₁) F₂
    omega
  have hUB : Fs ∪ F₁ ∪ F₂ ⊆ B11 E S e₁ e₂ := by
    intro f hf
    simp only [Fs, F₁, F₂, Finset.mem_union, Finset.mem_filter] at hf
    rcases hf with (h' | h') | h'
    · exact C.edges_R hsR h'.1 h'.2
    · exact C.edges_R ha₁R h'.1 h'.2
    · exact C.edges_R ha₂R h'.1 h'.2
  have hRsB : Rs ⊆ B11 E S e₁ e₂ \ (Fs ∪ F₁ ∪ F₂) := by
    intro f hf
    obtain ⟨hfE, hfR, hsf, ha₁f, ha₂f⟩ := Finset.mem_filter.1 hf
    obtain ⟨v, hv⟩ : f.Nonempty := Finset.card_pos.1 (by rw [hL.card3 f hfE]; omega)
    refine Finset.mem_sdiff.2 ⟨C.edges_R (hfR hv) hfE hv, ?_⟩
    simp only [Fs, F₁, F₂, Finset.mem_union, Finset.mem_filter]
    tauto
  have hEc : Rs.card ≤ 5 := by
    have := Finset.card_le_card hRsB
    rw [Finset.card_sdiff_of_subset hUB, C.card_B] at this
    omega
  have hh : 3 * hE Rs ≤ (verts Rs).card := mul_hE_le _ 3 fun f hf => by
    rw [Finset.inter_eq_left.2 (subset_verts (isoEdges_subset _ hf)),
      hL.card3 f (Finset.filter_subset _ _ (isoEdges_subset _ hf))]
  obtain ⟨Tr, hTr, hTrw⟩ := (C.h.ih Rs (MinCex.sz_lt_of_ssubset hRsE) (hL.mono hRsE.subset)
    (C.h.F7.mono hRsE.subset)).1
  have hTr2 : (Tr ∩ verts Rs).card ≤ 2 := by
    have := Finset.card_le_card (Finset.inter_subset_left (s₁ := Tr) (s₂ := verts Rs))
    unfold wt at hTrw
    omega
  have h1 := Finset.card_insert_le a₁ (insert a₂ (insert q (Tr ∩ verts Rs)))
  have h2 := Finset.card_insert_le a₂ (insert q (Tr ∩ verts Rs))
  have h3 := Finset.card_insert_le q (Tr ∩ verts Rs)
  set X := insert a₁ (insert a₂ (insert q (Tr ∩ verts Rs))) with hX
  have hXc : X.card ≤ 5 := by omega
  refine C.red5 hq (by simp [hX]) ?_ hXc ?_
  · intro v hv
    simp only [hX, Finset.mem_insert] at hv
    rcases hv with rfl | rfl | rfl | hv
    · exact Finset.mem_union_left _ ha₁R
    · exact Finset.mem_union_left _ ha₂R
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    · have := hV (Finset.mem_inter.1 hv).2
      exact Finset.mem_union_left _ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
        (Finset.mem_of_mem_erase this)))
  · intro f hf
    rw [Finset.not_disjoint_iff]
    have hfE := C.B_sub hf
    by_cases hsf : s ∈ f
    · rcases hall f hfE hsf with rfl | rfl | rfl
      · exact ⟨a₁, ha₁, by simp [hX]⟩
      · exact ⟨a₂, ha₂, by simp [hX]⟩
      · exact ⟨q, hqD, by simp [hX]⟩
    by_cases ha₁f : a₁ ∈ f
    · exact ⟨a₁, ha₁f, by simp [hX]⟩
    by_cases ha₂f : a₂ ∈ f
    · exact ⟨a₂, ha₂f, by simp [hX]⟩
    -- `f` lies inside `R`, so it is an edge of `R*`
    have hfR : f ⊆ R11 x S e₁ e₂ := by
      intro v hv
      rcases mem_B.1 hf with hfS | rfl | rfl
      · rcases C.mem_RQ' hfS hv with h' | h'
        · exact h'
        · exfalso
          obtain ⟨y, hyf, hyS⟩ := Finset.not_disjoint_iff.1 (mem_hit.1 hfS).2
          have hys : y ≠ s := fun h' => hsf (h' ▸ hyf)
          have hvy : v ≠ y := fun h'' => C.S_gone hyS (h'' ▸ (mem_Q.1 h').1)
          exact huniq y hyS hys v h' (MinCex.mem_nbr_of hfE hyf hv hvy)
      · exact mem_R.2 (Or.inr (Or.inr (Finset.mem_union_left _ hv)))
      · exact mem_R.2 (Or.inr (Or.inr (Finset.mem_union_right _ hv)))
    have hfRs : f ∈ Rs := Finset.mem_filter.2 ⟨hfE, hfR, hsf, ha₁f, ha₂f⟩
    obtain ⟨y, hy⟩ := hTr.inter_verts f hfRs
    obtain ⟨hyf, hyT⟩ := Finset.mem_inter.1 hy
    exact ⟨y, hyf, by simp [hX, hyT]⟩

end C11

end OpenProblemsLab.HY
