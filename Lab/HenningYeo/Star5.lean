import Lab.HenningYeo.Star4

/-!
# Henning–Yeo Claim 7.6 and the end of Claim 7
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-- An `F₇` in `H' = Hf + S₀` (with `Hf` `F₇`-free, and each vertex of `S₀` in at most one edge
of `Hf`) has `S₀` as a line avoiding its centre, and each vertex of `S₀` lies on a line of `Hf`
through the centre. -/
lemma F7_centre {Hf : Finset (Finset α)} {S₀ : Finset α} (hF : F7Free Hf)
    (huniq : ∀ s ∈ S₀, ∀ e ∈ Hf, ∀ e' ∈ Hf, s ∈ e → s ∈ e' → e = e')
    (hnot : ¬ F7Free (insert S₀ Hf)) :
    ∃ g : Fin 7 → α, Function.Injective g ∧ (∀ k, ln g k ∈ insert S₀ Hf) ∧ g 0 ∉ S₀ ∧
      ∀ s ∈ S₀, ∃ k, ln g k ∈ Hf ∧ s ∈ ln g k ∧ g 0 ∈ ln g k := by
  rw [F7Free_iff] at hnot
  push Not at hnot
  obtain ⟨g, hg, hall⟩ := hnot
  have hall' : ∀ k, ln g k ∈ insert S₀ Hf := hall
  obtain ⟨l, hl⟩ : ∃ l, ln g l = S₀ := by
    by_contra hno
    push Not at hno
    exact (F7Free_iff.1 hF) g hg fun k => (Finset.mem_insert.1 (hall' k)).resolve_left (hno k)
  have hHf : ∀ k, k ≠ l → ln g k ∈ Hf := fun k hk =>
    (Finset.mem_insert.1 (hall' k)).resolve_left fun h' => hk ((ln_inj hg).1 (h'.trans hl.symm))
  have h0 : ∀ k : Fin 5, k = 0 ∨ k = 1 ∨ k = 2 → g 0 ∈ ln g k := fun k hk =>
    (mem_ln hg).2 ((F7_centre_iff k).2 hk)
  have hz : g 0 ∉ S₀ := by
    intro hzS
    have hne : ∀ {a b : Fin 5}, a ≠ b → ln g a ≠ ln g b := fun hab h' => hab ((ln_inj hg).1 h')
    have key : ∀ a b : Fin 5, a ≠ b → (a = 0 ∨ a = 1 ∨ a = 2) → (b = 0 ∨ b = 1 ∨ b = 2) →
        a ≠ l → b ≠ l → False := fun a b hab ha hb hal hbl =>
      hne hab (huniq _ hzS _ (hHf a hal) _ (hHf b hbl) (h0 a ha) (h0 b hb))
    by_cases h0l : (0 : Fin 5) = l
    · exact key 1 2 (by decide) (by decide) (by decide) (fun h' => by subst h0l; exact absurd h' (by decide))
        (fun h' => by subst h0l; exact absurd h' (by decide))
    · by_cases h1l : (1 : Fin 5) = l
      · exact key 0 2 (by decide) (by decide) (by decide) h0l
          (fun h' => by subst h1l; exact absurd h' (by decide))
      · exact key 0 1 (by decide) (by decide) (by decide) h0l h1l
  refine ⟨g, hg, hall', hz, fun s hs => ?_⟩
  rw [← hl] at hs
  obtain ⟨i, hil, rfl⟩ := mem_ln_iff.1 hs
  obtain ⟨k, h0k, hik⟩ := F7_centre_line i
  have hkl : k ≠ l := by
    rintro rfl
    exact hz (hl ▸ (mem_ln hg).2 h0k)
  exact ⟨k, hHf k hkl, (mem_ln hg).2 hik, (mem_ln hg).2 h0k⟩

namespace Star2

open OpenProblemsLab.HY.Star

variable {E : Finset (Finset α)} {x : α} {u v : Fin 3 → α} {f : Fin 3 → Finset α}

/-- The set `S`. -/
def SS (x : α) (u v : Fin 3 → α) (f : Fin 3 → Finset α) : Finset α :=
  (f 0 ∪ f 1 ∪ f 2) \ nx x u v

lemma mem_SS {s : α} : s ∈ SS x u v f ↔ (∃ t, s ∈ f t) ∧ s ∉ nx x u v := by
  simp only [SS, Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨(h | h) | h, hn⟩ <;> exact ⟨⟨_, h⟩, hn⟩
  · rintro ⟨⟨t, ht⟩, hn⟩
    refine ⟨?_, hn⟩
    fin_cases t
    · exact Or.inl (Or.inl ht)
    · exact Or.inl (Or.inr ht)
    · exact Or.inr ht

lemma hit_eq (T : Star2 E x u v f) : hit E (nx x u v) = D7 x u v f := by
  ext g
  rw [mem_hit]
  constructor
  · rintro ⟨hg, hgn⟩
    obtain ⟨c, hcg, hcn⟩ := Finset.not_disjoint_iff.1 hgn
    exact mem_D7.2 (T.edges_at hcn hg hcg)
  · intro hg
    refine ⟨?_, T.D7_meet hg⟩
    rcases mem_D7.1 hg with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩
    exacts [T.S.htop, T.S.he m, T.hf m]

lemma card_Hf (T : Star2 E x u v f) (h : MinCex E) : (del E (nx x u v)).card + 7 = E.card := by
  have := card_del_add_hit E (nx x u v)
  rw [T.hit_eq, T.card_D7 h] at this
  exact this

lemma nx_verts (T : Star2 E x u v f) : nx x u v ⊆ verts E := by
  intro c hc
  rcases mem_nx.1 hc with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact subset_verts (T.S.he 0) (x_ed 0)
  · exact T.S.u_verts m
  · exact T.S.v_verts m

lemma SS_verts (T : Star2 E x u v f) : SS x u v f ⊆ verts E := by
  intro s hs
  obtain ⟨⟨t, hst⟩, -⟩ := mem_SS.1 hs
  exact subset_verts (T.hf t) hst

/-- Each vertex of `S` lies in exactly one edge of `H - N[x]`. -/
lemma unique_edge (T : Star2 E x u v f) (h : MinCex E) {s : α} (hs : s ∈ SS x u v f) :
    ∃ e ∈ del E (nx x u v), s ∈ e ∧ ∀ e' ∈ del E (nx x u v), s ∈ e' → e' = e := by
  obtain ⟨⟨t, hst⟩, hsn⟩ := mem_SS.1 hs
  have hsv : s ≠ v t := fun h' => hsn (h' ▸ v_nx t)
  obtain ⟨e, he, hne, hse, hall⟩ := exists_other_edge (T.hf t) hst (T.deg_S h hst hsv)
  have hed : e ∈ del E (nx x u v) := by
    refine mem_del.2 ⟨he, Finset.disjoint_left.2 fun c hce hcn => ?_⟩
    rcases T.edges_at hcn he hce with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact hsn (top_sub_nx hse)
    · exact hsn (ed_sub_nx m hse)
    · by_cases hmt : m = t
      · subst hmt; exact hne rfl
      · exact Finset.disjoint_left.1 (T.f_disj h hmt) hse hst
  refine ⟨e, hed, hse, fun e' he' hse' => ?_⟩
  rcases hall e' (del_subset _ _ he') hse' with rfl | rfl
  · exact (Finset.disjoint_left.1 (mem_del.1 he').2 (T.vf t) (v_nx t)).elim
  · rfl

/-- No edge of `H - N[x]` has three vertices in `S` (it would be isolated). -/
lemma inter_SS_le (T : Star2 E x u v f) (h : MinCex E) {e : Finset α}
    (he : e ∈ del E (nx x u v)) : (e ∩ SS x u v f).card ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have heE := del_subset _ _ he
  have hsub : e ⊆ SS x u v f := by
    have hc : (e ∩ SS x u v f) = e := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [h.L.card3 e heE]; omega)
    rw [← hc]; exact Finset.inter_subset_right
  have hiso : e ∈ isoEdges (del E (nx x u v)) := by
    refine Finset.mem_filter.2 ⟨he, fun e' he' hne => Finset.disjoint_left.2 fun c hce hce' => ?_⟩
    obtain ⟨g, -, -, hgu⟩ := T.unique_edge h (hsub hce)
    exact hne ((hgu e' he' hce').trans (hgu e he hce).symm)
  have := T.hE_del_nx h
  unfold hE at this
  rw [Finset.card_eq_zero] at this
  rw [this] at hiso
  exact Finset.notMem_empty _ hiso

lemma card_SS (T : Star2 E x u v f) (h : MinCex E) : 6 ≤ (SS x u v f).card := by
  have hpiece : ∀ t, 2 ≤ (f t \ nx x u v).card := fun t => by
    have h1 := Finset.card_sdiff_add_card_inter (f t) (nx x u v)
    have h2 : f t ∩ nx x u v ⊆ {v t} := fun c hc => by
      rw [Finset.mem_inter] at hc
      obtain ⟨m, rfl, hm⟩ := T.f_inter_nx hc.1 hc.2
      rw [Finset.mem_singleton, T.f_inj h hm]
    have h3 := Finset.card_le_card h2
    rw [Finset.card_singleton] at h3
    rw [h.L.card3 _ (T.hf t)] at h1
    omega
  have hd : ∀ {i j : Fin 3}, i ≠ j → Disjoint (f i \ nx x u v) (f j \ nx x u v) := fun hij =>
    Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset (T.f_disj h hij))
  have heq : SS x u v f = (f 0 \ nx x u v) ∪ (f 1 \ nx x u v) ∪ (f 2 \ nx x u v) := by
    unfold SS; rw [Finset.union_sdiff_distrib, Finset.union_sdiff_distrib]
  rw [heq, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint (hd (by decide))]
  · have := hpiece 0; have := hpiece 1; have := hpiece 2; omega
  · exact Finset.disjoint_union_left.2 ⟨hd (by decide), hd (by decide)⟩

/-- **Claim 7.6**: adding a "linear" triple `S₀ ⊆ S` to `H - N[x]` creates an `F₇`. -/
lemma not_free (T : Star2 E x u v f) (h : MinCex E) {S₀ : Finset α} (hS : S₀ ⊆ SS x u v f)
    (hc : S₀.card = 3) (hlin : ∀ e ∈ del E (nx x u v), (e ∩ S₀).card ≤ 1) :
    ¬ F7Free (insert S₀ (del E (nx x u v))) := by
  intro hF
  have S := T.S
  have hS0 : S₀ ∉ (del E (nx x u v)) := fun h' => by
    have := hlin S₀ h'; rw [Finset.inter_self, hc] at this; omega
  have hcard : (insert S₀ (del E (nx x u v))).card + 6 = E.card := by
    rw [Finset.card_insert_of_notMem hS0]; have := T.card_Hf h; omega
  have hverts : verts (insert S₀ (del E (nx x u v))) ⊆ verts E \ nx x u v := by
    rw [verts_insert]
    refine Finset.union_subset (fun c hc => ?_) (fun c hc => ?_)
    · have := hS hc
      exact Finset.mem_sdiff.2 ⟨T.SS_verts this, (mem_SS.1 this).2⟩
    · exact Finset.mem_sdiff.2 ⟨verts_mono (del_subset _ _) hc,
        Finset.disjoint_left.1 (verts_del_disjoint E _) hc⟩
  have hvc := Finset.card_le_card hverts
  rw [Finset.card_sdiff_of_subset T.nx_verts, S.card_nx] at hvc
  have hV7 : 7 ≤ (verts E).card := S.card_nx ▸ Finset.card_le_card T.nx_verts
  have h0 : hE (insert S₀ (del E (nx x u v))) = 0 := by
    rw [hE, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro e he
    have heI := Finset.mem_filter.1 he
    rcases Finset.mem_insert.1 heI.1 with rfl | heH
    · obtain ⟨s, hs⟩ : e.Nonempty := by rw [← Finset.card_pos, hc]; norm_num
      obtain ⟨g, hg, hsg, -⟩ := T.unique_edge h (hS hs)
      have hne : g ≠ e := fun h' => hS0 (h' ▸ hg)
      exact Finset.disjoint_left.1 (heI.2 g (Finset.mem_insert_of_mem hg) hne) hs hsg
    · have hiso : e ∈ isoEdges (del E (nx x u v)) :=
        Finset.mem_filter.2 ⟨heH, fun e' he' hne => heI.2 e' (Finset.mem_insert_of_mem he') hne⟩
      have := T.hE_del_nx h
      rw [hE, Finset.card_eq_zero] at this
      rw [this] at hiso
      exact Finset.notMem_empty _ hiso
  refine h.no_plus 3 ?_ ((h.L.mono (del_subset _ _)).insert hc hlin) hF ?_ ?_
  · unfold sz; omega
  · intro T' hT'
    obtain ⟨s, hs⟩ := hT' S₀ (Finset.mem_insert_self _ _)
    rw [Finset.mem_inter] at hs
    obtain ⟨⟨t, hst⟩, -⟩ := mem_SS.1 (hS hs.1)
    obtain ⟨i, j, hti, htj, hij⟩ := exists_others t
    refine ⟨T' ∪ {v i, v j, u t}, ?_, fun e he => ?_⟩
    · have := Finset.card_union_le T' {v i, v j, u t}
      have : ({v i, v j, u t} : Finset α).card ≤ 3 := Finset.card_le_three
      omega
    by_cases heH : e ∈ (del E (nx x u v))
    · obtain ⟨c, hc'⟩ := hT' e (Finset.mem_insert_of_mem heH)
      rw [Finset.mem_inter] at hc'
      exact ⟨c, Finset.mem_inter.2 ⟨hc'.1, Finset.mem_union_left _ hc'.2⟩⟩
    have heD : e ∈ D7 x u v f := by
      rw [← T.hit_eq, mem_hit]
      exact ⟨he, fun hd => heH (mem_del.2 ⟨he, hd⟩)⟩
    have pick : ∀ c ∈ e, c ∈ ({v i, v j, u t} : Finset α) → (e ∩ (T' ∪ {v i, v j, u t})).Nonempty :=
      fun c hce hcX => ⟨c, Finset.mem_inter.2 ⟨hce, Finset.mem_union_right _ hcX⟩⟩
    rcases mem_D7.1 heD with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact pick _ (mem_top t) (by simp)
    · rcases fin3_cases hti htj hij m with rfl | rfl | rfl
      · exact pick _ (u_ed _) (by simp)
      · exact pick _ (v_ed _) (by simp)
      · exact pick _ (v_ed _) (by simp)
    · rcases fin3_cases hti htj hij m with rfl | rfl | rfl
      · exact ⟨s, Finset.mem_inter.2 ⟨hst, Finset.mem_union_left _ hs.2⟩⟩
      · exact pick _ (T.vf _) (by simp)
      · exact pick _ (T.vf _) (by simp)
  · rw [h.wt_eq]
    unfold wt
    rw [h0]
    omega

/-- Two vertices of `S` lie in the same edge of `H - N[x]` iff they share their edge. -/
lemma huniq_of (T : Star2 E x u v f) (h : MinCex E) {S₀ : Finset α} (hS : S₀ ⊆ SS x u v f) :
    ∀ s ∈ S₀, ∀ e ∈ del E (nx x u v), ∀ e' ∈ del E (nx x u v), s ∈ e → s ∈ e' → e = e' := by
  intro s hs e he e' he' hse hse'
  obtain ⟨g, -, -, hg⟩ := T.unique_edge h (hS hs)
  exact (hg e he hse).trans (hg e' he' hse').symm

/-- The end of **Claim 7**: a `Star2` is impossible. -/
lemma false (T : Star2 E x u v f) (h : MinCex E) : False := by
  have S := T.S
  set Hf := del E (nx x u v) with hHf
  set SS' := SS x u v f with hSS'
  have hue : ∀ s, ∃ e, s ∈ SS' → e ∈ Hf ∧ s ∈ e ∧ ∀ e' ∈ Hf, s ∈ e' → e' = e := fun s => by
    by_cases hs : s ∈ SS'
    · obtain ⟨e, he, hse, hu⟩ := T.unique_edge h hs
      exact ⟨e, fun _ => ⟨he, hse, hu⟩⟩
    · exact ⟨∅, fun h' => absurd h' hs⟩
  choose G hG using hue
  have hGmem : ∀ {s s'}, s ∈ SS' → s' ∈ SS' → s' ∈ G s → G s' = G s := fun hs hs' h' =>
    ((hG _ hs').2.2 _ (hG _ hs).1 h').symm
  have hcard : 6 ≤ SS'.card := T.card_SS h
  have hinter : ∀ s ∈ SS', (SS' ∩ G s).card ≤ 2 := fun s hs => by
    rw [Finset.inter_comm]; exact T.inter_SS_le h (hG s hs).1
  have hFf : F7Free Hf := h.F7.mono (del_subset _ _)
  -- validity of a triple with distinct `G`-values
  have valid : ∀ {a b c : α}, a ∈ SS' → b ∈ SS' → c ∈ SS' → G a ≠ G b → G a ≠ G c → G b ≠ G c →
      ({a, b, c} : Finset α).card = 3 ∧ ∀ e ∈ Hf, (e ∩ {a, b, c}).card ≤ 1 := by
    intro a b c ha hb hc hab hac hbc
    have hne : ∀ {p q : α}, G p ≠ G q → p ≠ q := fun h' hpq => h' (hpq ▸ rfl)
    refine ⟨Finset.card_eq_three.2 ⟨a, b, c, hne hab, hne hac, hne hbc, rfl⟩, fun e he => ?_⟩
    refine Finset.card_le_one.2 fun p hp q hq => ?_
    rw [Finset.mem_inter] at hp hq
    have hmem : ∀ {r}, r ∈ ({a, b, c} : Finset α) → r ∈ SS' := fun hr => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl <;> assumption
    have hGe : G p = G q :=
      ((hG p (hmem hp.2)).2.2 e he hp.1).symm.trans ((hG q (hmem hq.2)).2.2 e he hq.1)
    have hp' := hp.2; have hq' := hq.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp' hq'
    rcases hp' with rfl | rfl | rfl <;> rcases hq' with rfl | rfl | rfl <;> simp_all
  -- choose `s₁, s₂, s₃`
  obtain ⟨s₁, hs₁⟩ : SS'.Nonempty := Finset.card_pos.1 (by omega)
  have hG1 := hG s₁ hs₁
  obtain ⟨s₂, hs₂⟩ : (SS' \ G s₁).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.card_sdiff_add_card_inter SS' (G s₁)
    have := hinter s₁ hs₁
    omega
  rw [Finset.mem_sdiff] at hs₂
  have hG2 := hG s₂ hs₂.1
  obtain ⟨s₃, hs₃⟩ : (SS' \ (G s₁ ∪ G s₂)).Nonempty := by
    rw [← Finset.card_pos]
    have hsd := Finset.card_sdiff_add_card_inter SS' (G s₁ ∪ G s₂)
    have := hinter s₁ hs₁; have := hinter s₂ hs₂.1
    rw [Finset.inter_union_distrib_left] at hsd
    have := Finset.card_union_le (SS' ∩ G s₁) (SS' ∩ G s₂)
    omega
  rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hs₃
  have hG3 := hG s₃ hs₃.1
  have h12 : G s₁ ≠ G s₂ := fun h' => hs₂.2 (h' ▸ hG2.2.1)
  have h13 : G s₁ ≠ G s₃ := fun h' => hs₃.2.1 (h' ▸ hG3.2.1)
  have h23 : G s₂ ≠ G s₃ := fun h' => hs₃.2.2 (h' ▸ hG3.2.1)
  have hsub3 : ∀ {a b c : α}, a ∈ SS' → b ∈ SS' → c ∈ SS' → ({a, b, c} : Finset α) ⊆ SS' :=
    fun ha hb hc r hr => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl <;> assumption
  obtain ⟨hc0, hl0⟩ := valid hs₁ hs₂.1 hs₃.1 h12 h13 h23
  have hS0 := hsub3 hs₁ hs₂.1 hs₃.1
  obtain ⟨g, hg, hgall, hz, hcen⟩ := F7_centre hFf (T.huniq_of h hS0) (T.not_free h hS0 hc0 hl0)
  have hzG : ∀ {s}, s ∈ ({s₁, s₂, s₃} : Finset α) → s ∈ SS' → g 0 ∈ G s := fun hs hsS => by
    obtain ⟨k, hk, hsk, hzk⟩ := hcen _ hs
    rwa [← (hG _ hsS).2.2 _ hk hsk]
  have hz1 := hzG (by simp) hs₁
  have hz2 := hzG (by simp) hs₂.1
  -- the edges of `Hf` at the centre `z = g 0` are the three centre lines
  have hcl : ∀ m : Fin 5, (m = 0 ∨ m = 1 ∨ m = 2) → ln g m ∈ Hf ∧ g 0 ∈ ln g m := fun m hm => by
    have hzm : g 0 ∈ ln g m := (mem_ln hg).2 ((F7_centre_iff m).2 hm)
    refine ⟨(Finset.mem_insert.1 (hgall m)).resolve_left fun h' => hz (h' ▸ hzm), hzm⟩
  have hzedges : ∀ e ∈ Hf, g 0 ∈ e → ∃ m : Fin 5, (m = 0 ∨ m = 1 ∨ m = 2) ∧ e = ln g m := by
    intro e he hze
    have hsub : ({ln g 0, ln g 1, ln g 2} : Finset (Finset α)) ⊆ Hf.filter (g 0 ∈ ·) := by
      intro e' he'
      simp only [Finset.mem_insert, Finset.mem_singleton] at he'
      rcases he' with rfl | rfl | rfl
      · exact Finset.mem_filter.2 (hcl 0 (by decide))
      · exact Finset.mem_filter.2 (hcl 1 (by decide))
      · exact Finset.mem_filter.2 (hcl 2 (by decide))
    have hc3 : ({ln g 0, ln g 1, ln g 2} : Finset (Finset α)).card = 3 :=
      Finset.card_eq_three.2 ⟨_, _, _, fun h' => absurd ((ln_inj hg).1 h') (by decide),
        fun h' => absurd ((ln_inj hg).1 h') (by decide),
        fun h' => absurd ((ln_inj hg).1 h') (by decide), rfl⟩
    have hdeg : deg Hf (g 0) ≤ 3 := (deg_del_le E _ _).trans (h.claim5 _)
    unfold deg at hdeg
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    have : e ∈ Hf.filter (g 0 ∈ ·) := Finset.mem_filter.2 ⟨he, hze⟩
    rw [← heq] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl | rfl
    exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩]
  -- choose `s''`
  obtain ⟨s', hs'⟩ : (SS' \ (insert s₃ (G s₁ ∪ G s₂))).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.card_sdiff_add_card_inter SS' (insert s₃ (G s₁ ∪ G s₂))
    have := hinter s₁ hs₁; have := hinter s₂ hs₂.1
    have h1 : SS' ∩ insert s₃ (G s₁ ∪ G s₂) ⊆ insert s₃ ((SS' ∩ G s₁) ∪ (SS' ∩ G s₂)) := by
      intro r hr
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_union] at hr ⊢
      tauto
    have := Finset.card_le_card h1
    have := Finset.card_insert_le s₃ ((SS' ∩ G s₁) ∪ (SS' ∩ G s₂))
    have := Finset.card_union_le (SS' ∩ G s₁) (SS' ∩ G s₂)
    omega
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union, not_or] at hs'
  obtain ⟨hs'S, hs'3, hs'1, hs'2⟩ := hs'
  have hG' := hG s' hs'S
  have h1' : G s₁ ≠ G s' := fun h' => hs'1 (h' ▸ hG'.2.1)
  have h2' : G s₂ ≠ G s' := fun h' => hs'2 (h' ▸ hG'.2.1)
  have hs'0 : s' ∉ ({s₁, s₂, s₃} : Finset α) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h' => hs'1 (h' ▸ hG1.2.1), fun h' => hs'2 (h' ▸ hG2.2.1), hs'3⟩
  obtain ⟨hc1, hl1⟩ := valid hs₁ hs₂.1 hs'S h12 h1' h2'
  have hS1 := hsub3 hs₁ hs₂.1 hs'S
  obtain ⟨g', hg', -, -, hcen'⟩ := F7_centre hFf (T.huniq_of h hS1) (T.not_free h hS1 hc1 hl1)
  have hzG' : ∀ {s}, s ∈ ({s₁, s₂, s'} : Finset α) → s ∈ SS' → g' 0 ∈ G s := fun hs hsS => by
    obtain ⟨k, hk, hsk, hzk⟩ := hcen' _ hs
    rwa [← (hG _ hsS).2.2 _ hk hsk]
  have hzz : g' 0 = g 0 := by
    have hlin := h.L.linear _ (del_subset _ _ hG1.1) _ (del_subset _ _ hG2.1) h12
    exact Finset.card_le_one.1 hlin _ (Finset.mem_inter.2 ⟨hzG' (by simp) hs₁, hzG' (by simp) hs₂.1⟩)
      _ (Finset.mem_inter.2 ⟨hz1, hz2⟩)
  have hzs' : g 0 ∈ G s' := hzz ▸ hzG' (by simp) hs'S
  obtain ⟨m, -, hm⟩ := hzedges _ hG'.1 hzs'
  have hs'm : s' ∈ ln g m := hm ▸ hG'.2.1
  obtain ⟨i, him, rfl⟩ := mem_ln_iff.1 hs'm
  obtain ⟨k, hkm, hik⟩ := F7L_two m i him
  have hlk := hgall k
  have hik' : g i ∈ ln g k := (mem_ln hg).2 hik
  have hkHf : ln g k ∈ Hf := (Finset.mem_insert.1 hlk).resolve_left fun h' => hs'0 (h' ▸ hik')
  exact hkm ((ln_inj hg).1 (((hG'.2.2 _ hkHf hik').trans hm)))

end Star2

namespace Star

/-- **Claim 7**: if `{u₀, u₁, u₂} ⊆ N(x)` is an edge, all `uᵢ` have degree 3. -/
lemma claim7 {E : Finset (Finset α)} {x : α} {u v : Fin 3 → α} (S : Star E x u v)
    (h : MinCex E) (t : Fin 3) : deg E (u t) = 3 := by
  rcases h.deg_two_or_three (S.u_verts t) with h2 | h3
  · obtain ⟨f, T⟩ := S.exists_star2 h h2
    exact T.false h |>.elim
  · exact h3

end Star

end OpenProblemsLab.HY
