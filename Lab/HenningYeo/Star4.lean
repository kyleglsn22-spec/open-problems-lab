import Lab.HenningYeo.Star3

/-!
# Henning–Yeo Claims 7.4 and 7.5
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

namespace Star2

open OpenProblemsLab.HY.Star

variable {E : Finset (Finset α)} {x : α} {u v : Fin 3 → α} {f : Fin 3 → Finset α}

/-- The seven edges meeting `N[x]`. -/
def D7 (x : α) (u v : Fin 3 → α) (f : Fin 3 → Finset α) : Finset (Finset α) :=
  insert (top u) (Finset.univ.image (ed x u v) ∪ Finset.univ.image f)

lemma mem_D7 {g : Finset α} : g ∈ D7 x u v f ↔ g = top u ∨ (∃ t, g = ed x u v t) ∨ ∃ t, g = f t := by
  simp [D7, eq_comm]

lemma card_D7 (T : Star2 E x u v f) (h : MinCex E) : (D7 x u v f).card = 7 := by
  unfold D7
  rw [Finset.card_insert_of_notMem, Finset.card_union_of_disjoint,
    Finset.card_image_of_injective _ (fun i j h' => by by_contra hij; exact T.S.ed_ne hij h'),
    Finset.card_image_of_injective _ (T.f_inj h)]
  · rfl
  · rw [Finset.disjoint_left]; intro g hg hg'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hg hg'
    obtain ⟨i, rfl⟩ := hg; obtain ⟨j, hj⟩ := hg'
    exact T.f_ne_ed j i hj
  · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, not_or, not_exists]
    exact ⟨fun i h' => T.S.top_ne i h'.symm, fun i h' => T.f_ne_top i h'⟩

lemma D7_meet {g : Finset α} (hg : g ∈ D7 x u v f) (T : Star2 E x u v f) :
    ¬ Disjoint g (nx x u v) := by
  rcases mem_D7.1 hg with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact Finset.not_disjoint_iff.2 ⟨u 0, mem_top 0, u_nx 0⟩
  · exact Finset.not_disjoint_iff.2 ⟨x, x_ed t, x_nx⟩
  · exact Finset.not_disjoint_iff.2 ⟨v t, T.vf t, v_nx t⟩

/-- A vertex outside `N[x]` but adjacent to it lies in some `f t`. -/
lemma mem_f_of_nbr (T : Star2 E x u v f) {a : α} (ha : a ∈ nbr E (nx x u v)) :
    ∃ t, a ∈ f t ∧ a ≠ v t := by
  rw [nbr, Finset.mem_sdiff] at ha
  obtain ⟨g, hg, hag⟩ := mem_verts.1 ha.1
  rw [mem_hit] at hg
  obtain ⟨c, hcg, hcn⟩ := Finset.not_disjoint_iff.1 hg.2
  rcases T.edges_at hcn hg.1 hcg with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact absurd (top_sub_nx hag) ha.2
  · exact absurd (ed_sub_nx t hag) ha.2
  · exact ⟨t, hag, fun h' => ha.2 (h' ▸ v_nx t)⟩

lemma card_f_sdiff (T : Star2 E x u v f) (h : MinCex E) (t : Fin 3) :
    (f t \ nx x u v).card ≤ 2 := by
  have := card_sdiff_le_of_one (T.vf t) (v_nx (x := x) (u := u) t)
  rw [h.L.card3 _ (T.hf t)] at this
  omega

/-- **Claim 7.4**: `H - N[x]` has no isolated edge. -/
lemma hE_del_nx (T : Star2 E x u v f) (h : MinCex E) : hE (del E (nx x u v)) = 0 := by
  have S := T.S
  by_contra h0
  obtain ⟨e, he⟩ : (isoEdges (del E (nx x u v))).Nonempty :=
    Finset.card_pos.1 (Nat.pos_of_ne_zero h0)
  have hed := isoEdges_subset _ he
  have heE := del_subset _ _ hed
  have hen := (mem_del.1 hed).2
  have hesub : ∀ a ∈ e, a ∈ nbr E (nx x u v) := fun a ha => h.iso_sub_nbr he ha
  have hene : ∀ a ∈ e, a ∉ nx x u v := fun a ha hn => Finset.disjoint_left.1 hen ha hn
  -- each vertex of `e` has degree 2, with edges `e` and some `f m`
  have hat : ∀ a ∈ e, ∃ m, a ∈ f m ∧ ∀ g ∈ E, a ∈ g → g = e ∨ g = f m := fun a ha => by
    obtain ⟨m, ham, hav⟩ := T.mem_f_of_nbr (hesub a ha)
    have hne : e ≠ f m := fun h' => Finset.disjoint_left.1 hen (h' ▸ T.vf m) (v_nx m)
    exact ⟨m, ham, eq_or_eq_of_deg_two (T.deg_S h ham hav) heE (T.hf m) hne ha ham⟩
  obtain ⟨s, hs⟩ : e.Nonempty := by
    rw [← Finset.card_pos, h.L.card3 e heE]; norm_num
  obtain ⟨t, hst, -⟩ := hat s hs
  obtain ⟨i, j, hti, htj, hij⟩ := exists_others t
  set X : Finset α := {s, v i, v j, u t} with hX
  have meet : ∀ {g : Finset α} {w : α}, w ∈ g → w ∈ X → ¬ Disjoint g X := fun hw hwX =>
    Finset.not_disjoint_iff.2 ⟨_, hw, hwX⟩
  have hs' : s ∈ X := by simp [hX]
  have hvi : v i ∈ X := by simp [hX]
  have hvj : v j ∈ X := by simp [hX]
  have hut : u t ∈ X := by simp [hX]
  have hDm : ∀ g ∈ insert e (D7 x u v f), ¬ Disjoint g X := by
    intro g hg
    rw [Finset.mem_insert] at hg
    rcases hg with rfl | hg
    · exact meet hs hs'
    rcases mem_D7.1 hg with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact meet (mem_top t) hut
    · rcases fin3_cases hti htj hij m with rfl | rfl | rfl
      · exact meet (u_ed _) hut
      · exact meet (v_ed _) hvi
      · exact meet (v_ed _) hvj
    · rcases fin3_cases hti htj hij m with rfl | rfl | rfl
      · exact meet hst hs'
      · exact meet (T.vf _) hvi
      · exact meet (T.vf _) hvj
  have hRd : Disjoint (nx x u v ∪ e) (verts (del E X)) := by
    refine disjoint_verts_del fun c hc g hg hcg => hDm g ?_
    rcases Finset.mem_union.1 hc with hc | hc
    · exact Finset.mem_insert_of_mem (mem_D7.2 (T.edges_at hc hg hcg))
    · obtain ⟨m, -, hm⟩ := hat c hc
      rcases hm g hg hcg with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (mem_D7.2 (Or.inr (Or.inr ⟨m, rfl⟩)))
  have hk : hE (del E X) ≤ 2 := by
    have h3 := h.three_hE_le (C := (f 0 \ nx x u v) ∪ (f 1 \ nx x u v) ∪ (f 2 \ nx x u v))
      hRd ?_
    · have := Finset.card_union_le ((f 0 \ nx x u v) ∪ (f 1 \ nx x u v)) (f 2 \ nx x u v)
      have := Finset.card_union_le (f 0 \ nx x u v) (f 1 \ nx x u v)
      have := T.card_f_sdiff h 0; have := T.card_f_sdiff h 1; have := T.card_f_sdiff h 2
      omega
    · intro g hg hgX c hcg hcR
      have hcn : c ∉ nx x u v := fun h' => hcR (Finset.mem_union_left _ h')
      have hce : c ∉ e := fun h' => hcR (Finset.mem_union_right _ h')
      obtain ⟨d, hdg, hdX⟩ := Finset.not_disjoint_iff.1 hgX
      have hgD : g ∈ insert e (D7 x u v f) := by
        simp only [hX, Finset.mem_insert, Finset.mem_singleton] at hdX
        rcases hdX with rfl | rfl | rfl | rfl
        · obtain ⟨m, -, hm⟩ := hat d hs
          rcases hm g hg hdg with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (mem_D7.2 (Or.inr (Or.inr ⟨m, rfl⟩)))
        all_goals exact Finset.mem_insert_of_mem (mem_D7.2 (T.edges_at (by
          first | exact v_nx _ | exact u_nx _) hg hdg))
      rw [Finset.mem_insert] at hgD
      rcases hgD with rfl | hgD
      · exact absurd hcg hce
      rcases mem_D7.1 hgD with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact absurd (top_sub_nx hcg) hcn
      · exact absurd (ed_sub_nx m hcg) hcn
      · have : c ∈ f m \ nx x u v := Finset.mem_sdiff.2 ⟨hcg, hcn⟩
        fin_cases m <;> simp_all
  have hdisj : Disjoint (nx x u v) e := Finset.disjoint_left.2 fun c hc hce => hene c hce hc
  have heD : e ∉ D7 x u v f := fun h' => T.D7_meet h' hdisj.symm
  refine h.no_good_del (X := X) (R := nx x u v ∪ e) (D := insert e (D7 x u v f)) 2 ?_ hRd
    (fun g hg => mem_hit.2 ⟨?_, hDm g hg⟩) ⟨e, Finset.mem_insert_self _ _⟩ hk ?_
  · intro c hc
    rcases Finset.mem_union.1 hc with hc | hc
    · rcases mem_nx.1 hc with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact subset_verts (S.he 0) (x_ed 0)
      · exact S.u_verts m
      · exact S.v_verts m
    · exact subset_verts heE hc
  · rw [Finset.mem_insert] at hg
    rcases hg with rfl | hg
    · exact heE
    rcases mem_D7.1 hg with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩
    exacts [S.htop, S.he m, T.hf m]
  · rw [Finset.card_union_of_disjoint hdisj, S.card_nx, h.L.card3 e heE,
      Finset.card_insert_of_notMem heD, T.card_D7 h]
    have : X.card ≤ 4 := Finset.card_le_four
    omega

/-- **Claim 7.5**: the edges `f t` are pairwise disjoint. -/
lemma f_disj (T : Star2 E x u v f) (h : MinCex E) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (f i) (f j) := by
  have S := T.S
  rw [Finset.disjoint_left]
  intro c hci hcj
  have hcv : c ≠ v i := fun h' =>
    hij (T.f_inj h (T.v_mem_f (show v i ∈ f j by rw [← h']; exact hcj))).symm
  have hcvj : c ≠ v j := fun h' =>
    hij (T.f_inj h (T.v_mem_f (show v j ∈ f i by rw [← h']; exact hci)))
  have hcn := T.not_nx_of_f h hci hcv
  have hfij : f i ≠ f j := (T.f_inj h).ne hij
  have hatc := eq_or_eq_of_deg_two (T.deg_S h hci hcv) (T.hf i) (T.hf j) hfij hci hcj
  obtain ⟨k, hki, hkj⟩ : ∃ k, k ≠ i ∧ k ≠ j := exists_third i j
  set X : Finset α := {u k, v i, v j} with hX
  set R : Finset α := insert c {x, u i, u j, u k, v i, v j} with hR
  have meet : ∀ {g : Finset α} {w : α}, w ∈ g → w ∈ X → ¬ Disjoint g X := fun hw hwX =>
    Finset.not_disjoint_iff.2 ⟨_, hw, hwX⟩
  have huk : u k ∈ X := by simp [hX]
  have hvi : v i ∈ X := by simp [hX]
  have hvj : v j ∈ X := by simp [hX]
  have hRd : Disjoint R (verts (del E X)) := by
    refine disjoint_verts_del fun w hw g hg hwg => ?_
    simp only [hR, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rcases hatc g hg hwg with rfl | rfl
      · exact meet (T.vf i) hvi
      · exact meet (T.vf j) hvj
    · obtain ⟨m, rfl⟩ := S.atx g hg hwg
      rcases fin3_cases hki hkj hij m with rfl | rfl | rfl
      · exact meet (u_ed _) huk
      · exact meet (v_ed _) hvi
      · exact meet (v_ed _) hvj
    · rcases S.at_u (T.du i) g hg hwg with rfl | rfl
      · exact meet (mem_top k) huk
      · exact meet (v_ed _) hvi
    · rcases S.at_u (T.du j) g hg hwg with rfl | rfl
      · exact meet (mem_top k) huk
      · exact meet (v_ed _) hvj
    · exact meet hwg huk
    · exact meet hwg hvi
    · exact meet hwg hvj
  have htopR : top u ⊆ R := by
    rw [← top_eq hki hkj hij]
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> simp [hR]
  have hedR : ∀ m, m ≠ k → ed x u v m ⊆ R := fun m hm w hw => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases fin3_cases hki hkj hij m with rfl | rfl | rfl
    · exact absurd rfl hm
    · rcases hw with rfl | rfl | rfl <;> simp [hR]
    · rcases hw with rfl | rfl | rfl <;> simp [hR]
  have hk : hE (del E X) ≤ 1 := by
    have h3 := h.three_hE_le (C := insert (v k) ((f i \ R) ∪ (f j \ R))) hRd ?_
    · have c1 := card_sdiff_le_of_two (R := R) hcv.symm (T.vf i) hci (by simp [hR]) (by simp [hR])
      have c2 := card_sdiff_le_of_two (R := R) hcvj.symm (T.vf j) hcj (by simp [hR]) (by simp [hR])
      rw [h.L.card3 _ (T.hf i)] at c1
      rw [h.L.card3 _ (T.hf j)] at c2
      have := Finset.card_insert_le (v k) ((f i \ R) ∪ (f j \ R))
      have := Finset.card_union_le (f i \ R) (f j \ R)
      omega
    · intro g hg hgX w hwg hwR
      obtain ⟨d, hdg, hdX⟩ := Finset.not_disjoint_iff.1 hgX
      simp only [hX, Finset.mem_insert, Finset.mem_singleton] at hdX
      rcases hdX with rfl | rfl | rfl
      · rcases S.at_u (T.du k) g hg hdg with rfl | rfl
        · exact absurd (htopR hwg) hwR
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hwg
          rcases hwg with rfl | rfl | rfl
          · exact absurd (by simp [hR]) hwR
          · exact absurd (by simp [hR]) hwR
          · exact Finset.mem_insert_self _ _
      · rcases T.at_v i g hg hdg with rfl | rfl
        · exact absurd (hedR i hki.symm hwg) hwR
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hwg, hwR⟩))
      · rcases T.at_v j g hg hdg with rfl | rfl
        · exact absurd (hedR j hkj.symm hwg) hwR
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hwg, hwR⟩))
  have hD := card_six (S.top_ne k) (S.top_ne i) (T.f_ne_top i).symm (S.top_ne j)
    (T.f_ne_top j).symm (S.ed_ne hki) (T.f_ne_ed i k).symm (S.ed_ne hkj) (T.f_ne_ed j k).symm
    (T.f_ne_ed i i).symm (S.ed_ne hij) (T.f_ne_ed j i).symm (T.f_ne_ed i j) hfij
    (T.f_ne_ed j j).symm
  have hR7 : R.card = 7 := by
    rw [hR, Finset.card_insert_of_notMem, card_six (S.hxu i) (S.hxu j) (S.hxu k) (S.hxv i)
      (S.hxv j) (S.hu.ne hij) (S.hu.ne (Ne.symm hki)) (S.huv i i) (S.huv i j)
      (S.hu.ne (Ne.symm hkj)) (S.huv j i) (S.huv j j) (S.huv k i) (S.huv k j) (S.hv.ne hij)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h' => hcn (h' ▸ x_nx), fun h' => hcn (h' ▸ u_nx i), fun h' => hcn (h' ▸ u_nx j),
      fun h' => hcn (h' ▸ u_nx k), fun h' => hcn (h' ▸ v_nx i), fun h' => hcn (h' ▸ v_nx j)⟩
  refine h.no_good_del (X := X) (R := R)
    (D := {top u, ed x u v k, ed x u v i, f i, ed x u v j, f j}) 1 ?_ hRd ?_
    ⟨top u, by simp⟩ hk ?_
  · intro w hw
    simp only [hR, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact subset_verts (T.hf i) hci
    · exact subset_verts (S.he 0) (x_ed 0)
    · exact S.u_verts _
    · exact S.u_verts _
    · exact S.u_verts _
    · exact S.v_verts _
    · exact S.v_verts _
  · intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_hit.2 ⟨S.htop, meet (mem_top k) huk⟩
    · exact mem_hit.2 ⟨S.he k, meet (u_ed k) huk⟩
    · exact mem_hit.2 ⟨S.he i, meet (v_ed i) hvi⟩
    · exact mem_hit.2 ⟨T.hf i, meet (T.vf i) hvi⟩
    · exact mem_hit.2 ⟨S.he j, meet (v_ed j) hvj⟩
    · exact mem_hit.2 ⟨T.hf j, meet (T.vf j) hvj⟩
  · rw [hR7, hD]
    have : X.card ≤ 3 := Finset.card_le_three
    omega

end Star2

end OpenProblemsLab.HY
