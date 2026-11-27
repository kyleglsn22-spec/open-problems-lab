import Lab.AlbertsonBerman.Good3

/-! Part of claim AB-1, see `Lab/AlbertsonBerman/Basic.lean`. -/

namespace OpenProblemsLab.AlbertsonBerman

open SimpleGraph

lemma allGood : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f → goodPair e.1 e.2 f.1 f.2 = true := by
  intro e he
  rw [edges_split, List.mem_append, List.mem_append, List.mem_append] at he
  rcases he with ((he | he) | he) | he
  · exact allGood0 e he
  · exact allGood1 e he
  · exact allGood2 e he
  · exact allGood3 e he

/-- The real point of an integer point. -/
def toR (q : ℤ × ℤ) : ℝ × ℝ := ((q.1 : ℝ), (q.2 : ℝ))

lemma toR_injective : Function.Injective toR := by
  intro a b h
  simp only [toR, Prod.mk.injEq, Int.cast_inj] at h
  exact Prod.ext h.1 h.2

/-- Real orientation. -/
def orR (a b z : ℝ × ℝ) : ℝ := (b.1 - a.1) * (z.2 - a.2) - (b.2 - a.2) * (z.1 - a.1)

lemma orR_toR (a b c : ℤ × ℤ) : orR (toR a) (toR b) (toR c) = (orient a b c : ℝ) := by
  simp only [orR, toR, orient]; push_cast; ring

lemma orR_of_mem_segment_left {a b z : ℝ × ℝ} (hz : z ∈ segment ℝ a b) : orR a b z = 0 := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  simp only [orR, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have : s = 1 - t := by linarith
  subst this; ring

lemma orR_of_mem_segment {a b c d z : ℝ × ℝ} (hz : z ∈ segment ℝ c d) :
    ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t = 1 ∧ orR a b z = s * orR a b c + t * orR a b d := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  refine ⟨s, t, hs, ht, hst, ?_⟩
  simp only [orR, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have : s = 1 - t := by linarith
  subst this; ring

lemma segment_inter_eq_empty {a b c d : ℝ × ℝ} (h : 0 < orR a b c * orR a b d) :
    segment ℝ a b ∩ segment ℝ c d = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hab hcd
  have h0 := orR_of_mem_segment_left hab
  obtain ⟨s, t, hs, ht, hst, he⟩ := orR_of_mem_segment (a := a) (b := b) hcd
  rw [h0] at he
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · have h1 : s * min (orR a b c) (orR a b d) ≤ s * orR a b c :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hs
    have h2 : t * min (orR a b c) (orR a b d) ≤ t * orR a b d :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) ht
    have hm : 0 < min (orR a b c) (orR a b d) := lt_min hc hd
    nlinarith
  · have h1 : s * orR a b c ≤ s * max (orR a b c) (orR a b d) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hs
    have h2 : t * orR a b d ≤ t * max (orR a b c) (orR a b d) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) ht
    have hm : max (orR a b c) (orR a b d) < 0 := max_lt hc hd
    nlinarith

lemma segment_inter_subset {v x y : ℝ × ℝ} (h : orR v x y ≠ 0) :
    segment ℝ v x ∩ segment ℝ v y ⊆ {v} := by
  rintro z ⟨⟨s, t, hs, ht, hst, rfl⟩, ⟨s', t', hs', ht', hst', hz⟩⟩
  have e1 := congrArg Prod.fst hz
  have e2 := congrArg Prod.snd hz
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2
  have hs1 : s = 1 - t := by linarith
  have hs2 : s' = 1 - t' := by linarith
  subst hs1 hs2
  have key : t' * orR v x y = 0 := by
    simp only [orR]
    linear_combination (x.1 - v.1) * e2 - (x.2 - v.2) * e1
  have ht0 : t' = 0 := by
    rcases mul_eq_zero.1 key with h' | h'
    · exact h'
    · exact absurd h' h
  subst ht0
  rw [Set.mem_singleton_iff, ← hz]
  simp

/-- The drawing map. -/
def pt (i : Fin 29) : ℝ × ℝ := toR (P i)

lemma orient_cast_ne {a b c : Fin 29} (h : orient (P a) (P b) (P c) ≠ 0) :
    orR (pt a) (pt b) (pt c) ≠ 0 := by
  simp only [pt, orR_toR]; exact_mod_cast h

lemma orient_cast_pos {a b c d : Fin 29}
    (h : 0 < orient (P a) (P b) (P c) * orient (P a) (P b) (P d)) :
    0 < orR (pt a) (pt b) (pt c) * orR (pt a) (pt b) (pt d) := by
  simp only [pt, orR_toR]; exact_mod_cast h

lemma good_segments (a b c d : Fin 29) (h : goodPair a b c d = true) :
    segment ℝ (pt a) (pt b) ∩ segment ℝ (pt c) (pt d) ⊆ pt '' ({a, b} ∩ {c, d} : Set (Fin 29)) := by
  unfold goodPair at h
  split_ifs at h with h1 h2 h3 h4
  · subst h1
    have := segment_inter_subset (orient_cast_ne (of_decide_eq_true h))
    intro z hz
    rw [Set.mem_singleton_iff.1 (this hz)]
    exact ⟨a, by simp, rfl⟩
  · subst h2
    have := segment_inter_subset (orient_cast_ne (of_decide_eq_true h))
    intro z hz
    rw [segment_symm ℝ (pt c)] at hz
    rw [Set.mem_singleton_iff.1 (this hz)]
    exact ⟨a, by simp, rfl⟩
  · subst h3
    have := segment_inter_subset (orient_cast_ne (of_decide_eq_true h))
    intro z hz
    rw [segment_symm ℝ (pt a)] at hz
    rw [Set.mem_singleton_iff.1 (this hz)]
    exact ⟨b, by simp, rfl⟩
  · subst h4
    have := segment_inter_subset (orient_cast_ne (of_decide_eq_true h))
    intro z hz
    rw [segment_symm ℝ (pt a), segment_symm ℝ (pt c)] at hz
    rw [Set.mem_singleton_iff.1 (this hz)]
    exact ⟨b, by simp, rfl⟩
  · rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    rcases h with h | h
    · rw [segment_inter_eq_empty (orient_cast_pos h)]; exact Set.empty_subset _
    · rw [Set.inter_comm, segment_inter_eq_empty (orient_cast_pos h)]; exact Set.empty_subset _

/-- `G₂₉` has a straight-line planar drawing. -/
theorem straightLinePlanar_G : StraightLinePlanar G := by
  refine ⟨pt, fun i j h => P_inj i j (toR_injective h), ?_⟩
  intro a b c d hab hcd hne
  rw [adj_iff] at hab hcd
  have key : ∀ a b c d : Fin 29, (a, b) ∈ edges → (c, d) ∈ edges → s(a, b) ≠ s(c, d) →
      segment ℝ (pt a) (pt b) ∩ segment ℝ (pt c) (pt d) ⊆
        pt '' ({a, b} ∩ {c, d} : Set (Fin 29)) := by
    intro a b c d h1 h2 hne
    refine good_segments a b c d (allGood _ h1 _ h2 ?_)
    rintro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hne rfl
  rcases hab with hab | hab <;> rcases hcd with hcd | hcd
  · exact key a b c d hab hcd hne
  · rw [segment_symm ℝ (pt c), Set.pair_comm c d]
    exact key a b d c hab hcd (by rwa [Sym2.eq_swap (a := d)])
  · rw [segment_symm ℝ (pt a), Set.pair_comm a b]
    exact key b a c d hab hcd (by rwa [Sym2.eq_swap (a := b)])
  · rw [segment_symm ℝ (pt a), Set.pair_comm a b, segment_symm ℝ (pt c), Set.pair_comm c d]
    exact key b a d c hab hcd (by rwa [Sym2.eq_swap (a := b), Sym2.eq_swap (a := d)])

end OpenProblemsLab.AlbertsonBerman
