import Lab.TotalDomination.Good5

/-! Part of claim GHT-1, see `Lab/TotalDomination/Basic.lean`. The straight-line drawing of `B`,
following `Lab/AlbertsonBerman/Drawing.lean`. -/

namespace OpenProblemsLab.TotalDomination

open SimpleGraph AlbertsonBerman

lemma allGood : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f → goodPair e.1 e.2 f.1 f.2 = true := by
  intro e he
  rw [edges_split] at he
  simp only [List.mem_append] at he
  rcases he with ((((he | he) | he) | he) | he) | he
  · exact allGood0 e he
  · exact allGood1 e he
  · exact allGood2 e he
  · exact allGood3 e he
  · exact allGood4 e he
  · exact allGood5 e he

/-- The drawing map. -/
def pt (i : Fin 36) : ℝ × ℝ := toR (P i.val)

lemma orient_cast_ne {a b c : Fin 36} (h : orient (P a.val) (P b.val) (P c.val) ≠ 0) :
    orR (pt a) (pt b) (pt c) ≠ 0 := by
  simp only [pt, orR_toR]; exact_mod_cast h

lemma orient_cast_pos {a b c d : Fin 36}
    (h : 0 < orient (P a.val) (P b.val) (P c.val) * orient (P a.val) (P b.val) (P d.val)) :
    0 < orR (pt a) (pt b) (pt c) * orR (pt a) (pt b) (pt d) := by
  simp only [pt, orR_toR]; exact_mod_cast h

lemma good_segments (a b c d : Fin 36) (h : goodPair a.val b.val c.val d.val = true) :
    segment ℝ (pt a) (pt b) ∩ segment ℝ (pt c) (pt d) ⊆ pt '' ({a, b} ∩ {c, d} : Set (Fin 36)) := by
  unfold goodPair at h
  split_ifs at h with h1 h2 h3 h4
  · obtain rfl : a = c := Fin.ext h1
    have := segment_inter_subset (orient_cast_ne (of_decide_eq_true h))
    intro z hz
    rw [Set.mem_singleton_iff.1 (this hz)]
    exact ⟨a, by simp, rfl⟩
  · obtain rfl : a = d := Fin.ext h2
    have := segment_inter_subset (orient_cast_ne (of_decide_eq_true h))
    intro z hz
    rw [segment_symm ℝ (pt c)] at hz
    rw [Set.mem_singleton_iff.1 (this hz)]
    exact ⟨a, by simp, rfl⟩
  · obtain rfl : b = c := Fin.ext h3
    have := segment_inter_subset (orient_cast_ne (of_decide_eq_true h))
    intro z hz
    rw [segment_symm ℝ (pt a)] at hz
    rw [Set.mem_singleton_iff.1 (this hz)]
    exact ⟨b, by simp, rfl⟩
  · obtain rfl : b = d := Fin.ext h4
    have := segment_inter_subset (orient_cast_ne (of_decide_eq_true h))
    intro z hz
    rw [segment_symm ℝ (pt a), segment_symm ℝ (pt c)] at hz
    rw [Set.mem_singleton_iff.1 (this hz)]
    exact ⟨b, by simp, rfl⟩
  · rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    rcases h with h | h
    · rw [segment_inter_eq_empty (orient_cast_pos h)]; exact Set.empty_subset _
    · rw [Set.inter_comm, segment_inter_eq_empty (orient_cast_pos h)]; exact Set.empty_subset _

/-- `B` has a straight-line planar drawing. -/
theorem straightLinePlanar_B : StraightLinePlanar B := by
  refine ⟨pt, fun i j h => P_inj i j (toR_injective h), ?_⟩
  intro a b c d hab hcd hne
  rw [adj_iff] at hab hcd
  have key : ∀ a b c d : Fin 36, (a.val, b.val) ∈ edges → (c.val, d.val) ∈ edges →
      s(a, b) ≠ s(c, d) →
      segment ℝ (pt a) (pt b) ∩ segment ℝ (pt c) (pt d) ⊆
        pt '' ({a, b} ∩ {c, d} : Set (Fin 36)) := by
    intro a b c d h1 h2 hne
    refine good_segments a b c d (allGood _ h1 _ h2 ?_)
    rintro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h3, h4⟩ := h
    obtain rfl : a = c := Fin.ext h3
    obtain rfl : b = d := Fin.ext h4
    exact hne rfl
  rcases hab with hab | hab <;> rcases hcd with hcd | hcd
  · exact key a b c d hab hcd hne
  · rw [segment_symm ℝ (pt c), Set.pair_comm c d]
    exact key a b d c hab hcd (by rwa [Sym2.eq_swap (a := d)])
  · rw [segment_symm ℝ (pt a), Set.pair_comm a b]
    exact key b a c d hab hcd (by rwa [Sym2.eq_swap (a := b)])
  · rw [segment_symm ℝ (pt a), Set.pair_comm a b, segment_symm ℝ (pt c), Set.pair_comm c d]
    exact key b a d c hab hcd (by rwa [Sym2.eq_swap (a := b), Sym2.eq_swap (a := d)])

end OpenProblemsLab.TotalDomination
