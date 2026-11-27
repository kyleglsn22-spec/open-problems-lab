import Lab.AlbertsonBerman.Hits

/-! Part of claim AB-1, see `Lab/AlbertsonBerman/Basic.lean`. -/

namespace OpenProblemsLab.AlbertsonBerman

open SimpleGraph

/-! ## The forest bound -/

lemma mem_parts : ∀ v : Fin 29, (v ∈ QI ∧ v ∉ RI ∧ v ≠ 27 ∧ v ≠ 28) ∨ (v ∉ QI ∧ v ∈ RI ∧ v ≠ 27 ∧ v ≠ 28) ∨
    (v ∉ QI ∧ v ∉ RI ∧ (v = 27 ∨ v = 28)) := by decide +kernel

lemma card_split (S : Finset (Fin 29)) :
    S.card = (S ∩ QI).card + (S ∩ RI).card + (S ∩ {27, 28}).card := by
  have h1 := Finset.card_inter_add_card_sdiff S QI
  have h2 := Finset.card_inter_add_card_sdiff (S \ QI) RI
  have e1 : (S \ QI) ∩ RI = S ∩ RI := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    rcases mem_parts v with h | h | h <;> tauto
  have e2 : (S \ QI) \ RI = S ∩ {27, 28} := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    rcases mem_parts v with h | h | h <;> tauto
  rw [e1, e2] at h2
  omega

/-- Every induced forest of `G₂₉` has at most 14 vertices. -/
theorem card_le_of_isAcyclic (S : Finset (Fin 29))
    (hS : (G.induce (S : Set (Fin 29))).IsAcyclic) : S.card ≤ 14 := by
  rw [card_split S]
  by_cases hx : (27 : Fin 29) ∈ S <;> by_cases hy : (28 : Fin 29) ∈ S
  · have hP : S ∩ {27, 28} = {27, 28} := by
      ext v; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro (rfl | rfl) <;> simp_all
    have hX : ∀ v ∈ ([27, 28] : List (Fin 29)), v ∈ S := by
      intro v hv
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl <;> assumption
    have hq := card_inter_lt S QI QL [27, 28] cycQxy _ cycQxy_valid QL_eq hX hitQxy hS
    have hr := card_inter_lt S RI RL [27, 28] cycRxy _ cycRxy_valid RL_eq hX hitRxy hS
    rw [hP]; simp only [Finset.card_insert_of_notMem (by decide : (27 : Fin 29) ∉ ({28} : Finset (Fin 29))),
      Finset.card_singleton]
    omega
  · have hP : S ∩ {27, 28} = {27} := by
      ext v; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, rfl | rfl⟩
        · rfl
        · exact absurd h1 hy
      · rintro rfl; exact ⟨hx, Or.inl rfl⟩
    have hX : ∀ v ∈ ([27] : List (Fin 29)), v ∈ S := by
      intro v hv; rw [List.mem_singleton] at hv; rw [hv]; exact hx
    have hq := card_inter_lt S QI QL [27] cycQx _ cycQx_valid QL_eq hX hitQx hS
    have hr := card_inter_lt S RI RL [27] cycRx _ cycRx_valid RL_eq hX hitRx hS
    rw [hP, Finset.card_singleton]
    omega
  · have hP : S ∩ {27, 28} = {28} := by
      ext v; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, rfl | rfl⟩
        · exact absurd h1 hx
        · rfl
      · rintro rfl; exact ⟨hy, Or.inr rfl⟩
    have hX : ∀ v ∈ ([28] : List (Fin 29)), v ∈ S := by
      intro v hv; rw [List.mem_singleton] at hv; rw [hv]; exact hy
    have hq := card_inter_lt S QI QL [28] cycQy _ cycQy_valid QL_eq hX hitQy hS
    have hr := card_inter_lt S RI RL [28] cycRy _ cycRy_valid RL_eq hX hitRy hS
    rw [hP, Finset.card_singleton]
    omega
  · have hP : S ∩ {27, 28} = ∅ := by
      ext v; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false, not_and]
      rintro h (rfl | rfl)
      · exact hx h
      · exact hy h
    have hX : ∀ v ∈ ([] : List (Fin 29)), v ∈ S := by simp
    have hq := card_inter_lt S QI QL [] cycQ0 _ cycQ0_valid QL_eq hX hitQ0 hS
    have hr := card_inter_lt S RI RL [] cycR0 _ cycR0_valid RL_eq hX hitR0 hS
    rw [hP, Finset.card_empty]
    omega

end OpenProblemsLab.AlbertsonBerman
