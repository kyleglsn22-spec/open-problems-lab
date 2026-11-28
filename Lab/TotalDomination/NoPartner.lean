import Lab.TotalDomination.Lemma

/-! Part of claim GHT-1, see `Lab/TotalDomination/Basic.lean`. -/

namespace OpenProblemsLab.TotalDomination

open SimpleGraph

lemma nbr_1_3 : ∀ u : Fin 36, adjB 3 u = true → u = 0 ∨ u = 2 ∨ u = 4 ∨ u = 11 := by
  decide +kernel

lemma nbr_1_5 : ∀ u : Fin 36, adjB 5 u = true → u = 0 ∨ u = 4 ∨ u = 6 ∨ u = 12 := by
  decide +kernel

lemma nbr_1_9 : ∀ u : Fin 36, adjB 9 u = true → u = 1 ∨ u = 7 ∨ u = 8 ∨ u = 13 := by
  decide +kernel

lemma nbr_2_3 : ∀ u : Fin 36, adjB 14 u = true → u = 1 ∨ u = 2 ∨ u = 15 ∨ u = 22 := by
  decide +kernel

lemma nbr_2_5 : ∀ u : Fin 36, adjB 16 u = true → u = 1 ∨ u = 15 ∨ u = 17 ∨ u = 23 := by
  decide +kernel

lemma nbr_2_9 : ∀ u : Fin 36, adjB 20 u = true → u = 0 ∨ u = 18 ∨ u = 19 ∨ u = 24 := by
  decide +kernel

lemma nbr_3_3 : ∀ u : Fin 36, adjB 25 u = true → u = 0 ∨ u = 1 ∨ u = 26 ∨ u = 33 := by
  decide +kernel

lemma nbr_3_5 : ∀ u : Fin 36, adjB 27 u = true → u = 0 ∨ u = 26 ∨ u = 28 ∨ u = 34 := by
  decide +kernel

lemma nbr_3_9 : ∀ u : Fin 36, adjB 31 u = true → u = 18 ∨ u = 29 ∨ u = 30 ∨ u = 35 := by
  decide +kernel

/-- Lemma 3.1 transported to the copy `H^(i)` of `G₁₄` inside `B`. -/
theorem no_partner_coloring_B (c : Fin 36 → Fin 4) (hp : ∀ u v, adjB u v = true → c u ≠ c v)
    (hnd : ∀ v, ∃ u, adjB v u = true ∧ c u = partner (c v)) : False := by
  have n1_3 : c 0 = partner (c 3) ∨ c 2 = partner (c 3) ∨ c 4 = partner (c 3) ∨ c 11 = partner (c 3) := by
    obtain ⟨u, hu, h⟩ := hnd 3
    rcases nbr_1_3 u hu with rfl | rfl | rfl | rfl
    exacts [(Or.inl h), (Or.inr (Or.inl h)), (Or.inr (Or.inr (Or.inl h))), (Or.inr (Or.inr (Or.inr h)))]
  have n1_5 : c 0 = partner (c 5) ∨ c 4 = partner (c 5) ∨ c 6 = partner (c 5) ∨ c 12 = partner (c 5) := by
    obtain ⟨u, hu, h⟩ := hnd 5
    rcases nbr_1_5 u hu with rfl | rfl | rfl | rfl
    exacts [(Or.inl h), (Or.inr (Or.inl h)), (Or.inr (Or.inr (Or.inl h))), (Or.inr (Or.inr (Or.inr h)))]
  have n1_9 : c 1 = partner (c 9) ∨ c 7 = partner (c 9) ∨ c 8 = partner (c 9) ∨ c 13 = partner (c 9) := by
    obtain ⟨u, hu, h⟩ := hnd 9
    rcases nbr_1_9 u hu with rfl | rfl | rfl | rfl
    exacts [(Or.inl h), (Or.inr (Or.inl h)), (Or.inr (Or.inr (Or.inl h))), (Or.inr (Or.inr (Or.inr h)))]
  have e1 : c 2 ≠ partner (c 0) := fun hP =>
    lemma31 
      (c 0) (c 2) (hp 0 2 (by decide +kernel)) hP (c 1) (hp 0 1 (by decide +kernel)) (hp 2 1 (by decide +kernel)) (c 3) (hp 0 3 (by decide +kernel)) (hp 2 3 (by decide +kernel)) (c 4) (hp 0 4 (by decide +kernel)) (hp 3 4 (by decide +kernel)) (c 11) (hp 2 11 (by decide +kernel)) (hp 3 11 (by decide +kernel)) (hp 4 11 (by decide +kernel)) n1_3 (c 5) (hp 0 5 (by decide +kernel)) (hp 4 5 (by decide +kernel)) (c 12) (hp 4 12 (by decide +kernel)) (hp 11 12 (by decide +kernel)) (hp 5 12 (by decide +kernel)) (c 6) (hp 0 6 (by decide +kernel)) (hp 5 6 (by decide +kernel)) (hp 12 6 (by decide +kernel)) n1_5 (c 10) (hp 2 10 (by decide +kernel)) (hp 11 10 (by decide +kernel)) (hp 12 10 (by decide +kernel)) (hp 6 10 (by decide +kernel)) (c 7) (hp 0 7 (by decide +kernel)) (hp 1 7 (by decide +kernel)) (hp 6 7 (by decide +kernel)) (c 8) (hp 2 8 (by decide +kernel)) (hp 1 8 (by decide +kernel)) (hp 10 8 (by decide +kernel)) (c 13) (hp 6 13 (by decide +kernel)) (hp 10 13 (by decide +kernel)) (hp 7 13 (by decide +kernel)) (hp 8 13 (by decide +kernel)) (c 9) (hp 1 9 (by decide +kernel)) (hp 7 9 (by decide +kernel)) (hp 8 9 (by decide +kernel)) (hp 13 9 (by decide +kernel)) n1_9
  have n2_3 : c 1 = partner (c 14) ∨ c 2 = partner (c 14) ∨ c 15 = partner (c 14) ∨ c 22 = partner (c 14) := by
    obtain ⟨u, hu, h⟩ := hnd 14
    rcases nbr_2_3 u hu with rfl | rfl | rfl | rfl
    exacts [(Or.inl h), (Or.inr (Or.inl h)), (Or.inr (Or.inr (Or.inl h))), (Or.inr (Or.inr (Or.inr h)))]
  have n2_5 : c 1 = partner (c 16) ∨ c 15 = partner (c 16) ∨ c 17 = partner (c 16) ∨ c 23 = partner (c 16) := by
    obtain ⟨u, hu, h⟩ := hnd 16
    rcases nbr_2_5 u hu with rfl | rfl | rfl | rfl
    exacts [(Or.inl h), (Or.inr (Or.inl h)), (Or.inr (Or.inr (Or.inl h))), (Or.inr (Or.inr (Or.inr h)))]
  have n2_9 : c 0 = partner (c 20) ∨ c 18 = partner (c 20) ∨ c 19 = partner (c 20) ∨ c 24 = partner (c 20) := by
    obtain ⟨u, hu, h⟩ := hnd 20
    rcases nbr_2_9 u hu with rfl | rfl | rfl | rfl
    exacts [(Or.inl h), (Or.inr (Or.inl h)), (Or.inr (Or.inr (Or.inl h))), (Or.inr (Or.inr (Or.inr h)))]
  have e2 : c 2 ≠ partner (c 1) := fun hP =>
    lemma31 
      (c 1) (c 2) (hp 1 2 (by decide +kernel)) hP (c 0) (hp 1 0 (by decide +kernel)) (hp 2 0 (by decide +kernel)) (c 14) (hp 1 14 (by decide +kernel)) (hp 2 14 (by decide +kernel)) (c 15) (hp 1 15 (by decide +kernel)) (hp 14 15 (by decide +kernel)) (c 22) (hp 2 22 (by decide +kernel)) (hp 14 22 (by decide +kernel)) (hp 15 22 (by decide +kernel)) n2_3 (c 16) (hp 1 16 (by decide +kernel)) (hp 15 16 (by decide +kernel)) (c 23) (hp 15 23 (by decide +kernel)) (hp 22 23 (by decide +kernel)) (hp 16 23 (by decide +kernel)) (c 17) (hp 1 17 (by decide +kernel)) (hp 16 17 (by decide +kernel)) (hp 23 17 (by decide +kernel)) n2_5 (c 21) (hp 2 21 (by decide +kernel)) (hp 22 21 (by decide +kernel)) (hp 23 21 (by decide +kernel)) (hp 17 21 (by decide +kernel)) (c 18) (hp 1 18 (by decide +kernel)) (hp 0 18 (by decide +kernel)) (hp 17 18 (by decide +kernel)) (c 19) (hp 2 19 (by decide +kernel)) (hp 0 19 (by decide +kernel)) (hp 21 19 (by decide +kernel)) (c 24) (hp 17 24 (by decide +kernel)) (hp 21 24 (by decide +kernel)) (hp 18 24 (by decide +kernel)) (hp 19 24 (by decide +kernel)) (c 20) (hp 0 20 (by decide +kernel)) (hp 18 20 (by decide +kernel)) (hp 19 20 (by decide +kernel)) (hp 24 20 (by decide +kernel)) n2_9
  have n3_3 : c 0 = partner (c 25) ∨ c 1 = partner (c 25) ∨ c 26 = partner (c 25) ∨ c 33 = partner (c 25) := by
    obtain ⟨u, hu, h⟩ := hnd 25
    rcases nbr_3_3 u hu with rfl | rfl | rfl | rfl
    exacts [(Or.inl h), (Or.inr (Or.inl h)), (Or.inr (Or.inr (Or.inl h))), (Or.inr (Or.inr (Or.inr h)))]
  have n3_5 : c 0 = partner (c 27) ∨ c 26 = partner (c 27) ∨ c 28 = partner (c 27) ∨ c 34 = partner (c 27) := by
    obtain ⟨u, hu, h⟩ := hnd 27
    rcases nbr_3_5 u hu with rfl | rfl | rfl | rfl
    exacts [(Or.inl h), (Or.inr (Or.inl h)), (Or.inr (Or.inr (Or.inl h))), (Or.inr (Or.inr (Or.inr h)))]
  have n3_9 : c 18 = partner (c 31) ∨ c 29 = partner (c 31) ∨ c 30 = partner (c 31) ∨ c 35 = partner (c 31) := by
    obtain ⟨u, hu, h⟩ := hnd 31
    rcases nbr_3_9 u hu with rfl | rfl | rfl | rfl
    exacts [(Or.inl h), (Or.inr (Or.inl h)), (Or.inr (Or.inr (Or.inl h))), (Or.inr (Or.inr (Or.inr h)))]
  have e3 : c 1 ≠ partner (c 0) := fun hP =>
    lemma31 
      (c 0) (c 1) (hp 0 1 (by decide +kernel)) hP (c 18) (hp 0 18 (by decide +kernel)) (hp 1 18 (by decide +kernel)) (c 25) (hp 0 25 (by decide +kernel)) (hp 1 25 (by decide +kernel)) (c 26) (hp 0 26 (by decide +kernel)) (hp 25 26 (by decide +kernel)) (c 33) (hp 1 33 (by decide +kernel)) (hp 25 33 (by decide +kernel)) (hp 26 33 (by decide +kernel)) n3_3 (c 27) (hp 0 27 (by decide +kernel)) (hp 26 27 (by decide +kernel)) (c 34) (hp 26 34 (by decide +kernel)) (hp 33 34 (by decide +kernel)) (hp 27 34 (by decide +kernel)) (c 28) (hp 0 28 (by decide +kernel)) (hp 27 28 (by decide +kernel)) (hp 34 28 (by decide +kernel)) n3_5 (c 32) (hp 1 32 (by decide +kernel)) (hp 33 32 (by decide +kernel)) (hp 34 32 (by decide +kernel)) (hp 28 32 (by decide +kernel)) (c 29) (hp 0 29 (by decide +kernel)) (hp 18 29 (by decide +kernel)) (hp 28 29 (by decide +kernel)) (c 30) (hp 1 30 (by decide +kernel)) (hp 18 30 (by decide +kernel)) (hp 32 30 (by decide +kernel)) (c 35) (hp 28 35 (by decide +kernel)) (hp 32 35 (by decide +kernel)) (hp 29 35 (by decide +kernel)) (hp 30 35 (by decide +kernel)) (c 31) (hp 18 31 (by decide +kernel)) (hp 29 31 (by decide +kernel)) (hp 30 31 (by decide +kernel)) (hp 35 31 (by decide +kernel)) n3_9
  exact triangle (c 0) (c 1) (c 2) (hp 0 1 (by decide +kernel)) (hp 0 2 (by decide +kernel))
    (hp 1 2 (by decide +kernel)) e1 e2 e3

end OpenProblemsLab.TotalDomination
