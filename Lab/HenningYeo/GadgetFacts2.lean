import Lab.HenningYeo.GF10Part9

/-! Claim 10 template check: dispatch to the per-template lemmas. -/

namespace OpenProblemsLab.HY

/-- No set of neighbours of `x` in a template satisfies the constraints of Claim 10. -/
lemma no_P10 {l : Fin 5} {a b : Fin 7} (hv : GValid l a b) (n : Fin 10 → Bool) : ¬ P10 l a b n := by
  have hn : n = ![n 0, n 1, n 2, n 3, n 4, n 5, n 6, n 7, n 8, n 9] := by
    funext i; fin_cases i <;> rfl
  rw [hn]
  fin_cases l <;> fin_cases a <;> fin_cases b
  all_goals first | exact absurd hv (by decide) | skip
  · exact no_P10_0_0_1 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_0_0_2 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_0_1_0 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_0_1_2 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_0_2_0 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_0_2_1 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_1_0_3 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_1_0_4 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_1_3_0 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_1_3_4 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_1_4_0 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_1_4_3 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_2_0_5 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_2_0_6 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_2_5_0 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_2_5_6 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_2_6_0 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_2_6_5 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_3_1_3 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_3_1_5 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_3_3_1 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_3_3_5 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_3_5_1 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_3_5_3 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_4_2_4 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_4_2_6 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_4_4_2 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_4_4_6 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_4_6_2 _ _ _ _ _ _ _ _ _ _
  · exact no_P10_4_6_4 _ _ _ _ _ _ _ _ _ _

end OpenProblemsLab.HY
