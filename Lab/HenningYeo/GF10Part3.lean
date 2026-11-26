import Lab.HenningYeo.GF10Part2

/-! Per-template `decide` checks for Claim 10 (split across files, built one after another, to bound kernel memory). -/

namespace OpenProblemsLab.HY

lemma no_P10_1_3_4 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    ¬ P10 1 3 4 ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] := by
  decide +kernel

lemma no_P10_1_4_0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    ¬ P10 1 4 0 ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] := by
  decide +kernel

lemma no_P10_1_4_3 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    ¬ P10 1 4 3 ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] := by
  decide +kernel

end OpenProblemsLab.HY
