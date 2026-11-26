import Lab.HenningYeo.GF10Part0

/-! Per-template `decide` checks for Claim 10 (split across files, built one after another, to bound kernel memory). -/

namespace OpenProblemsLab.HY

lemma no_P10_0_1_2 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    ¬ P10 0 1 2 ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] := by
  decide +kernel

lemma no_P10_0_2_0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    ¬ P10 0 2 0 ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] := by
  decide +kernel

lemma no_P10_0_2_1 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    ¬ P10 0 2 1 ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] := by
  decide +kernel

end OpenProblemsLab.HY
