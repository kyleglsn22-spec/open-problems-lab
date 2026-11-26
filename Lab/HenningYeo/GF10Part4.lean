import Lab.HenningYeo.GF10Part3

/-! Per-template `decide` checks for Claim 10 (split across files, built one after another, to bound kernel memory). -/

namespace OpenProblemsLab.HY

lemma no_P10_2_0_5 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    ¬ P10 2 0 5 ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] := by
  decide +kernel

lemma no_P10_2_0_6 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    ¬ P10 2 0 6 ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] := by
  decide +kernel

lemma no_P10_2_5_0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    ¬ P10 2 5 0 ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] := by
  decide +kernel

end OpenProblemsLab.HY
