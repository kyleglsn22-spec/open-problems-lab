import Lab.HenningYeo.GF10Part8

/-! Per-template `decide` checks for Claim 10 (split across files, built one after another, to bound kernel memory). -/

namespace OpenProblemsLab.HY

lemma no_P10_4_4_6 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    ¬ P10 4 4 6 ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] := by
  decide +kernel

lemma no_P10_4_6_2 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    ¬ P10 4 6 2 ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] := by
  decide +kernel

lemma no_P10_4_6_4 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    ¬ P10 4 6 4 ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] := by
  decide +kernel

end OpenProblemsLab.HY
