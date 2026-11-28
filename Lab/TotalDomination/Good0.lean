import Lab.TotalDomination.DrawData

/-! Part of claim GHT-1, see `Lab/TotalDomination/Basic.lean`. -/

namespace OpenProblemsLab.TotalDomination

open SimpleGraph

lemma allGood0 : ∀ e ∈ edges0, ∀ f ∈ edges, e ≠ f → goodPair e.1 e.2 f.1 f.2 = true := by
  decide +kernel

end OpenProblemsLab.TotalDomination
