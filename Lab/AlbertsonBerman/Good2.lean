import Lab.AlbertsonBerman.Good1

/-! Part of claim AB-1, see `Lab/AlbertsonBerman/Basic.lean`. -/

namespace OpenProblemsLab.AlbertsonBerman

open SimpleGraph

lemma allGood2 : ∀ e ∈ edges2, ∀ f ∈ edges, e ≠ f → goodPair e.1 e.2 f.1 f.2 = true := by
  decide +kernel

end OpenProblemsLab.AlbertsonBerman
