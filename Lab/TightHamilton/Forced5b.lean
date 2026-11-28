import Lab.TightHamilton.Forced5a

/-! Lemma 2.4 for k = 5: apex sets with least position 1. -/

namespace OpenProblemsLab.TightHamilton

open Finset

theorem forced5At_1 : Forced5At 1 := by unfold Forced5At; decide +kernel

end OpenProblemsLab.TightHamilton
