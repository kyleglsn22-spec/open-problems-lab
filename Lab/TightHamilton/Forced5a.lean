import Lab.TightHamilton.Forced34

/-! Lemma 2.4 for k = 5: apex sets with least position 0. -/

namespace OpenProblemsLab.TightHamilton

open Finset

theorem forced5At_0 : Forced5At 0 := by unfold Forced5At; decide +kernel

end OpenProblemsLab.TightHamilton
