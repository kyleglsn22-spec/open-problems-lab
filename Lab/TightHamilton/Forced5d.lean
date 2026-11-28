import Lab.TightHamilton.Forced5c

/-! Lemma 2.4 for k = 5: apex sets with least position 4, 5 or 6. -/

namespace OpenProblemsLab.TightHamilton

open Finset

theorem forced5At_4 : Forced5At 4 := by unfold Forced5At; decide +kernel
theorem forced5At_5 : Forced5At 5 := by unfold Forced5At; decide +kernel
theorem forced5At_6 : Forced5At 6 := by unfold Forced5At; decide +kernel

end OpenProblemsLab.TightHamilton
