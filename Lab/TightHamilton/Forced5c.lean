import Lab.TightHamilton.Forced5b

/-! Lemma 2.4 for k = 5: apex sets with least position 2 or 3. -/

namespace OpenProblemsLab.TightHamilton

open Finset

theorem forced5At_2 : Forced5At 2 := by unfold Forced5At; decide +kernel
theorem forced5At_3 : Forced5At 3 := by unfold Forced5At; decide +kernel

end OpenProblemsLab.TightHamilton
