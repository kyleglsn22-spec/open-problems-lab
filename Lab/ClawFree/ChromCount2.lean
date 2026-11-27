import Lab.ClawFree.ChromCount1

/-! Colouring counts of `G`, part 2 of 6 (see `ChromCount0`). -/

namespace OpenProblemsLab.ClawFree.Counterexample

open MvPolynomial Finset OpenProblemsLab.ClawFree

theorem pref_28 : summ (Enum.genFrom colR [[1, 2, 0, 2]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_29 : summ (Enum.genFrom colR [[1, 2, 0, 3]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_30 : summ (Enum.genFrom colR [[1, 2, 1, 0]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_31 : summ (Enum.genFrom colR [[1, 2, 1, 2]] 8) = (4, 8, 16, true) := by
  decide +kernel

theorem pref_32 : summ (Enum.genFrom colR [[1, 2, 1, 3]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_33 : summ (Enum.genFrom colR [[1, 2, 3, 0]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_34 : summ (Enum.genFrom colR [[1, 2, 3, 2]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_35 : summ (Enum.genFrom colR [[1, 3, 0, 2]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_36 : summ (Enum.genFrom colR [[1, 3, 0, 3]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_37 : summ (Enum.genFrom colR [[1, 3, 1, 0]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_38 : summ (Enum.genFrom colR [[1, 3, 1, 2]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_39 : summ (Enum.genFrom colR [[1, 3, 1, 3]] 8) = (4, 0, 16, true) := by
  decide +kernel

theorem pref_40 : summ (Enum.genFrom colR [[1, 3, 2, 0]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_41 : summ (Enum.genFrom colR [[1, 3, 2, 3]] 8) = (0, 4, 8, true) := by
  decide +kernel

end OpenProblemsLab.ClawFree.Counterexample
