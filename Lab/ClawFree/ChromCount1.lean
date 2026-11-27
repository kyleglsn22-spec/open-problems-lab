import Lab.ClawFree.ChromCount0

/-! Colouring counts of `G`, part 1 of 6 (see `ChromCount0`). -/

namespace OpenProblemsLab.ClawFree.Counterexample

open MvPolynomial Finset OpenProblemsLab.ClawFree

theorem pref_14 : summ (Enum.genFrom colR [[0, 3, 0, 1]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_15 : summ (Enum.genFrom colR [[0, 3, 0, 2]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_16 : summ (Enum.genFrom colR [[0, 3, 0, 3]] 8) = (4, 8, 16, true) := by
  decide +kernel

theorem pref_17 : summ (Enum.genFrom colR [[0, 3, 1, 2]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_18 : summ (Enum.genFrom colR [[0, 3, 1, 3]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_19 : summ (Enum.genFrom colR [[0, 3, 2, 1]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_20 : summ (Enum.genFrom colR [[0, 3, 2, 3]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_21 : summ (Enum.genFrom colR [[1, 0, 1, 0]] 8) = (0, 0, 16, true) := by
  decide +kernel

theorem pref_22 : summ (Enum.genFrom colR [[1, 0, 1, 2]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_23 : summ (Enum.genFrom colR [[1, 0, 1, 3]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_24 : summ (Enum.genFrom colR [[1, 0, 2, 0]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_25 : summ (Enum.genFrom colR [[1, 0, 2, 3]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_26 : summ (Enum.genFrom colR [[1, 0, 3, 0]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_27 : summ (Enum.genFrom colR [[1, 0, 3, 2]] 8) = (0, 4, 8, true) := by
  decide +kernel

end OpenProblemsLab.ClawFree.Counterexample
