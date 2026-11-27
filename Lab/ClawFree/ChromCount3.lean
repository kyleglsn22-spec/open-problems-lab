import Lab.ClawFree.ChromCount2

/-! Colouring counts of `G`, part 3 of 6 (see `ChromCount0`). -/

namespace OpenProblemsLab.ClawFree.Counterexample

open MvPolynomial Finset OpenProblemsLab.ClawFree

theorem pref_42 : summ (Enum.genFrom colR [[2, 0, 1, 0]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_43 : summ (Enum.genFrom colR [[2, 0, 1, 3]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_44 : summ (Enum.genFrom colR [[2, 0, 2, 0]] 8) = (4, 0, 16, true) := by
  decide +kernel

theorem pref_45 : summ (Enum.genFrom colR [[2, 0, 2, 1]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_46 : summ (Enum.genFrom colR [[2, 0, 2, 3]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_47 : summ (Enum.genFrom colR [[2, 0, 3, 0]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_48 : summ (Enum.genFrom colR [[2, 0, 3, 1]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_49 : summ (Enum.genFrom colR [[2, 1, 0, 1]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_50 : summ (Enum.genFrom colR [[2, 1, 0, 3]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_51 : summ (Enum.genFrom colR [[2, 1, 2, 0]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_52 : summ (Enum.genFrom colR [[2, 1, 2, 1]] 8) = (4, 8, 16, true) := by
  decide +kernel

theorem pref_53 : summ (Enum.genFrom colR [[2, 1, 2, 3]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_54 : summ (Enum.genFrom colR [[2, 1, 3, 0]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_55 : summ (Enum.genFrom colR [[2, 1, 3, 1]] 8) = (4, 4, 8, true) := by
  decide +kernel

end OpenProblemsLab.ClawFree.Counterexample
