import Lab.ClawFree.ChromCount3

/-! Colouring counts of `G`, part 4 of 6 (see `ChromCount0`). -/

namespace OpenProblemsLab.ClawFree.Counterexample

open MvPolynomial Finset OpenProblemsLab.ClawFree

theorem pref_56 : summ (Enum.genFrom colR [[2, 3, 0, 1]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_57 : summ (Enum.genFrom colR [[2, 3, 0, 3]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_58 : summ (Enum.genFrom colR [[2, 3, 1, 0]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_59 : summ (Enum.genFrom colR [[2, 3, 1, 3]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_60 : summ (Enum.genFrom colR [[2, 3, 2, 0]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_61 : summ (Enum.genFrom colR [[2, 3, 2, 1]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_62 : summ (Enum.genFrom colR [[2, 3, 2, 3]] 8) = (0, 0, 16, true) := by
  decide +kernel

theorem pref_63 : summ (Enum.genFrom colR [[3, 0, 1, 0]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_64 : summ (Enum.genFrom colR [[3, 0, 1, 2]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_65 : summ (Enum.genFrom colR [[3, 0, 2, 0]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_66 : summ (Enum.genFrom colR [[3, 0, 2, 1]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_67 : summ (Enum.genFrom colR [[3, 0, 3, 0]] 8) = (4, 8, 16, true) := by
  decide +kernel

theorem pref_68 : summ (Enum.genFrom colR [[3, 0, 3, 1]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_69 : summ (Enum.genFrom colR [[3, 0, 3, 2]] 8) = (0, 4, 8, true) := by
  decide +kernel

end OpenProblemsLab.ClawFree.Counterexample
