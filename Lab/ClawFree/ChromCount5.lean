import Lab.ClawFree.ChromCount4

/-! Colouring counts of `G`, part 5 of 6 (see `ChromCount0`). -/

namespace OpenProblemsLab.ClawFree.Counterexample

open MvPolynomial Finset OpenProblemsLab.ClawFree

theorem pref_70 : summ (Enum.genFrom colR [[3, 1, 0, 1]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_71 : summ (Enum.genFrom colR [[3, 1, 0, 2]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_72 : summ (Enum.genFrom colR [[3, 1, 2, 0]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_73 : summ (Enum.genFrom colR [[3, 1, 2, 1]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_74 : summ (Enum.genFrom colR [[3, 1, 3, 0]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_75 : summ (Enum.genFrom colR [[3, 1, 3, 1]] 8) = (4, 0, 16, true) := by
  decide +kernel

theorem pref_76 : summ (Enum.genFrom colR [[3, 1, 3, 2]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_77 : summ (Enum.genFrom colR [[3, 2, 0, 1]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_78 : summ (Enum.genFrom colR [[3, 2, 0, 2]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_79 : summ (Enum.genFrom colR [[3, 2, 1, 0]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_80 : summ (Enum.genFrom colR [[3, 2, 1, 2]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_81 : summ (Enum.genFrom colR [[3, 2, 3, 0]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_82 : summ (Enum.genFrom colR [[3, 2, 3, 1]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_83 : summ (Enum.genFrom colR [[3, 2, 3, 2]] 8) = (0, 0, 16, true) := by
  decide +kernel

end OpenProblemsLab.ClawFree.Counterexample
