import Lab.ClawFree2.ChromCount2

/-! Colouring counts of `G`, part 3 of 8 (see `ChromCount0`). -/

namespace OpenProblemsLab.ClawFree.Second

open MvPolynomial Finset OpenProblemsLab.ClawFree

theorem pref_96 : summ (Enum.genFrom colR [[1, 2, 0, 0]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_97 : summ (Enum.genFrom colR [[1, 2, 0, 1]] 8) = (0, 4, 4, 4, true) := by
  decide +kernel

theorem pref_98 : summ (Enum.genFrom colR [[1, 2, 0, 2]] 8) = (0, 0, 2, 4, true) := by
  decide +kernel

theorem pref_99 : summ (Enum.genFrom colR [[1, 2, 0, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_100 : summ (Enum.genFrom colR [[1, 2, 1, 0]] 8) = (0, 4, 4, 4, true) := by
  decide +kernel

theorem pref_101 : summ (Enum.genFrom colR [[1, 2, 1, 1]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_102 : summ (Enum.genFrom colR [[1, 2, 1, 2]] 8) = (0, 0, 4, 8, true) := by
  decide +kernel

theorem pref_103 : summ (Enum.genFrom colR [[1, 2, 1, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_104 : summ (Enum.genFrom colR [[1, 2, 2, 0]] 8) = (0, 0, 6, 8, true) := by
  decide +kernel

theorem pref_105 : summ (Enum.genFrom colR [[1, 2, 2, 1]] 8) = (0, 0, 4, 16, true) := by
  decide +kernel

theorem pref_106 : summ (Enum.genFrom colR [[1, 2, 2, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_107 : summ (Enum.genFrom colR [[1, 2, 2, 3]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_108 : summ (Enum.genFrom colR [[1, 2, 3, 0]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_109 : summ (Enum.genFrom colR [[1, 2, 3, 1]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_110 : summ (Enum.genFrom colR [[1, 2, 3, 2]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_111 : summ (Enum.genFrom colR [[1, 2, 3, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_112 : summ (Enum.genFrom colR [[1, 3, 0, 0]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_113 : summ (Enum.genFrom colR [[1, 3, 0, 1]] 8) = (0, 4, 8, 4, true) := by
  decide +kernel

theorem pref_114 : summ (Enum.genFrom colR [[1, 3, 0, 2]] 8) = (0, 0, 2, 4, true) := by
  decide +kernel

theorem pref_115 : summ (Enum.genFrom colR [[1, 3, 0, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_116 : summ (Enum.genFrom colR [[1, 3, 1, 0]] 8) = (0, 4, 8, 4, true) := by
  decide +kernel

theorem pref_117 : summ (Enum.genFrom colR [[1, 3, 1, 1]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_118 : summ (Enum.genFrom colR [[1, 3, 1, 2]] 8) = (0, 0, 4, 4, true) := by
  decide +kernel

theorem pref_119 : summ (Enum.genFrom colR [[1, 3, 1, 3]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_120 : summ (Enum.genFrom colR [[1, 3, 2, 0]] 8) = (0, 0, 2, 4, true) := by
  decide +kernel

theorem pref_121 : summ (Enum.genFrom colR [[1, 3, 2, 1]] 8) = (0, 0, 4, 4, true) := by
  decide +kernel

theorem pref_122 : summ (Enum.genFrom colR [[1, 3, 2, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_123 : summ (Enum.genFrom colR [[1, 3, 2, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_124 : summ (Enum.genFrom colR [[1, 3, 3, 0]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_125 : summ (Enum.genFrom colR [[1, 3, 3, 1]] 8) = (0, 0, 0, 16, true) := by
  decide +kernel

theorem pref_126 : summ (Enum.genFrom colR [[1, 3, 3, 2]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_127 : summ (Enum.genFrom colR [[1, 3, 3, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem part_3 : summ (Enum.genFrom colR L3 8) = (0, 16, 52, 144, true) := by
  simp only [L3, genFrom_cons2, summ_append, pref_96, pref_97, pref_98, pref_99, pref_100, pref_101, pref_102, pref_103, pref_104, pref_105, pref_106, pref_107, pref_108, pref_109, pref_110, pref_111, pref_112, pref_113, pref_114, pref_115, pref_116, pref_117, pref_118, pref_119, pref_120, pref_121, pref_122, pref_123, pref_124, pref_125, pref_126, pref_127]
  rfl

end OpenProblemsLab.ClawFree.Second
