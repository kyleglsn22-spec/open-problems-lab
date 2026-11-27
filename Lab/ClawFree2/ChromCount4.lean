import Lab.ClawFree2.ChromCount3

/-! Colouring counts of `G`, part 4 of 8 (see `ChromCount0`). -/

namespace OpenProblemsLab.ClawFree.Second

open MvPolynomial Finset OpenProblemsLab.ClawFree

theorem pref_128 : summ (Enum.genFrom colR [[2, 0, 0, 0]] 8) = (8, 8, 12, 0, true) := by
  decide +kernel

theorem pref_129 : summ (Enum.genFrom colR [[2, 0, 0, 1]] 8) = (0, 6, 10, 8, true) := by
  decide +kernel

theorem pref_130 : summ (Enum.genFrom colR [[2, 0, 0, 2]] 8) = (0, 0, 8, 16, true) := by
  decide +kernel

theorem pref_131 : summ (Enum.genFrom colR [[2, 0, 0, 3]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_132 : summ (Enum.genFrom colR [[2, 0, 1, 0]] 8) = (0, 2, 2, 4, true) := by
  decide +kernel

theorem pref_133 : summ (Enum.genFrom colR [[2, 0, 1, 1]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_134 : summ (Enum.genFrom colR [[2, 0, 1, 2]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_135 : summ (Enum.genFrom colR [[2, 0, 1, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_136 : summ (Enum.genFrom colR [[2, 0, 2, 0]] 8) = (0, 0, 4, 8, true) := by
  decide +kernel

theorem pref_137 : summ (Enum.genFrom colR [[2, 0, 2, 1]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_138 : summ (Enum.genFrom colR [[2, 0, 2, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_139 : summ (Enum.genFrom colR [[2, 0, 2, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_140 : summ (Enum.genFrom colR [[2, 0, 3, 0]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_141 : summ (Enum.genFrom colR [[2, 0, 3, 1]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_142 : summ (Enum.genFrom colR [[2, 0, 3, 2]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_143 : summ (Enum.genFrom colR [[2, 0, 3, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_144 : summ (Enum.genFrom colR [[2, 1, 0, 0]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_145 : summ (Enum.genFrom colR [[2, 1, 0, 1]] 8) = (0, 2, 2, 4, true) := by
  decide +kernel

theorem pref_146 : summ (Enum.genFrom colR [[2, 1, 0, 2]] 8) = (0, 0, 4, 4, true) := by
  decide +kernel

theorem pref_147 : summ (Enum.genFrom colR [[2, 1, 0, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_148 : summ (Enum.genFrom colR [[2, 1, 1, 0]] 8) = (0, 6, 6, 8, true) := by
  decide +kernel

theorem pref_149 : summ (Enum.genFrom colR [[2, 1, 1, 1]] 8) = (0, 8, 0, 0, true) := by
  decide +kernel

theorem pref_150 : summ (Enum.genFrom colR [[2, 1, 1, 2]] 8) = (0, 0, 4, 16, true) := by
  decide +kernel

theorem pref_151 : summ (Enum.genFrom colR [[2, 1, 1, 3]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_152 : summ (Enum.genFrom colR [[2, 1, 2, 0]] 8) = (0, 0, 4, 4, true) := by
  decide +kernel

theorem pref_153 : summ (Enum.genFrom colR [[2, 1, 2, 1]] 8) = (0, 0, 4, 8, true) := by
  decide +kernel

theorem pref_154 : summ (Enum.genFrom colR [[2, 1, 2, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_155 : summ (Enum.genFrom colR [[2, 1, 2, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_156 : summ (Enum.genFrom colR [[2, 1, 3, 0]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_157 : summ (Enum.genFrom colR [[2, 1, 3, 1]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_158 : summ (Enum.genFrom colR [[2, 1, 3, 2]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_159 : summ (Enum.genFrom colR [[2, 1, 3, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem part_4 : summ (Enum.genFrom colR L4 8) = (8, 32, 60, 144, true) := by
  simp only [L4, genFrom_cons2, summ_append, pref_128, pref_129, pref_130, pref_131, pref_132, pref_133, pref_134, pref_135, pref_136, pref_137, pref_138, pref_139, pref_140, pref_141, pref_142, pref_143, pref_144, pref_145, pref_146, pref_147, pref_148, pref_149, pref_150, pref_151, pref_152, pref_153, pref_154, pref_155, pref_156, pref_157, pref_158, pref_159]
  rfl

end OpenProblemsLab.ClawFree.Second
