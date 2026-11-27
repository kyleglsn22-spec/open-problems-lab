import Lab.ClawFree2.ChromCount4

/-! Colouring counts of `G`, part 5 of 8 (see `ChromCount0`). -/

namespace OpenProblemsLab.ClawFree.Second

open MvPolynomial Finset OpenProblemsLab.ClawFree

theorem pref_160 : summ (Enum.genFrom colR [[2, 2, 0, 0]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_161 : summ (Enum.genFrom colR [[2, 2, 0, 1]] 8) = (0, 4, 0, 0, true) := by
  decide +kernel

theorem pref_162 : summ (Enum.genFrom colR [[2, 2, 0, 2]] 8) = (0, 0, 8, 8, true) := by
  decide +kernel

theorem pref_163 : summ (Enum.genFrom colR [[2, 2, 0, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_164 : summ (Enum.genFrom colR [[2, 2, 1, 0]] 8) = (0, 4, 0, 0, true) := by
  decide +kernel

theorem pref_165 : summ (Enum.genFrom colR [[2, 2, 1, 1]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_166 : summ (Enum.genFrom colR [[2, 2, 1, 2]] 8) = (0, 0, 4, 8, true) := by
  decide +kernel

theorem pref_167 : summ (Enum.genFrom colR [[2, 2, 1, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_168 : summ (Enum.genFrom colR [[2, 2, 2, 0]] 8) = (0, 0, 8, 8, true) := by
  decide +kernel

theorem pref_169 : summ (Enum.genFrom colR [[2, 2, 2, 1]] 8) = (0, 0, 4, 8, true) := by
  decide +kernel

theorem pref_170 : summ (Enum.genFrom colR [[2, 2, 2, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_171 : summ (Enum.genFrom colR [[2, 2, 2, 3]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_172 : summ (Enum.genFrom colR [[2, 2, 3, 0]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_173 : summ (Enum.genFrom colR [[2, 2, 3, 1]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_174 : summ (Enum.genFrom colR [[2, 2, 3, 2]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_175 : summ (Enum.genFrom colR [[2, 2, 3, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_176 : summ (Enum.genFrom colR [[2, 3, 0, 0]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_177 : summ (Enum.genFrom colR [[2, 3, 0, 1]] 8) = (0, 4, 2, 4, true) := by
  decide +kernel

theorem pref_178 : summ (Enum.genFrom colR [[2, 3, 0, 2]] 8) = (0, 0, 8, 4, true) := by
  decide +kernel

theorem pref_179 : summ (Enum.genFrom colR [[2, 3, 0, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_180 : summ (Enum.genFrom colR [[2, 3, 1, 0]] 8) = (0, 4, 2, 4, true) := by
  decide +kernel

theorem pref_181 : summ (Enum.genFrom colR [[2, 3, 1, 1]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_182 : summ (Enum.genFrom colR [[2, 3, 1, 2]] 8) = (0, 0, 4, 4, true) := by
  decide +kernel

theorem pref_183 : summ (Enum.genFrom colR [[2, 3, 1, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_184 : summ (Enum.genFrom colR [[2, 3, 2, 0]] 8) = (0, 0, 8, 4, true) := by
  decide +kernel

theorem pref_185 : summ (Enum.genFrom colR [[2, 3, 2, 1]] 8) = (0, 0, 4, 4, true) := by
  decide +kernel

theorem pref_186 : summ (Enum.genFrom colR [[2, 3, 2, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_187 : summ (Enum.genFrom colR [[2, 3, 2, 3]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_188 : summ (Enum.genFrom colR [[2, 3, 3, 0]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_189 : summ (Enum.genFrom colR [[2, 3, 3, 1]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_190 : summ (Enum.genFrom colR [[2, 3, 3, 2]] 8) = (0, 0, 0, 16, true) := by
  decide +kernel

theorem pref_191 : summ (Enum.genFrom colR [[2, 3, 3, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem part_5 : summ (Enum.genFrom colR L5 8) = (0, 16, 52, 120, true) := by
  simp only [L5, genFrom_cons2, summ_append, pref_160, pref_161, pref_162, pref_163, pref_164, pref_165, pref_166, pref_167, pref_168, pref_169, pref_170, pref_171, pref_172, pref_173, pref_174, pref_175, pref_176, pref_177, pref_178, pref_179, pref_180, pref_181, pref_182, pref_183, pref_184, pref_185, pref_186, pref_187, pref_188, pref_189, pref_190, pref_191]
  rfl

end OpenProblemsLab.ClawFree.Second
