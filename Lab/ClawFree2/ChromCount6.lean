import Lab.ClawFree2.ChromCount5

/-! Colouring counts of `G`, part 6 of 8 (see `ChromCount0`). -/

namespace OpenProblemsLab.ClawFree.Second

open MvPolynomial Finset OpenProblemsLab.ClawFree

theorem pref_192 : summ (Enum.genFrom colR [[3, 0, 0, 0]] 8) = (8, 8, 16, 0, true) := by
  decide +kernel

theorem pref_193 : summ (Enum.genFrom colR [[3, 0, 0, 1]] 8) = (0, 6, 6, 8, true) := by
  decide +kernel

theorem pref_194 : summ (Enum.genFrom colR [[3, 0, 0, 2]] 8) = (0, 0, 6, 8, true) := by
  decide +kernel

theorem pref_195 : summ (Enum.genFrom colR [[3, 0, 0, 3]] 8) = (0, 0, 0, 16, true) := by
  decide +kernel

theorem pref_196 : summ (Enum.genFrom colR [[3, 0, 1, 0]] 8) = (0, 2, 2, 4, true) := by
  decide +kernel

theorem pref_197 : summ (Enum.genFrom colR [[3, 0, 1, 1]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_198 : summ (Enum.genFrom colR [[3, 0, 1, 2]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_199 : summ (Enum.genFrom colR [[3, 0, 1, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_200 : summ (Enum.genFrom colR [[3, 0, 2, 0]] 8) = (0, 0, 2, 4, true) := by
  decide +kernel

theorem pref_201 : summ (Enum.genFrom colR [[3, 0, 2, 1]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_202 : summ (Enum.genFrom colR [[3, 0, 2, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_203 : summ (Enum.genFrom colR [[3, 0, 2, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_204 : summ (Enum.genFrom colR [[3, 0, 3, 0]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_205 : summ (Enum.genFrom colR [[3, 0, 3, 1]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_206 : summ (Enum.genFrom colR [[3, 0, 3, 2]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_207 : summ (Enum.genFrom colR [[3, 0, 3, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_208 : summ (Enum.genFrom colR [[3, 1, 0, 0]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_209 : summ (Enum.genFrom colR [[3, 1, 0, 1]] 8) = (0, 2, 4, 4, true) := by
  decide +kernel

theorem pref_210 : summ (Enum.genFrom colR [[3, 1, 0, 2]] 8) = (0, 0, 2, 4, true) := by
  decide +kernel

theorem pref_211 : summ (Enum.genFrom colR [[3, 1, 0, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_212 : summ (Enum.genFrom colR [[3, 1, 1, 0]] 8) = (0, 6, 12, 8, true) := by
  decide +kernel

theorem pref_213 : summ (Enum.genFrom colR [[3, 1, 1, 1]] 8) = (0, 8, 0, 0, true) := by
  decide +kernel

theorem pref_214 : summ (Enum.genFrom colR [[3, 1, 1, 2]] 8) = (0, 0, 4, 8, true) := by
  decide +kernel

theorem pref_215 : summ (Enum.genFrom colR [[3, 1, 1, 3]] 8) = (0, 0, 0, 16, true) := by
  decide +kernel

theorem pref_216 : summ (Enum.genFrom colR [[3, 1, 2, 0]] 8) = (0, 0, 2, 4, true) := by
  decide +kernel

theorem pref_217 : summ (Enum.genFrom colR [[3, 1, 2, 1]] 8) = (0, 0, 4, 4, true) := by
  decide +kernel

theorem pref_218 : summ (Enum.genFrom colR [[3, 1, 2, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_219 : summ (Enum.genFrom colR [[3, 1, 2, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_220 : summ (Enum.genFrom colR [[3, 1, 3, 0]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_221 : summ (Enum.genFrom colR [[3, 1, 3, 1]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_222 : summ (Enum.genFrom colR [[3, 1, 3, 2]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_223 : summ (Enum.genFrom colR [[3, 1, 3, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem part_6 : summ (Enum.genFrom colR L6 8) = (8, 32, 60, 144, true) := by
  simp only [L6, genFrom_cons2, summ_append, pref_192, pref_193, pref_194, pref_195, pref_196, pref_197, pref_198, pref_199, pref_200, pref_201, pref_202, pref_203, pref_204, pref_205, pref_206, pref_207, pref_208, pref_209, pref_210, pref_211, pref_212, pref_213, pref_214, pref_215, pref_216, pref_217, pref_218, pref_219, pref_220, pref_221, pref_222, pref_223]
  rfl

end OpenProblemsLab.ClawFree.Second
