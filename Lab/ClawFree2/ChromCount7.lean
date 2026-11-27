import Lab.ClawFree2.ChromCount6

/-! Colouring counts of `G`, part 7 of 8 (see `ChromCount0`). -/

namespace OpenProblemsLab.ClawFree.Second

open MvPolynomial Finset OpenProblemsLab.ClawFree

theorem pref_224 : summ (Enum.genFrom colR [[3, 2, 0, 0]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_225 : summ (Enum.genFrom colR [[3, 2, 0, 1]] 8) = (0, 4, 2, 4, true) := by
  decide +kernel

theorem pref_226 : summ (Enum.genFrom colR [[3, 2, 0, 2]] 8) = (0, 0, 4, 4, true) := by
  decide +kernel

theorem pref_227 : summ (Enum.genFrom colR [[3, 2, 0, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_228 : summ (Enum.genFrom colR [[3, 2, 1, 0]] 8) = (0, 4, 2, 4, true) := by
  decide +kernel

theorem pref_229 : summ (Enum.genFrom colR [[3, 2, 1, 1]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_230 : summ (Enum.genFrom colR [[3, 2, 1, 2]] 8) = (0, 0, 4, 4, true) := by
  decide +kernel

theorem pref_231 : summ (Enum.genFrom colR [[3, 2, 1, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_232 : summ (Enum.genFrom colR [[3, 2, 2, 0]] 8) = (0, 0, 12, 8, true) := by
  decide +kernel

theorem pref_233 : summ (Enum.genFrom colR [[3, 2, 2, 1]] 8) = (0, 0, 4, 8, true) := by
  decide +kernel

theorem pref_234 : summ (Enum.genFrom colR [[3, 2, 2, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_235 : summ (Enum.genFrom colR [[3, 2, 2, 3]] 8) = (0, 0, 0, 16, true) := by
  decide +kernel

theorem pref_236 : summ (Enum.genFrom colR [[3, 2, 3, 0]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_237 : summ (Enum.genFrom colR [[3, 2, 3, 1]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_238 : summ (Enum.genFrom colR [[3, 2, 3, 2]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_239 : summ (Enum.genFrom colR [[3, 2, 3, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_240 : summ (Enum.genFrom colR [[3, 3, 0, 0]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_241 : summ (Enum.genFrom colR [[3, 3, 0, 1]] 8) = (0, 4, 4, 0, true) := by
  decide +kernel

theorem pref_242 : summ (Enum.genFrom colR [[3, 3, 0, 2]] 8) = (0, 0, 4, 0, true) := by
  decide +kernel

theorem pref_243 : summ (Enum.genFrom colR [[3, 3, 0, 3]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_244 : summ (Enum.genFrom colR [[3, 3, 1, 0]] 8) = (0, 4, 4, 0, true) := by
  decide +kernel

theorem pref_245 : summ (Enum.genFrom colR [[3, 3, 1, 1]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_246 : summ (Enum.genFrom colR [[3, 3, 1, 2]] 8) = (0, 0, 4, 0, true) := by
  decide +kernel

theorem pref_247 : summ (Enum.genFrom colR [[3, 3, 1, 3]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_248 : summ (Enum.genFrom colR [[3, 3, 2, 0]] 8) = (0, 0, 4, 0, true) := by
  decide +kernel

theorem pref_249 : summ (Enum.genFrom colR [[3, 3, 2, 1]] 8) = (0, 0, 4, 0, true) := by
  decide +kernel

theorem pref_250 : summ (Enum.genFrom colR [[3, 3, 2, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_251 : summ (Enum.genFrom colR [[3, 3, 2, 3]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_252 : summ (Enum.genFrom colR [[3, 3, 3, 0]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_253 : summ (Enum.genFrom colR [[3, 3, 3, 1]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_254 : summ (Enum.genFrom colR [[3, 3, 3, 2]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_255 : summ (Enum.genFrom colR [[3, 3, 3, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem part_7 : summ (Enum.genFrom colR L7 8) = (0, 16, 52, 120, true) := by
  simp only [L7, genFrom_cons2, summ_append, pref_224, pref_225, pref_226, pref_227, pref_228, pref_229, pref_230, pref_231, pref_232, pref_233, pref_234, pref_235, pref_236, pref_237, pref_238, pref_239, pref_240, pref_241, pref_242, pref_243, pref_244, pref_245, pref_246, pref_247, pref_248, pref_249, pref_250, pref_251, pref_252, pref_253, pref_254, pref_255]
  rfl

end OpenProblemsLab.ClawFree.Second
