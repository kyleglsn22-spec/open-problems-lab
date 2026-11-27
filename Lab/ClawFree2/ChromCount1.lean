import Lab.ClawFree2.ChromCount0

/-! Colouring counts of `G`, part 1 of 8 (see `ChromCount0`). -/

namespace OpenProblemsLab.ClawFree.Second

open MvPolynomial Finset OpenProblemsLab.ClawFree

theorem pref_32 : summ (Enum.genFrom colR [[0, 2, 0, 0]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_33 : summ (Enum.genFrom colR [[0, 2, 0, 1]] 8) = (0, 4, 6, 4, true) := by
  decide +kernel

theorem pref_34 : summ (Enum.genFrom colR [[0, 2, 0, 2]] 8) = (0, 0, 6, 8, true) := by
  decide +kernel

theorem pref_35 : summ (Enum.genFrom colR [[0, 2, 0, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_36 : summ (Enum.genFrom colR [[0, 2, 1, 0]] 8) = (0, 4, 6, 4, true) := by
  decide +kernel

theorem pref_37 : summ (Enum.genFrom colR [[0, 2, 1, 1]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_38 : summ (Enum.genFrom colR [[0, 2, 1, 2]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_39 : summ (Enum.genFrom colR [[0, 2, 1, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_40 : summ (Enum.genFrom colR [[0, 2, 2, 0]] 8) = (0, 0, 10, 16, true) := by
  decide +kernel

theorem pref_41 : summ (Enum.genFrom colR [[0, 2, 2, 1]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_42 : summ (Enum.genFrom colR [[0, 2, 2, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_43 : summ (Enum.genFrom colR [[0, 2, 2, 3]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_44 : summ (Enum.genFrom colR [[0, 2, 3, 0]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_45 : summ (Enum.genFrom colR [[0, 2, 3, 1]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_46 : summ (Enum.genFrom colR [[0, 2, 3, 2]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_47 : summ (Enum.genFrom colR [[0, 2, 3, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_48 : summ (Enum.genFrom colR [[0, 3, 0, 0]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_49 : summ (Enum.genFrom colR [[0, 3, 0, 1]] 8) = (0, 4, 6, 4, true) := by
  decide +kernel

theorem pref_50 : summ (Enum.genFrom colR [[0, 3, 0, 2]] 8) = (0, 0, 6, 4, true) := by
  decide +kernel

theorem pref_51 : summ (Enum.genFrom colR [[0, 3, 0, 3]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_52 : summ (Enum.genFrom colR [[0, 3, 1, 0]] 8) = (0, 4, 6, 4, true) := by
  decide +kernel

theorem pref_53 : summ (Enum.genFrom colR [[0, 3, 1, 1]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_54 : summ (Enum.genFrom colR [[0, 3, 1, 2]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_55 : summ (Enum.genFrom colR [[0, 3, 1, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_56 : summ (Enum.genFrom colR [[0, 3, 2, 0]] 8) = (0, 0, 6, 4, true) := by
  decide +kernel

theorem pref_57 : summ (Enum.genFrom colR [[0, 3, 2, 1]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_58 : summ (Enum.genFrom colR [[0, 3, 2, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_59 : summ (Enum.genFrom colR [[0, 3, 2, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_60 : summ (Enum.genFrom colR [[0, 3, 3, 0]] 8) = (0, 0, 0, 16, true) := by
  decide +kernel

theorem pref_61 : summ (Enum.genFrom colR [[0, 3, 3, 1]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_62 : summ (Enum.genFrom colR [[0, 3, 3, 2]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_63 : summ (Enum.genFrom colR [[0, 3, 3, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem part_1 : summ (Enum.genFrom colR L1 8) = (0, 16, 52, 144, true) := by
  simp only [L1, genFrom_cons2, summ_append, pref_32, pref_33, pref_34, pref_35, pref_36, pref_37, pref_38, pref_39, pref_40, pref_41, pref_42, pref_43, pref_44, pref_45, pref_46, pref_47, pref_48, pref_49, pref_50, pref_51, pref_52, pref_53, pref_54, pref_55, pref_56, pref_57, pref_58, pref_59, pref_60, pref_61, pref_62, pref_63]
  rfl

end OpenProblemsLab.ClawFree.Second
