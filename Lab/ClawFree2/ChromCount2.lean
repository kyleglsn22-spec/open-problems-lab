import Lab.ClawFree2.ChromCount1

/-! Colouring counts of `G`, part 2 of 8 (see `ChromCount0`). -/

namespace OpenProblemsLab.ClawFree.Second

open MvPolynomial Finset OpenProblemsLab.ClawFree

theorem pref_64 : summ (Enum.genFrom colR [[1, 0, 0, 0]] 8) = (8, 0, 12, 0, true) := by
  decide +kernel

theorem pref_65 : summ (Enum.genFrom colR [[1, 0, 0, 1]] 8) = (0, 12, 8, 16, true) := by
  decide +kernel

theorem pref_66 : summ (Enum.genFrom colR [[1, 0, 0, 2]] 8) = (0, 0, 10, 8, true) := by
  decide +kernel

theorem pref_67 : summ (Enum.genFrom colR [[1, 0, 0, 3]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_68 : summ (Enum.genFrom colR [[1, 0, 1, 0]] 8) = (0, 4, 4, 8, true) := by
  decide +kernel

theorem pref_69 : summ (Enum.genFrom colR [[1, 0, 1, 1]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_70 : summ (Enum.genFrom colR [[1, 0, 1, 2]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_71 : summ (Enum.genFrom colR [[1, 0, 1, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_72 : summ (Enum.genFrom colR [[1, 0, 2, 0]] 8) = (0, 0, 2, 4, true) := by
  decide +kernel

theorem pref_73 : summ (Enum.genFrom colR [[1, 0, 2, 1]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_74 : summ (Enum.genFrom colR [[1, 0, 2, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_75 : summ (Enum.genFrom colR [[1, 0, 2, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_76 : summ (Enum.genFrom colR [[1, 0, 3, 0]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_77 : summ (Enum.genFrom colR [[1, 0, 3, 1]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_78 : summ (Enum.genFrom colR [[1, 0, 3, 2]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_79 : summ (Enum.genFrom colR [[1, 0, 3, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_80 : summ (Enum.genFrom colR [[1, 1, 0, 0]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_81 : summ (Enum.genFrom colR [[1, 1, 0, 1]] 8) = (0, 0, 8, 8, true) := by
  decide +kernel

theorem pref_82 : summ (Enum.genFrom colR [[1, 1, 0, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_83 : summ (Enum.genFrom colR [[1, 1, 0, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_84 : summ (Enum.genFrom colR [[1, 1, 1, 0]] 8) = (0, 0, 8, 8, true) := by
  decide +kernel

theorem pref_85 : summ (Enum.genFrom colR [[1, 1, 1, 1]] 8) = (0, 8, 0, 0, true) := by
  decide +kernel

theorem pref_86 : summ (Enum.genFrom colR [[1, 1, 1, 2]] 8) = (0, 0, 4, 8, true) := by
  decide +kernel

theorem pref_87 : summ (Enum.genFrom colR [[1, 1, 1, 3]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_88 : summ (Enum.genFrom colR [[1, 1, 2, 0]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_89 : summ (Enum.genFrom colR [[1, 1, 2, 1]] 8) = (0, 0, 4, 8, true) := by
  decide +kernel

theorem pref_90 : summ (Enum.genFrom colR [[1, 1, 2, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_91 : summ (Enum.genFrom colR [[1, 1, 2, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_92 : summ (Enum.genFrom colR [[1, 1, 3, 0]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_93 : summ (Enum.genFrom colR [[1, 1, 3, 1]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_94 : summ (Enum.genFrom colR [[1, 1, 3, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_95 : summ (Enum.genFrom colR [[1, 1, 3, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem part_2 : summ (Enum.genFrom colR L2 8) = (8, 24, 60, 120, true) := by
  simp only [L2, genFrom_cons2, summ_append, pref_64, pref_65, pref_66, pref_67, pref_68, pref_69, pref_70, pref_71, pref_72, pref_73, pref_74, pref_75, pref_76, pref_77, pref_78, pref_79, pref_80, pref_81, pref_82, pref_83, pref_84, pref_85, pref_86, pref_87, pref_88, pref_89, pref_90, pref_91, pref_92, pref_93, pref_94, pref_95]
  rfl

end OpenProblemsLab.ClawFree.Second
