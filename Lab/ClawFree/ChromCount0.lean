import Lab.ClawFree.Graph

/-!
# Counting the proper 4-colourings of `G` by class sizes

The kernel enumerates the proper colourings with the verified backtracking list. To keep memory
low, the enumeration is split by the colours of the first 4 vertices: `gen4` lists the 84 valid
prefixes, and each `pref_i` handles the colourings extending one prefix in its own declaration.
`summ_gen` adds the pieces up.
-/

namespace OpenProblemsLab.ClawFree.Counterexample

open MvPolynomial Finset OpenProblemsLab.ClawFree

theorem gen4 : Enum.gen colR 4 = [
    [0, 1, 0, 1],
    [0, 1, 0, 2],
    [0, 1, 0, 3],
    [0, 1, 2, 1],
    [0, 1, 2, 3],
    [0, 1, 3, 1],
    [0, 1, 3, 2],
    [0, 2, 0, 1],
    [0, 2, 0, 2],
    [0, 2, 0, 3],
    [0, 2, 1, 2],
    [0, 2, 1, 3],
    [0, 2, 3, 1],
    [0, 2, 3, 2],
    [0, 3, 0, 1],
    [0, 3, 0, 2],
    [0, 3, 0, 3],
    [0, 3, 1, 2],
    [0, 3, 1, 3],
    [0, 3, 2, 1],
    [0, 3, 2, 3],
    [1, 0, 1, 0],
    [1, 0, 1, 2],
    [1, 0, 1, 3],
    [1, 0, 2, 0],
    [1, 0, 2, 3],
    [1, 0, 3, 0],
    [1, 0, 3, 2],
    [1, 2, 0, 2],
    [1, 2, 0, 3],
    [1, 2, 1, 0],
    [1, 2, 1, 2],
    [1, 2, 1, 3],
    [1, 2, 3, 0],
    [1, 2, 3, 2],
    [1, 3, 0, 2],
    [1, 3, 0, 3],
    [1, 3, 1, 0],
    [1, 3, 1, 2],
    [1, 3, 1, 3],
    [1, 3, 2, 0],
    [1, 3, 2, 3],
    [2, 0, 1, 0],
    [2, 0, 1, 3],
    [2, 0, 2, 0],
    [2, 0, 2, 1],
    [2, 0, 2, 3],
    [2, 0, 3, 0],
    [2, 0, 3, 1],
    [2, 1, 0, 1],
    [2, 1, 0, 3],
    [2, 1, 2, 0],
    [2, 1, 2, 1],
    [2, 1, 2, 3],
    [2, 1, 3, 0],
    [2, 1, 3, 1],
    [2, 3, 0, 1],
    [2, 3, 0, 3],
    [2, 3, 1, 0],
    [2, 3, 1, 3],
    [2, 3, 2, 0],
    [2, 3, 2, 1],
    [2, 3, 2, 3],
    [3, 0, 1, 0],
    [3, 0, 1, 2],
    [3, 0, 2, 0],
    [3, 0, 2, 1],
    [3, 0, 3, 0],
    [3, 0, 3, 1],
    [3, 0, 3, 2],
    [3, 1, 0, 1],
    [3, 1, 0, 2],
    [3, 1, 2, 0],
    [3, 1, 2, 1],
    [3, 1, 3, 0],
    [3, 1, 3, 1],
    [3, 1, 3, 2],
    [3, 2, 0, 1],
    [3, 2, 0, 2],
    [3, 2, 1, 0],
    [3, 2, 1, 2],
    [3, 2, 3, 0],
    [3, 2, 3, 1],
    [3, 2, 3, 2]] := by
  decide +kernel

theorem pref_0 : summ (Enum.genFrom colR [[0, 1, 0, 1]] 8) = (0, 0, 16, true) := by
  decide +kernel

theorem pref_1 : summ (Enum.genFrom colR [[0, 1, 0, 2]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_2 : summ (Enum.genFrom colR [[0, 1, 0, 3]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_3 : summ (Enum.genFrom colR [[0, 1, 2, 1]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_4 : summ (Enum.genFrom colR [[0, 1, 2, 3]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_5 : summ (Enum.genFrom colR [[0, 1, 3, 1]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_6 : summ (Enum.genFrom colR [[0, 1, 3, 2]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_7 : summ (Enum.genFrom colR [[0, 2, 0, 1]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_8 : summ (Enum.genFrom colR [[0, 2, 0, 2]] 8) = (4, 0, 16, true) := by
  decide +kernel

theorem pref_9 : summ (Enum.genFrom colR [[0, 2, 0, 3]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_10 : summ (Enum.genFrom colR [[0, 2, 1, 2]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_11 : summ (Enum.genFrom colR [[0, 2, 1, 3]] 8) = (4, 4, 8, true) := by
  decide +kernel

theorem pref_12 : summ (Enum.genFrom colR [[0, 2, 3, 1]] 8) = (0, 4, 8, true) := by
  decide +kernel

theorem pref_13 : summ (Enum.genFrom colR [[0, 2, 3, 2]] 8) = (0, 4, 8, true) := by
  decide +kernel

end OpenProblemsLab.ClawFree.Counterexample
