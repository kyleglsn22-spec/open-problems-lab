import Lab.ClawFree2.Graph

/-!
# Counting the proper 4-colourings of `G` by class sizes

As in `Lab/ClawFree/ChromCount0.lean`: the kernel enumerates the proper colourings with the verified
backtracking list, split by the colours of the first 4 vertices (`gen4` lists the 256 valid
prefixes in 8 parts `L0 … L7`; each `pref_i` handles one prefix in its own declaration, and
`part_c` adds up part `c`). `summ_gen` in `ChromCount` adds the parts up.
-/

namespace OpenProblemsLab.ClawFree.Second

open MvPolynomial Finset OpenProblemsLab.ClawFree

/-- Prefixes handled in part 0. -/
def L0 : List (List (Fin 4)) := [
    [0, 0, 0, 0],
    [0, 0, 0, 1],
    [0, 0, 0, 2],
    [0, 0, 0, 3],
    [0, 0, 1, 0],
    [0, 0, 1, 1],
    [0, 0, 1, 2],
    [0, 0, 1, 3],
    [0, 0, 2, 0],
    [0, 0, 2, 1],
    [0, 0, 2, 2],
    [0, 0, 2, 3],
    [0, 0, 3, 0],
    [0, 0, 3, 1],
    [0, 0, 3, 2],
    [0, 0, 3, 3],
    [0, 1, 0, 0],
    [0, 1, 0, 1],
    [0, 1, 0, 2],
    [0, 1, 0, 3],
    [0, 1, 1, 0],
    [0, 1, 1, 1],
    [0, 1, 1, 2],
    [0, 1, 1, 3],
    [0, 1, 2, 0],
    [0, 1, 2, 1],
    [0, 1, 2, 2],
    [0, 1, 2, 3],
    [0, 1, 3, 0],
    [0, 1, 3, 1],
    [0, 1, 3, 2],
    [0, 1, 3, 3]]

/-- Prefixes handled in part 1. -/
def L1 : List (List (Fin 4)) := [
    [0, 2, 0, 0],
    [0, 2, 0, 1],
    [0, 2, 0, 2],
    [0, 2, 0, 3],
    [0, 2, 1, 0],
    [0, 2, 1, 1],
    [0, 2, 1, 2],
    [0, 2, 1, 3],
    [0, 2, 2, 0],
    [0, 2, 2, 1],
    [0, 2, 2, 2],
    [0, 2, 2, 3],
    [0, 2, 3, 0],
    [0, 2, 3, 1],
    [0, 2, 3, 2],
    [0, 2, 3, 3],
    [0, 3, 0, 0],
    [0, 3, 0, 1],
    [0, 3, 0, 2],
    [0, 3, 0, 3],
    [0, 3, 1, 0],
    [0, 3, 1, 1],
    [0, 3, 1, 2],
    [0, 3, 1, 3],
    [0, 3, 2, 0],
    [0, 3, 2, 1],
    [0, 3, 2, 2],
    [0, 3, 2, 3],
    [0, 3, 3, 0],
    [0, 3, 3, 1],
    [0, 3, 3, 2],
    [0, 3, 3, 3]]

/-- Prefixes handled in part 2. -/
def L2 : List (List (Fin 4)) := [
    [1, 0, 0, 0],
    [1, 0, 0, 1],
    [1, 0, 0, 2],
    [1, 0, 0, 3],
    [1, 0, 1, 0],
    [1, 0, 1, 1],
    [1, 0, 1, 2],
    [1, 0, 1, 3],
    [1, 0, 2, 0],
    [1, 0, 2, 1],
    [1, 0, 2, 2],
    [1, 0, 2, 3],
    [1, 0, 3, 0],
    [1, 0, 3, 1],
    [1, 0, 3, 2],
    [1, 0, 3, 3],
    [1, 1, 0, 0],
    [1, 1, 0, 1],
    [1, 1, 0, 2],
    [1, 1, 0, 3],
    [1, 1, 1, 0],
    [1, 1, 1, 1],
    [1, 1, 1, 2],
    [1, 1, 1, 3],
    [1, 1, 2, 0],
    [1, 1, 2, 1],
    [1, 1, 2, 2],
    [1, 1, 2, 3],
    [1, 1, 3, 0],
    [1, 1, 3, 1],
    [1, 1, 3, 2],
    [1, 1, 3, 3]]

/-- Prefixes handled in part 3. -/
def L3 : List (List (Fin 4)) := [
    [1, 2, 0, 0],
    [1, 2, 0, 1],
    [1, 2, 0, 2],
    [1, 2, 0, 3],
    [1, 2, 1, 0],
    [1, 2, 1, 1],
    [1, 2, 1, 2],
    [1, 2, 1, 3],
    [1, 2, 2, 0],
    [1, 2, 2, 1],
    [1, 2, 2, 2],
    [1, 2, 2, 3],
    [1, 2, 3, 0],
    [1, 2, 3, 1],
    [1, 2, 3, 2],
    [1, 2, 3, 3],
    [1, 3, 0, 0],
    [1, 3, 0, 1],
    [1, 3, 0, 2],
    [1, 3, 0, 3],
    [1, 3, 1, 0],
    [1, 3, 1, 1],
    [1, 3, 1, 2],
    [1, 3, 1, 3],
    [1, 3, 2, 0],
    [1, 3, 2, 1],
    [1, 3, 2, 2],
    [1, 3, 2, 3],
    [1, 3, 3, 0],
    [1, 3, 3, 1],
    [1, 3, 3, 2],
    [1, 3, 3, 3]]

/-- Prefixes handled in part 4. -/
def L4 : List (List (Fin 4)) := [
    [2, 0, 0, 0],
    [2, 0, 0, 1],
    [2, 0, 0, 2],
    [2, 0, 0, 3],
    [2, 0, 1, 0],
    [2, 0, 1, 1],
    [2, 0, 1, 2],
    [2, 0, 1, 3],
    [2, 0, 2, 0],
    [2, 0, 2, 1],
    [2, 0, 2, 2],
    [2, 0, 2, 3],
    [2, 0, 3, 0],
    [2, 0, 3, 1],
    [2, 0, 3, 2],
    [2, 0, 3, 3],
    [2, 1, 0, 0],
    [2, 1, 0, 1],
    [2, 1, 0, 2],
    [2, 1, 0, 3],
    [2, 1, 1, 0],
    [2, 1, 1, 1],
    [2, 1, 1, 2],
    [2, 1, 1, 3],
    [2, 1, 2, 0],
    [2, 1, 2, 1],
    [2, 1, 2, 2],
    [2, 1, 2, 3],
    [2, 1, 3, 0],
    [2, 1, 3, 1],
    [2, 1, 3, 2],
    [2, 1, 3, 3]]

/-- Prefixes handled in part 5. -/
def L5 : List (List (Fin 4)) := [
    [2, 2, 0, 0],
    [2, 2, 0, 1],
    [2, 2, 0, 2],
    [2, 2, 0, 3],
    [2, 2, 1, 0],
    [2, 2, 1, 1],
    [2, 2, 1, 2],
    [2, 2, 1, 3],
    [2, 2, 2, 0],
    [2, 2, 2, 1],
    [2, 2, 2, 2],
    [2, 2, 2, 3],
    [2, 2, 3, 0],
    [2, 2, 3, 1],
    [2, 2, 3, 2],
    [2, 2, 3, 3],
    [2, 3, 0, 0],
    [2, 3, 0, 1],
    [2, 3, 0, 2],
    [2, 3, 0, 3],
    [2, 3, 1, 0],
    [2, 3, 1, 1],
    [2, 3, 1, 2],
    [2, 3, 1, 3],
    [2, 3, 2, 0],
    [2, 3, 2, 1],
    [2, 3, 2, 2],
    [2, 3, 2, 3],
    [2, 3, 3, 0],
    [2, 3, 3, 1],
    [2, 3, 3, 2],
    [2, 3, 3, 3]]

/-- Prefixes handled in part 6. -/
def L6 : List (List (Fin 4)) := [
    [3, 0, 0, 0],
    [3, 0, 0, 1],
    [3, 0, 0, 2],
    [3, 0, 0, 3],
    [3, 0, 1, 0],
    [3, 0, 1, 1],
    [3, 0, 1, 2],
    [3, 0, 1, 3],
    [3, 0, 2, 0],
    [3, 0, 2, 1],
    [3, 0, 2, 2],
    [3, 0, 2, 3],
    [3, 0, 3, 0],
    [3, 0, 3, 1],
    [3, 0, 3, 2],
    [3, 0, 3, 3],
    [3, 1, 0, 0],
    [3, 1, 0, 1],
    [3, 1, 0, 2],
    [3, 1, 0, 3],
    [3, 1, 1, 0],
    [3, 1, 1, 1],
    [3, 1, 1, 2],
    [3, 1, 1, 3],
    [3, 1, 2, 0],
    [3, 1, 2, 1],
    [3, 1, 2, 2],
    [3, 1, 2, 3],
    [3, 1, 3, 0],
    [3, 1, 3, 1],
    [3, 1, 3, 2],
    [3, 1, 3, 3]]

/-- Prefixes handled in part 7. -/
def L7 : List (List (Fin 4)) := [
    [3, 2, 0, 0],
    [3, 2, 0, 1],
    [3, 2, 0, 2],
    [3, 2, 0, 3],
    [3, 2, 1, 0],
    [3, 2, 1, 1],
    [3, 2, 1, 2],
    [3, 2, 1, 3],
    [3, 2, 2, 0],
    [3, 2, 2, 1],
    [3, 2, 2, 2],
    [3, 2, 2, 3],
    [3, 2, 3, 0],
    [3, 2, 3, 1],
    [3, 2, 3, 2],
    [3, 2, 3, 3],
    [3, 3, 0, 0],
    [3, 3, 0, 1],
    [3, 3, 0, 2],
    [3, 3, 0, 3],
    [3, 3, 1, 0],
    [3, 3, 1, 1],
    [3, 3, 1, 2],
    [3, 3, 1, 3],
    [3, 3, 2, 0],
    [3, 3, 2, 1],
    [3, 3, 2, 2],
    [3, 3, 2, 3],
    [3, 3, 3, 0],
    [3, 3, 3, 1],
    [3, 3, 3, 2],
    [3, 3, 3, 3]]

theorem gen4 : Enum.gen colR 4 = L0 ++ L1 ++ L2 ++ L3 ++ L4 ++ L5 ++ L6 ++ L7 := by
  decide +kernel

theorem genFrom_cons2 (p q : List (Fin 4)) (L : List (List (Fin 4))) (j : ℕ) :
    Enum.genFrom colR (p :: q :: L) j = Enum.genFrom colR [p] j ++ Enum.genFrom colR (q :: L) j :=
  Enum.genFrom_cons colR p (q :: L) j

theorem pref_0 : summ (Enum.genFrom colR [[0, 0, 0, 0]] 8) = (0, 8, 24, 0, true) := by
  decide +kernel

theorem pref_1 : summ (Enum.genFrom colR [[0, 0, 0, 1]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_2 : summ (Enum.genFrom colR [[0, 0, 0, 2]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_3 : summ (Enum.genFrom colR [[0, 0, 0, 3]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_4 : summ (Enum.genFrom colR [[0, 0, 1, 0]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_5 : summ (Enum.genFrom colR [[0, 0, 1, 1]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_6 : summ (Enum.genFrom colR [[0, 0, 1, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_7 : summ (Enum.genFrom colR [[0, 0, 1, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_8 : summ (Enum.genFrom colR [[0, 0, 2, 0]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_9 : summ (Enum.genFrom colR [[0, 0, 2, 1]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_10 : summ (Enum.genFrom colR [[0, 0, 2, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_11 : summ (Enum.genFrom colR [[0, 0, 2, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_12 : summ (Enum.genFrom colR [[0, 0, 3, 0]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_13 : summ (Enum.genFrom colR [[0, 0, 3, 1]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_14 : summ (Enum.genFrom colR [[0, 0, 3, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_15 : summ (Enum.genFrom colR [[0, 0, 3, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_16 : summ (Enum.genFrom colR [[0, 1, 0, 0]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_17 : summ (Enum.genFrom colR [[0, 1, 0, 1]] 8) = (0, 4, 6, 8, true) := by
  decide +kernel

theorem pref_18 : summ (Enum.genFrom colR [[0, 1, 0, 2]] 8) = (0, 0, 6, 4, true) := by
  decide +kernel

theorem pref_19 : summ (Enum.genFrom colR [[0, 1, 0, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_20 : summ (Enum.genFrom colR [[0, 1, 1, 0]] 8) = (0, 12, 10, 16, true) := by
  decide +kernel

theorem pref_21 : summ (Enum.genFrom colR [[0, 1, 1, 1]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_22 : summ (Enum.genFrom colR [[0, 1, 1, 2]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_23 : summ (Enum.genFrom colR [[0, 1, 1, 3]] 8) = (0, 0, 0, 8, true) := by
  decide +kernel

theorem pref_24 : summ (Enum.genFrom colR [[0, 1, 2, 0]] 8) = (0, 0, 6, 4, true) := by
  decide +kernel

theorem pref_25 : summ (Enum.genFrom colR [[0, 1, 2, 1]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_26 : summ (Enum.genFrom colR [[0, 1, 2, 2]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem pref_27 : summ (Enum.genFrom colR [[0, 1, 2, 3]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_28 : summ (Enum.genFrom colR [[0, 1, 3, 0]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_29 : summ (Enum.genFrom colR [[0, 1, 3, 1]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_30 : summ (Enum.genFrom colR [[0, 1, 3, 2]] 8) = (0, 0, 0, 4, true) := by
  decide +kernel

theorem pref_31 : summ (Enum.genFrom colR [[0, 1, 3, 3]] 8) = (0, 0, 0, 0, true) := by
  decide +kernel

theorem part_0 : summ (Enum.genFrom colR L0 8) = (0, 24, 52, 120, true) := by
  simp only [L0, genFrom_cons2, summ_append, pref_0, pref_1, pref_2, pref_3, pref_4, pref_5, pref_6, pref_7, pref_8, pref_9, pref_10, pref_11, pref_12, pref_13, pref_14, pref_15, pref_16, pref_17, pref_18, pref_19, pref_20, pref_21, pref_22, pref_23, pref_24, pref_25, pref_26, pref_27, pref_28, pref_29, pref_30, pref_31]
  rfl

end OpenProblemsLab.ClawFree.Second
