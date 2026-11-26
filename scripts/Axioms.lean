import Lab

/-!
Axiom audit. CI runs `lake env lean scripts/Axioms.lean` and fails if any theorem listed
here depends on anything other than `propext`, `Classical.choice` and `Quot.sound`.
`sorryAx` (an unfinished proof) and `Lean.ofReduceBool` (from `native_decide`) both fail.

Add a `#print axioms` line for every theorem the ledger marks as checked.
-/

#print axioms OpenProblemsLab.E757.upperBound
#print axioms OpenProblemsLab.E757.erdos_757_upperBound
#print axioms OpenProblemsLab.C37.no_degree4_sensitivity10
#print axioms OpenProblemsLab.E757.FourSevenths.sSup_le_four_sevenths
#print axioms OpenProblemsLab.E757.LowerBound.isAdmissible_nine_seventeenths
#print axioms OpenProblemsLab.E757.LowerBound.nine_seventeenths_le_sSup
#print axioms OpenProblemsLab.E757.LowerBound.erdos_757_lowerBound_of_henningYeo
#print axioms OpenProblemsLab.E757.LowerBound.apEdges_F7Free
#print axioms OpenProblemsLab.E757.LowerBound.apEdges_linear
#print axioms OpenProblemsLab.E757.FiveNinths.sSup_le_five_ninths
#print axioms OpenProblemsLab.C44.exists_degLE_all_relevant
#print axioms OpenProblemsLab.C44.three_halves_le
#print axioms OpenProblemsLab.Davenport.zeroSumFree_S
#print axioms OpenProblemsLab.Davenport.exists_zeroSumFree_C6_15
#print axioms OpenProblemsLab.Davenport.not_vanEmdeBoasKruyswijk
#print axioms OpenProblemsLab.Davenport.Family.ggwz
#print axioms OpenProblemsLab.Davenport.Family.vEBK_fails
#print axioms OpenProblemsLab.Davenport.Family.exists_zeroSumFree_family
#print axioms OpenProblemsLab.Davenport.Floor.ggwz_floor
#print axioms OpenProblemsLab.Davenport.Floor.ggwz_floor'
#print axioms OpenProblemsLab.Davenport.Floor.replace
