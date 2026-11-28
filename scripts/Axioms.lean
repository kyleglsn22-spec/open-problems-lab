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
#print axioms OpenProblemsLab.E757.LowerBound.nine_seventeenths_le_sSup_of_theorem6
#print axioms OpenProblemsLab.HY.theorem6
#print axioms OpenProblemsLab.E757.LowerBound.nine_seventeenths_le_sSup_unconditional
#print axioms OpenProblemsLab.E757.LowerBound.erdos_757_lowerBound
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
#print axioms OpenProblemsLab.ListTotal.not_totalChoosable_four
#print axioms OpenProblemsLab.ListTotal.totalChromaticNumber_G
#print axioms OpenProblemsLab.ListTotal.not_listTotalColouringConjecture
#print axioms OpenProblemsLab.ListTotal.exists_counterexample
#print axioms OpenProblemsLab.ListTotalGeneral.exists_counterexample
#print axioms OpenProblemsLab.ListTotalGeneral.totalChromaticNumber_G
#print axioms OpenProblemsLab.ListTotalGeneral.not_totalChoosable
#print axioms OpenProblemsLab.ListTotalGeneral.degree_le
#print axioms OpenProblemsLab.ListTotalGeneral.not_listTotalColouringConjecture
#print axioms OpenProblemsLab.GMR.counterexample
#print axioms OpenProblemsLab.GMR.not_nonAbelianGMR
#print axioms OpenProblemsLab.GMR.exists_counterexample_card
#print axioms OpenProblemsLab.ClawFree.Counterexample.not_clawFreeSchurPositivity
#print axioms OpenProblemsLab.ClawFree.Counterexample.not_schurPositive
#print axioms OpenProblemsLab.ClawFree.Counterexample.G_isClawFree
#print axioms OpenProblemsLab.PartialList.not_partialListColouringConjecture
#print axioms OpenProblemsLab.PartialList.listChromaticNumber_G
#print axioms OpenProblemsLab.PartialList.partial_le_nine
#print axioms OpenProblemsLab.PartialList.exists_counterexample
#print axioms OpenProblemsLab.PartialList.connected_gap
#print axioms OpenProblemsLab.PartialList.chain_connected
#print axioms OpenProblemsLab.PartialList.listChromaticNumber_chain
#print axioms OpenProblemsLab.PartialList.chain_partial_le
#print axioms OpenProblemsLab.ClawFree.Second.not_clawFreeSchurPositivity
#print axioms OpenProblemsLab.ClawFree.Second.not_schurPositive
#print axioms OpenProblemsLab.ClawFree.Second.G_isClawFree
#print axioms OpenProblemsLab.PartialList.General.not_partialListColouringConjecture_general
#print axioms OpenProblemsLab.PartialList.General.not_conjecture_of
#print axioms OpenProblemsLab.PartialList.General.listChromaticNumber_Gk
#print axioms OpenProblemsLab.PartialList.General.partial_violates
#print axioms OpenProblemsLab.BlockEquitable.not_gapOneConjecture
#print axioms OpenProblemsLab.BlockEquitable.exists_counterexample
#print axioms OpenProblemsLab.BlockEquitable.Family.lauri_family
#print axioms OpenProblemsLab.BlockEquitable.Family.gap_unbounded
#print axioms OpenProblemsLab.LocalAntimagic.not_leafConjecture
#print axioms OpenProblemsLab.LocalAntimagic.no_constant
#print axioms OpenProblemsLab.LocalAntimagic.family
#print axioms OpenProblemsLab.LocalAntimagic.T3
#print axioms OpenProblemsLab.LocalAntimagic.not_leafConjecture_T3
#print axioms OpenProblemsLab.FibWalk.nine_mem_up_not_down
#print axioms OpenProblemsLab.FibWalk.not_gapSet_conjecture
#print axioms OpenProblemsLab.FibWalk.nine_not_mem_down
#print axioms OpenProblemsLab.FibWalk.nine_mem_up
#print axioms OpenProblemsLab.FibWalk.exists_rep
#print axioms OpenProblemsLab.FibWalk.shift
#print axioms OpenProblemsLab.Bipanchromatic.not_conjecture
#print axioms OpenProblemsLab.Bipanchromatic.excess_unbounded
#print axioms OpenProblemsLab.Bipanchromatic.sunflower_parameters
#print axioms OpenProblemsLab.SpanningForests.not_conjecture
#print axioms OpenProblemsLab.SpanningForests.counterexample_for_every_a
#print axioms OpenProblemsLab.SpanningForests.card_le_numSpanningForests
#print axioms OpenProblemsLab.OddFoldCovers.not_conjecture
#print axioms OpenProblemsLab.OddFoldCovers.F_L
#print axioms OpenProblemsLab.OddFoldCovers.F_sCyc
#print axioms OpenProblemsLab.AlbertsonBerman.not_albertsonBermanConjecture
#print axioms OpenProblemsLab.AlbertsonBerman.card_le_of_isAcyclic
#print axioms OpenProblemsLab.AlbertsonBerman.straightLinePlanar_G
#print axioms OpenProblemsLab.Goemans.not_goemansConjecture
#print axioms OpenProblemsLab.Goemans.unsplittable_bad
#print axioms OpenProblemsLab.Unstable.not_mizziConjecture
#print axioms OpenProblemsLab.Unstable.G_unstable
