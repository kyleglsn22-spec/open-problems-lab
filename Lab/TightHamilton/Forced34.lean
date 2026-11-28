import Lab.TightHamilton.Basic

/-! Ferudun's Lemma 2.4 (a forced complementary pair of windows) for k = 3 and 4, by the kernel. -/

namespace OpenProblemsLab.TightHamilton

open Finset

theorem forced3 : ForcedPair 3 := by unfold ForcedPair; decide +kernel
theorem forced4 : ForcedPair 4 := by unfold ForcedPair; decide +kernel

/-- Lemma 2.4 for `k = 5`, restricted to apex sets `{a} ∪ Q` with least element `a`. The cases
are split over several files to keep each kernel check below the CI memory limit. -/
def Forced5At (a : Fin 9) : Prop :=
  ∀ Q ∈ ((Finset.univ : Finset (Fin 9)).filter (a < ·)).powersetCard 2,
    ∃ i j : Fin 9, (idx 5 i \ insert a Q).card = 3 ∧ (idx 5 j \ insert a Q).card = 3 ∧
      Disjoint (idx 5 i \ insert a Q) (idx 5 j \ insert a Q)

end OpenProblemsLab.TightHamilton
