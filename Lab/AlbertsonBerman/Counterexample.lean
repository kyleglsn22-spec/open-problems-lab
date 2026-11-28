import Lab.AlbertsonBerman.Drawing

/-! Part of claim AB-1, see `Lab/AlbertsonBerman/Basic.lean`. -/

namespace OpenProblemsLab.AlbertsonBerman

open SimpleGraph

/-! ## Main result -/

/-- The Albertson–Berman conjecture, for straight-line planar graphs: every such graph on `n`
vertices has an induced forest on at least `n / 2` vertices. -/
def AlbertsonBermanConjecture : Prop :=
  ∀ (n : ℕ) (H : SimpleGraph (Fin n)), StraightLinePlanar H →
    ∃ S : Finset (Fin n), (H.induce (S : Set (Fin n))).IsAcyclic ∧ n ≤ 2 * S.card

/-- `G₂₉` is a counterexample: 29 vertices, straight-line planar, every induced forest has at most
14 vertices. Since a straight-line drawing is a planar drawing, the conjecture fails for planar
graphs in any usual sense. -/
theorem not_albertsonBermanConjecture : ¬ AlbertsonBermanConjecture := by
  intro h
  obtain ⟨S, hS, hcard⟩ := h 29 G straightLinePlanar_G
  have := card_le_of_isAcyclic S hS
  omega

end OpenProblemsLab.AlbertsonBerman
