import Lab.HenningYeo.Claim5

/-!
# Structure of the hypergraphs `H₁₀`, `H₁₀'`: facts about the templates (by `decide`)
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-- Valid parameters of the template. -/
def GValid (l : Fin 5) (a b : Fin 7) : Prop := a ∈ F7L l ∧ b ∈ F7L l ∧ a ≠ b

instance (l : Fin 5) (a b : Fin 7) : Decidable (GValid l a b) := by unfold GValid; infer_instance

/-! ### Template facts -/

end OpenProblemsLab.HY
