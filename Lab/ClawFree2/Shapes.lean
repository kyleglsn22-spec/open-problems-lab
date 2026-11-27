import Lab.ClawFree2.ChromCount
import Lab.ClawFree.Shapes

/-!
# The four shapes `5322`, `4422`, `4332`, `3333` and their Kostka numbers

Uses the cell-listing tools of `Lab/ClawFree/Shapes.lean` (`cellsOf`, `coeff_shape`).
-/

namespace OpenProblemsLab.ClawFree.Second

open MvPolynomial Finset OpenProblemsLab.ClawFree
open OpenProblemsLab.ClawFree.Counterexample (cellsOf coeff_shape mem_ofRowLens_iff)

/-- Shapes `(5,3,2,2)`, `(4,4,2,2)`, `(4,3,3,2)`, `(3,3,3,3)`. -/
def D0 : YoungDiagram := YoungDiagram.ofRowLens [5, 3, 2, 2] (by decide)
def D1 : YoungDiagram := YoungDiagram.ofRowLens [4, 4, 2, 2] (by decide)
def D2 : YoungDiagram := YoungDiagram.ofRowLens [4, 3, 3, 2] (by decide)
def D3 : YoungDiagram := YoungDiagram.ofRowLens [3, 3, 3, 3] (by decide)

/-- `K_{μ,α}` for `μ` one of `D0, …, D3`. -/
theorem kostka (w : List ℕ) (hw : w.SortedGE) (α : Fin 4 →₀ ℕ) (v : Fin 4 → ℕ)
    (hv : ∀ i, α i = v i)
    (h : w = [5, 3, 2, 2] ∨ w = [4, 4, 2, 2] ∨ w = [4, 3, 3, 2] ∨ w = [3, 3, 3, 3]) :
    coeff α (schurPoly 4 (YoungDiagram.ofRowLens w hw)) =
      (((Enum.gen (fun a b x y => ssytRule ((cellsOf w).getD a (0, 0))
          ((cellsOf w).getD b (0, 0)) x y) 12).filter
        fun l => (List.finRange 4).all fun i => l.count i == v i).length : ℤ) := by
  apply coeff_shape w hw 12 _ _ _ _ _ α v hv <;>
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem K00 : coeff e5322 (schurPoly 4 D0) = 1 := by
  rw [D0, kostka _ _ _ ![5, 3, 2, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K01 : coeff e4422 (schurPoly 4 D0) = 1 := by
  rw [D0, kostka _ _ _ ![4, 4, 2, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K02 : coeff e4332 (schurPoly 4 D0) = 2 := by
  rw [D0, kostka _ _ _ ![4, 3, 3, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K03 : coeff e3333 (schurPoly 4 D0) = 3 := by
  rw [D0, kostka _ _ _ ![3, 3, 3, 3] (fun _ => rfl) (by simp)]; decide +kernel
theorem K10 : coeff e5322 (schurPoly 4 D1) = 0 := by
  rw [D1, kostka _ _ _ ![5, 3, 2, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K11 : coeff e4422 (schurPoly 4 D1) = 1 := by
  rw [D1, kostka _ _ _ ![4, 4, 2, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K12 : coeff e4332 (schurPoly 4 D1) = 1 := by
  rw [D1, kostka _ _ _ ![4, 3, 3, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K13 : coeff e3333 (schurPoly 4 D1) = 2 := by
  rw [D1, kostka _ _ _ ![3, 3, 3, 3] (fun _ => rfl) (by simp)]; decide +kernel
theorem K20 : coeff e5322 (schurPoly 4 D2) = 0 := by
  rw [D2, kostka _ _ _ ![5, 3, 2, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K21 : coeff e4422 (schurPoly 4 D2) = 0 := by
  rw [D2, kostka _ _ _ ![4, 4, 2, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K22 : coeff e4332 (schurPoly 4 D2) = 1 := by
  rw [D2, kostka _ _ _ ![4, 3, 3, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K23 : coeff e3333 (schurPoly 4 D2) = 3 := by
  rw [D2, kostka _ _ _ ![3, 3, 3, 3] (fun _ => rfl) (by simp)]; decide +kernel
theorem K30 : coeff e5322 (schurPoly 4 D3) = 0 := by
  rw [D3, kostka _ _ _ ![5, 3, 2, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K31 : coeff e4422 (schurPoly 4 D3) = 0 := by
  rw [D3, kostka _ _ _ ![4, 4, 2, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K32 : coeff e4332 (schurPoly 4 D3) = 0 := by
  rw [D3, kostka _ _ _ ![4, 3, 3, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K33 : coeff e3333 (schurPoly 4 D3) = 1 := by
  rw [D3, kostka _ _ _ ![3, 3, 3, 3] (fun _ => rfl) (by simp)]; decide +kernel

end OpenProblemsLab.ClawFree.Second
