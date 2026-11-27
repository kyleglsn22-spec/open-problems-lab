import Lab.ClawFree.ChromCount

/-!
# The three shapes `4422`, `4332`, `3333` and their Kostka numbers
-/

namespace OpenProblemsLab.ClawFree.Counterexample

open MvPolynomial Finset OpenProblemsLab.ClawFree

/-! ### The three Young diagrams -/

theorem mem_ofRowLens_iff {w : List ℕ} {hw : w.SortedGE} {c : ℕ × ℕ} :
    c ∈ YoungDiagram.ofRowLens w hw ↔ c.2 < w.getD c.1 0 := by
  rw [YoungDiagram.mem_ofRowLens]
  constructor
  · rintro ⟨h, h'⟩; rwa [List.getD_eq_getElem _ _ h]
  · intro h
    by_cases h1 : c.1 < w.length
    · exact ⟨h1, by rwa [List.getD_eq_getElem _ _ h1] at h⟩
    · rw [List.getD_eq_default _ _ (not_lt.mp h1)] at h; omega

/-- Shapes `(4,4,2,2)`, `(4,3,3,2)`, `(3,3,3,3)`. -/
def D1 : YoungDiagram := YoungDiagram.ofRowLens [4, 4, 2, 2] (by decide)
def D2 : YoungDiagram := YoungDiagram.ofRowLens [4, 3, 3, 2] (by decide)
def D3 : YoungDiagram := YoungDiagram.ofRowLens [3, 3, 3, 3] (by decide)

/-- Row-major list of the cells of the shape `w`. -/
def cellsOf (w : List ℕ) : List (ℕ × ℕ) :=
  (List.range w.length).flatMap fun i => (List.range (w.getD i 0)).map fun j => (i, j)

/-- An explicit bijection `Fin m ≃ cells` from a row-major cell list, given decidable checks. -/
noncomputable def cellEquiv (w : List ℕ) (hw : w.SortedGE) (m : ℕ)
    (hmem : ∀ i : Fin m, ((cellsOf w).getD i (0, 0)).2 < w.getD ((cellsOf w).getD i (0, 0)).1 0)
    (hinj : ∀ a b : Fin m, (cellsOf w).getD a (0, 0) = (cellsOf w).getD b (0, 0) → a = b)
    (hsurj : ∀ x < w.length, ∀ y < w.getD x 0, ∃ i : Fin m, (cellsOf w).getD i (0, 0) = (x, y)) :
    Fin m ≃ (YoungDiagram.ofRowLens w hw).cells :=
  Equiv.ofBijective
    (fun i => ⟨(cellsOf w).getD i (0, 0), (YoungDiagram.mem_cells _).mpr
      (mem_ofRowLens_iff.mpr (hmem i))⟩)
    ⟨fun a b h => hinj a b (congrArg Subtype.val h), fun c => by
      have hc := mem_ofRowLens_iff.mp ((YoungDiagram.mem_cells _).mp c.2)
      have hx : c.1.1 < w.length := by
        by_contra hx
        rw [List.getD_eq_default _ _ (not_lt.mp hx)] at hc; omega
      obtain ⟨i, hi⟩ := hsurj c.1.1 hx c.1.2 hc
      exact ⟨i, Subtype.ext hi⟩⟩

/-- Kostka numbers of a shape, with all side conditions checked by `decide`. -/
theorem coeff_shape (w : List ℕ) (hw : w.SortedGE) (m : ℕ)
    (hmem : ∀ i : Fin m, ((cellsOf w).getD i (0, 0)).2 < w.getD ((cellsOf w).getD i (0, 0)).1 0)
    (hinj : ∀ a b : Fin m, (cellsOf w).getD a (0, 0) = (cellsOf w).getD b (0, 0) → a = b)
    (hsurj : ∀ x < w.length, ∀ y < w.getD x 0, ∃ i : Fin m, (cellsOf w).getD i (0, 0) = (x, y))
    (F1 : ∀ a b : Fin m, a < b → ((cellsOf w).getD a (0, 0)).1 = ((cellsOf w).getD b (0, 0)).1 →
      ((cellsOf w).getD a (0, 0)).2 ≤ ((cellsOf w).getD b (0, 0)).2)
    (F2 : ∀ a b : Fin m, a < b → ((cellsOf w).getD a (0, 0)).2 = ((cellsOf w).getD b (0, 0)).2 →
      ((cellsOf w).getD a (0, 0)).1 < ((cellsOf w).getD b (0, 0)).1)
    (α : Fin 4 →₀ ℕ) (v : Fin 4 → ℕ) (hv : ∀ i, α i = v i) :
    coeff α (schurPoly 4 (YoungDiagram.ofRowLens w hw)) =
      (((Enum.gen (fun a b x y => ssytRule ((cellsOf w).getD a (0, 0))
          ((cellsOf w).getD b (0, 0)) x y) m).filter
        fun l => (List.finRange 4).all fun i => l.count i == v i).length : ℤ) :=
  coeff_schurPoly_eq_gen _ (fun i => (cellsOf w).getD i (0, 0))
    (cellEquiv w hw m hmem hinj hsurj) (fun _ => rfl) F1 F2 α v hv

/-- `K_{μ,α}` for `μ` one of `D1, D2, D3`. -/
theorem kostka (w : List ℕ) (hw : w.SortedGE) (α : Fin 4 →₀ ℕ) (v : Fin 4 → ℕ)
    (hv : ∀ i, α i = v i) (h : w = [4, 4, 2, 2] ∨ w = [4, 3, 3, 2] ∨ w = [3, 3, 3, 3]) :
    coeff α (schurPoly 4 (YoungDiagram.ofRowLens w hw)) =
      (((Enum.gen (fun a b x y => ssytRule ((cellsOf w).getD a (0, 0))
          ((cellsOf w).getD b (0, 0)) x y) 12).filter
        fun l => (List.finRange 4).all fun i => l.count i == v i).length : ℤ) := by
  apply coeff_shape w hw 12 _ _ _ _ _ α v hv <;>
  rcases h with rfl | rfl | rfl <;> decide

theorem K11 : coeff e4422 (schurPoly 4 D1) = 1 := by
  rw [D1, kostka _ _ _ ![4, 4, 2, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K12 : coeff e4332 (schurPoly 4 D1) = 1 := by
  rw [D1, kostka _ _ _ ![4, 3, 3, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K13 : coeff e3333 (schurPoly 4 D1) = 2 := by
  rw [D1, kostka _ _ _ ![3, 3, 3, 3] (fun _ => rfl) (by simp)]; decide +kernel
theorem K21 : coeff e4422 (schurPoly 4 D2) = 0 := by
  rw [D2, kostka _ _ _ ![4, 4, 2, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K22 : coeff e4332 (schurPoly 4 D2) = 1 := by
  rw [D2, kostka _ _ _ ![4, 3, 3, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K23 : coeff e3333 (schurPoly 4 D2) = 3 := by
  rw [D2, kostka _ _ _ ![3, 3, 3, 3] (fun _ => rfl) (by simp)]; decide +kernel
theorem K31 : coeff e4422 (schurPoly 4 D3) = 0 := by
  rw [D3, kostka _ _ _ ![4, 4, 2, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K32 : coeff e4332 (schurPoly 4 D3) = 0 := by
  rw [D3, kostka _ _ _ ![4, 3, 3, 2] (fun _ => rfl) (by simp)]; decide +kernel
theorem K33 : coeff e3333 (schurPoly 4 D3) = 1 := by
  rw [D3, kostka _ _ _ ![3, 3, 3, 3] (fun _ => rfl) (by simp)]; decide +kernel


end OpenProblemsLab.ClawFree.Counterexample
