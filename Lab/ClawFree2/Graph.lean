import Lab.ClawFree.Tools
import Lab.ClawFree.Enum

/-!
# The second minimal counterexample: the graph and its colourings

See `Lab/ClawFree2/Counterexample.lean` for the overview. Here: the graph (given by its edge list,
from the graph6 code ``K?`CR@`bAbRB``), its claw-freeness, and the reduction of monomial
coefficients of `X_G` to counting lists of colourings (the same method as `Lab/ClawFree/Graph.lean`).
-/

namespace OpenProblemsLab.ClawFree.Second

open MvPolynomial Finset OpenProblemsLab.ClawFree

/-! ### The graph -/

/-- The 21 edges of `G` on the vertices `0 … 11`. -/
def edgesG : List (ℕ × ℕ) :=
  [(0, 4), (0, 6), (0, 9), (0, 11), (1, 5), (1, 7), (1, 8), (1, 10), (2, 7), (2, 8), (3, 10), (3, 11), (4, 6), (4, 9), (4, 11), (5, 9), (7, 8), (7, 10), (8, 10), (9, 11), (10, 11)]

/-- Adjacency: `i ~ j` iff `(i, j)` or `(j, i)` is an edge. -/
def adjN (i j : ℕ) : Bool := edgesG.contains (i, j) || edgesG.contains (j, i)

theorem adjN_symm : ∀ i j : Fin 12, adjN i j = true → adjN j i = true := by decide

theorem adjN_irrefl : ∀ i : Fin 12, adjN i i = false := by decide

/-- The graph `G` on vertex set `Fin 12`. -/
def G : SimpleGraph (Fin 12) where
  Adj i j := adjN i j = true
  symm := ⟨fun i j h => adjN_symm i j h⟩
  loopless := ⟨fun i h => by simp [adjN_irrefl i] at h⟩

theorem G_adj {i j : Fin 12} : G.Adj i j ↔ adjN i j = true := Iff.rfl

instance : DecidableRel G.Adj := fun _ _ => decidable_of_iff _ G_adj.symm

/-- Boolean form of "no claw centred at `v` with leaves `a, b, c`". -/
def clawB (v a b c : Fin 12) : Bool :=
  !(adjN v a && adjN v b && adjN v c && a != b && a != c && b != c) ||
    (adjN a b || adjN a c || adjN b c)

theorem clawB_all : ∀ v a b c : Fin 12, clawB v a b c = true := by decide

theorem G_isClawFree : IsClawFree G := by
  intro v a b c hva hvb hvc hab hac hbc
  have := clawB_all v a b c
  rw [clawB, G_adj.mp hva, G_adj.mp hvb, G_adj.mp hvc, bne_iff_ne.mpr hab, bne_iff_ne.mpr hac,
    bne_iff_ne.mpr hbc] at this
  simp only [G_adj]
  simpa [or_assoc] using this

/-! ### Monomial coefficients of `X_G` -/

/-- The adjacency matrix of `G` packed into one number: bit `12 b + a` is set iff `a ~ b`.
This is only a faster lookup table for the kernel; `adjB_eq` checks it against `adjN`. -/
def adjBits : ℕ := 8502139051590243936873777420823523682290256

/-- Fast adjacency lookup. -/
def adjB (a b : ℕ) : Bool := (adjBits >>> (12 * b + a)) % 2 == 1

theorem adjB_eq : ∀ a b : Fin 12, adjB a b = adjN a b := by decide

/-- The colouring constraint between vertices `a < b`. -/
def colR (a b : ℕ) (x y : Fin 4) : Bool := !(adjB a b) || (x != y)

theorem proper_iff (κ : Fin 12 → Fin 4) :
    (∀ u v, G.Adj u v → κ u ≠ κ v) ↔ ∀ a b : Fin 12, a < b → colR a b (κ a) (κ b) = true := by
  constructor
  · intro h a b _
    simp only [colR, adjB_eq, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq]
    by_cases hab : adjN a b = true
    · exact Or.inr (h a b (G_adj.mpr hab))
    · exact Or.inl (by simpa using hab)
  · intro h u v huv
    have hne : u ≠ v := G.ne_of_adj huv
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := h u v hlt
      simp only [colR, adjB_eq, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne] at this
      exact this.resolve_left (by simp [G_adj.mp huv])
    · have := h v u hlt
      simp only [colR, adjB_eq, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne] at this
      exact (this.resolve_left (by simp [adjN_symm u v (G_adj.mp huv)])).symm

theorem coeff_chromSym_eq_gen (α : Fin 4 →₀ ℕ) (w : Fin 4 → ℕ) (hw : ∀ i, α i = w i) :
    coeff α (chromSym G 4) =
      (((Enum.gen colR 12).filter
        fun l => (List.finRange 4).all fun i => l.count i == w i).length : ℤ) := by
  rw [chromSym, coeff_sum_prod_X, Finset.filter_filter,
    ← card_content_eq colR (fun κ : Fin 12 → Fin 4 => ∀ u v, G.Adj u v → κ u ≠ κ v) α w hw
      proper_iff]
  exact_mod_cast Finset.card_bij (fun a _ => a) (fun a ha => by simpa using ha)
    (fun _ _ _ _ h => h) (fun b hb => ⟨b, by simpa using hb, rfl⟩)

/-- `x^{5322}`, `x^{4422}`, `x^{4332}`, `x^{3333}` as exponent vectors. -/
noncomputable def e5322 : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![5, 3, 2, 2]
noncomputable def e4422 : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![4, 4, 2, 2]
noncomputable def e4332 : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![4, 3, 3, 2]
noncomputable def e3333 : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![3, 3, 3, 3]

/-- Every proper 4-colouring whose class sizes are non-increasing has class sizes `5322`, `4422`,
`4332` or `3333`. -/
def antiOK (l : List (Fin 4)) : Bool :=
  !(decide (l.count 1 ≤ l.count 0) && decide (l.count 2 ≤ l.count 1) &&
      decide (l.count 3 ≤ l.count 2)) ||
    ([l.count 0, l.count 1, l.count 2, l.count 3] == [5, 3, 2, 2] ||
     [l.count 0, l.count 1, l.count 2, l.count 3] == [4, 4, 2, 2] ||
     [l.count 0, l.count 1, l.count 2, l.count 3] == [4, 3, 3, 2] ||
     [l.count 0, l.count 1, l.count 2, l.count 3] == [3, 3, 3, 3])

/-- The content test "class sizes equal `w`" used for counting. -/
def contentIs (w : Fin 4 → ℕ) (l : List (Fin 4)) : Bool :=
  (List.finRange 4).all fun i => l.count i == w i

/-- All facts about a list of colourings that we need, gathered so that the kernel computes them
in one pass: the numbers with class sizes `5322`, `4422`, `4332`, `3333`, and `antiOK` for all. -/
def summ (L : List (List (Fin 4))) : ℕ × ℕ × ℕ × ℕ × Bool :=
  ((L.filter (contentIs ![5, 3, 2, 2])).length, (L.filter (contentIs ![4, 4, 2, 2])).length,
    (L.filter (contentIs ![4, 3, 3, 2])).length, (L.filter (contentIs ![3, 3, 3, 3])).length,
    L.all antiOK)

/-- Componentwise combination of two summaries. -/
def summAdd (x y : ℕ × ℕ × ℕ × ℕ × Bool) : ℕ × ℕ × ℕ × ℕ × Bool :=
  (x.1 + y.1, x.2.1 + y.2.1, x.2.2.1 + y.2.2.1, x.2.2.2.1 + y.2.2.2.1, x.2.2.2.2 && y.2.2.2.2)

theorem summ_append (L₁ L₂ : List (List (Fin 4))) :
    summ (L₁ ++ L₂) = summAdd (summ L₁) (summ L₂) := by
  simp [summ, summAdd, List.filter_append, List.all_append]

end OpenProblemsLab.ClawFree.Second
