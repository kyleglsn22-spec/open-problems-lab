import Mathlib

/-!
# The claw-free Schur-positivity conjecture: definitions

* `IsClawFree G`: `G` has no induced claw `K_{1,3}`, i.e. no vertex with three distinct,
  pairwise non-adjacent neighbours.
* `chromSym G n`: Stanley's chromatic symmetric function `X_G` in the variables `x_0, …, x_{n-1}`:
  the sum over all proper colourings `κ : V → Fin n` of `∏ v, x_{κ v}`.
* `schurPoly n μ`: the Schur polynomial `s_μ(x_0, …, x_{n-1})`, the sum over all semistandard
  fillings `T` of the Young diagram `μ` (Mathlib's `YoungDiagram`) with entries in `Fin n` of
  `∏ cells, x_{T c}`. Semistandard means rows weakly increase and columns strictly increase,
  exactly as in Mathlib's `SemistandardYoungTableau`.
* `SchurPositive f`: `f` is a non-negative integer combination of Schur polynomials.

`ClawFreeSchurPositivity` is the conjecture (Stanley 1998, Conjecture 1.4, credited to Gasharov):
for every claw-free graph `G` the chromatic symmetric function is Schur-positive.

## Why finitely many variables is faithful

The usual statement lives in the ring of symmetric functions in infinitely many variables:
`X_G = ∑ c_μ s_μ` with all `c_μ ≥ 0`. Setting `x_n = x_{n+1} = ⋯ = 0` maps `X_G` to `chromSym G n`
and each `s_μ` to `schurPoly n μ` (colourings and fillings using a colour `≥ n` die). So the usual
conjecture implies `SchurPositive (chromSym G n)` for every `n`, which is our
`ClawFreeSchurPositivity`. Refuting our version therefore refutes the usual one. (Conversely, for
`n ≥ |V|` the two are equivalent, so nothing is lost.)
-/

namespace OpenProblemsLab.ClawFree

open MvPolynomial Finset

/-- A graph is **claw-free** if it has no induced `K_{1,3}`: among any three distinct neighbours of
a vertex, some two are adjacent. -/
def IsClawFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ v a b c, G.Adj v a → G.Adj v b → G.Adj v c → a ≠ b → a ≠ c → b ≠ c →
    G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

/-- Stanley's **chromatic symmetric function** of `G` in the `n` variables `x_0, …, x_{n-1}`:
the sum, over all proper colourings `κ : V → Fin n`, of the monomial `∏ v, x_{κ v}`. -/
noncomputable def chromSym {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) : MvPolynomial (Fin n) ℤ :=
  ∑ κ ∈ univ.filter (fun κ : V → Fin n => ∀ u v, G.Adj u v → κ u ≠ κ v), ∏ v, X (κ v)

/-- A filling `T` of the cells of the Young diagram `μ` (rows indexed by the first coordinate)
is **semistandard** if rows weakly increase left to right and columns strictly increase top to
bottom. -/
def IsSSYT (μ : YoungDiagram) {n : ℕ} (T : μ.cells → Fin n) : Prop :=
  (∀ a b : μ.cells, a.1.1 = b.1.1 → a.1.2 ≤ b.1.2 → T a ≤ T b) ∧
  (∀ a b : μ.cells, a.1.2 = b.1.2 → a.1.1 < b.1.1 → T a < T b)

open scoped Classical in
/-- The **Schur polynomial** `s_μ(x_0, …, x_{n-1})`: the sum over semistandard fillings of `μ`
with entries in `Fin n` of `∏ cells, x_{T c}`. -/
noncomputable def schurPoly (n : ℕ) (μ : YoungDiagram) : MvPolynomial (Fin n) ℤ :=
  ∑ T ∈ univ.filter (fun T : μ.cells → Fin n => IsSSYT μ T), ∏ c, X (T c)

/-- A polynomial is **Schur-positive** if it is a non-negative integer combination of Schur
polynomials. -/
def SchurPositive {n : ℕ} (f : MvPolynomial (Fin n) ℤ) : Prop :=
  ∃ (s : Finset YoungDiagram) (c : YoungDiagram → ℕ), f = ∑ μ ∈ s, (c μ : ℤ) • schurPoly n μ

/-- **The claw-free Schur-positivity conjecture** (Stanley 1998, Conjecture 1.4, credited to
Gasharov): the chromatic symmetric function of every finite claw-free graph is Schur-positive
(here: in every finite number of variables, see the module docstring). -/
def ClawFreeSchurPositivity : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    IsClawFree G → ∀ n, SchurPositive (chromSym G n)

end OpenProblemsLab.ClawFree
