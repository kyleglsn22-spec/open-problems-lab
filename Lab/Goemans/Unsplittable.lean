import Mathlib

/-!
# Goemans's unsplittable-flow conjecture is false

Single-source unsplittable flow: a directed network with nonnegative arc costs, a source `s` and
terminals `t₀, …, t_k` with positive demands `d_i`. A fractional flow routes each demand along
several `s`–`t_i` paths. An unsplittable flow routes each demand along one path. Write `D` for the
largest demand.

Dinitz, Garg and Goemans (1999) showed that every fractional flow can be turned into an
unsplittable flow that raises each arc load by less than `D`. Goemans conjectured (personal
communication, January 2000, see Salazar–Skutella 2009) that this can be done **without
increasing the total cost**: for every fractional flow `f` there is an unsplittable flow `g` with
`load_g(a) ≤ load_f(a) + D` for every arc `a` and `cost(g) ≤ cost(f)`.

Ge, Xie, Li and Li (arXiv:2611.23244, Section 2.2.2, a counterexample they credit to Rybin) give a
seven-vertex network where this fails:

* vertices `s, u, v, w, t₁, t₂, t₃` (here `0, …, 6`),
* arcs `s→t₁` (cost 2), `s→t₂` (cost 3), `u→t₃` (cost 2), and cost-0 arcs `s→u, u→v, v→t₁, v→w,
  w→t₂, w→t₃`,
* demands `15, 10, 15`, so `D = 15`,
* fractional flow: terminal 1 sends `10` along `s t₁` and `5` along `s u v t₁`; terminal 2 sends
  `6` along `s t₂` and `4` along `s u v w t₂`; terminal 3 sends `10` along `s u t₃` and `5` along
  `s u v w t₃`. Its cost is `58`.

Every unsplittable flow uses one of the two paths per terminal (the network is acyclic, so walks and
paths agree). Taking two of the long paths
overloads `s→u`, `u→v` or `v→w`; taking at most one costs at least `60`.

Our statement restricts the conjecture to networks without parallel arcs and to fractional flows
along simple paths. Both restrictions only narrow the "for every", so refuting it refutes the
original. Main results: `not_goemansConjecture`, with the instance facts `fracFlow_isFlow`,
`fracCost_eq` and `unsplittable_bad`.
-/

namespace OpenProblemsLab.Goemans

open Finset

/-- A single-source network: a decidable arc relation on a finite vertex type, nonnegative arc
costs and a source. -/
structure Network (V : Type) where
  arc : V → V → Prop
  [decArc : DecidableRel arc]
  cost : V → V → ℝ
  cost_nonneg : ∀ u v, 0 ≤ cost u v
  source : V

/-- `p` is a directed path from `a` to `b` in `N`: a vertex list without repetitions, starting at
`a`, ending at `b`, with consecutive vertices joined by arcs. -/
def IsPath {V : Type} (N : Network V) (a b : V) (p : List V) : Prop :=
  p.head? = some a ∧ p.getLast? = some b ∧ p.Nodup ∧ p.IsChain N.arc

/-- The arcs traversed by a vertex list, as consecutive pairs. -/
def arcsOf {V : Type} (p : List V) : List (V × V) := p.zip p.tail

/-- A fractional (splittable) flow, given by a path decomposition: a finite list of entries
`(i, p, x)`, meaning `x ≥ 0` units of terminal `i`'s demand travel along the path `p`. -/
abbrev FracFlow (V : Type) (k : ℕ) := List (Fin (k + 1) × List V × ℝ)

/-- `f` is a fractional flow for terminals `t` with demands `d`: every entry is a nonnegative
amount on an `s`–`t_i` path, and the amounts for terminal `i` add up to `d i`. -/
def IsFlow {V : Type} {k : ℕ} (N : Network V) (t : Fin (k + 1) → V) (d : Fin (k + 1) → ℝ)
    (f : FracFlow V k) : Prop :=
  (∀ e ∈ f, 0 ≤ e.2.2 ∧ IsPath N N.source (t e.1) e.2.1) ∧
  ∀ i, (f.map fun e => if e.1 = i then e.2.2 else 0).sum = d i

variable {V : Type} [DecidableEq V] {k : ℕ}

/-- Load of the fractional flow `f` on the pair `(u, v)`. -/
def fracLoad (f : FracFlow V k) (u v : V) : ℝ :=
  (f.map fun e => if (u, v) ∈ arcsOf e.2.1 then e.2.2 else 0).sum

/-- Load of the unsplittable flow sending all of `d i` along `P i`, on the pair `(u, v)`. -/
def unsplitLoad (d : Fin (k + 1) → ℝ) (P : Fin (k + 1) → List V) (u v : V) : ℝ :=
  ∑ i, if (u, v) ∈ arcsOf (P i) then d i else 0

/-- Total cost of a load function. -/
def totalCost [Fintype V] (N : Network V) (load : V → V → ℝ) : ℝ :=
  ∑ u, ∑ v, N.cost u v * load u v

/-- The largest demand. -/
def maxDemand (d : Fin (k + 1) → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty d

/-- **Goemans's unsplittable-flow conjecture.** For every single-source network with nonnegative
costs, all positive demands and every fractional flow `f`, some unsplittable flow raises no arc load
by more than the largest demand and costs no more than `f`. -/
def GoemansConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (N : Network V) (k : ℕ) (t : Fin (k + 1) → V)
    (d : Fin (k + 1) → ℝ), (∀ i, 0 < d i) → ∀ f : FracFlow V k, IsFlow N t d f →
    ∃ P : Fin (k + 1) → List V, (∀ i, IsPath N N.source (t i) (P i)) ∧
      (∀ u v, unsplitLoad d P u v ≤ fracLoad f u v + maxDemand d) ∧
      totalCost N (unsplitLoad d P) ≤ totalCost N (fracLoad f)

attribute [instance] Network.decArc

/-! ## The seven-vertex counterexample

Vertices: `s = 0`, `u = 1`, `v = 2`, `w = 3`, `t₁ = 4`, `t₂ = 5`, `t₃ = 6`. -/

/-- The nine arcs. -/
def arcList : List (Fin 7 × Fin 7) :=
  [(0, 4), (0, 5), (0, 1), (1, 2), (1, 6), (2, 4), (2, 3), (3, 5), (3, 6)]

/-- Arc costs: `s→t₁` costs 2, `s→t₂` costs 3, `u→t₃` costs 2, every other pair costs 0. -/
def costFn (a b : Fin 7) : ℝ :=
  if (a, b) = (0, 4) then 2 else if (a, b) = (0, 5) then 3 else if (a, b) = (1, 6) then 2 else 0

/-- The network. -/
def N : Network (Fin 7) where
  arc a b := (a, b) ∈ arcList
  cost := costFn
  cost_nonneg a b := by unfold costFn; split_ifs <;> norm_num
  source := 0

/-- Terminals `t₁, t₂, t₃`. -/
def t : Fin 3 → Fin 7 := ![4, 5, 6]

/-- Demands `15, 10, 15`. -/
def d : Fin 3 → ℝ := ![15, 10, 15]

/-- The short paths `s t₁`, `s t₂`, `s u t₃`. -/
def rPath : Fin 3 → List (Fin 7) := ![[0, 4], [0, 5], [0, 1, 6]]

/-- The long paths `s u v t₁`, `s u v w t₂`, `s u v w t₃`. -/
def zPath : Fin 3 → List (Fin 7) := ![[0, 1, 2, 4], [0, 1, 2, 3, 5], [0, 1, 2, 3, 6]]

/-- The fractional flow of the paper. -/
def fracFlow : FracFlow (Fin 7) 2 :=
  [(0, rPath 0, 10), (0, zPath 0, 5), (1, rPath 1, 6), (1, zPath 1, 4), (2, rPath 2, 10),
    (2, zPath 2, 5)]

theorem d_pos : ∀ i, 0 < d i := by
  intro i; fin_cases i <;> simp [d]

theorem fracFlow_isFlow : IsFlow N t d fracFlow := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [fracFlow, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨by norm_num, ?_⟩ <;> simp only [IsPath, N] <;> decide
  · intro i
    fin_cases i <;> simp [fracFlow, d] <;> norm_num

theorem maxDemand_eq : maxDemand d = 15 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    fin_cases i <;> simp [d]; norm_num
  · exact Finset.le_sup' d (Finset.mem_univ (0 : Fin 3))

theorem fracCost_eq : totalCost N (fracLoad fracFlow) = 58 := by
  simp [totalCost, Fin.sum_univ_seven, fracLoad, fracFlow, N, costFn, arcsOf, rPath, zPath]
  norm_num

/-! ### Every `s`–`t_i` path is the short or the long one -/

/-- Out-neighbours. -/
def succs (a : Fin 7) : List (Fin 7) := (List.finRange 7).filter fun b => (a, b) ∈ arcList

/-- All walks from `a` with at most `n` arcs. -/
def walks : ℕ → Fin 7 → List (List (Fin 7))
  | 0, a => [[a]]
  | n + 1, a => [a] :: (succs a).flatMap fun b => (walks n b).map (a :: ·)

theorem mem_walks : ∀ (n : ℕ) (a : Fin 7) (p : List (Fin 7)), p.head? = some a →
    p.IsChain N.arc → p.length ≤ n + 1 → p ∈ walks n a := by
  intro n
  induction n with
  | zero =>
    intro a p hh _ hl
    match p, hh, hl with
    | [b], hh, _ => simp at hh; simp [walks, hh]
  | succ n ih =>
    intro a p hh hc hl
    match p, hh, hc, hl with
    | [b], hh, _, _ => simp at hh; simp [walks, hh]
    | b :: c :: q, hh, hc, hl =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      rw [List.isChain_cons_cons] at hc
      have hc1 : c ∈ succs b := by
        simp only [succs, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
        exact hc.1
      have := ih c (c :: q) rfl hc.2 (by simp at hl ⊢; omega)
      simp only [walks, List.mem_cons, List.mem_flatMap, List.mem_map]
      exact Or.inr ⟨c, hc1, c :: q, this, rfl⟩

theorem walks_end : ∀ i : Fin 3, ∀ p ∈ walks 6 0, p.getLast? = some (t i) →
    p = rPath i ∨ p = zPath i := by decide

theorem path_cases (i : Fin 3) (p : List (Fin 7)) (hp : IsPath N N.source (t i) p) :
    p = rPath i ∨ p = zPath i := by
  obtain ⟨hh, hl, hn, hc⟩ := hp
  have hlen : p.length ≤ 6 + 1 := by
    have := hn.length_le_card
    simpa using this
  exact walks_end i p (mem_walks 6 0 p hh hc hlen) hl

/-! ### No unsplittable flow is good enough -/

theorem unsplittable_bad (P : Fin 3 → List (Fin 7)) (hP : ∀ i, IsPath N N.source (t i) (P i))
    (hadm : ∀ u v, unsplitLoad d P u v ≤ fracLoad fracFlow u v + 15) :
    58 < totalCost N (unsplitLoad d P) := by
  have h0 := path_cases 0 (P 0) (hP 0)
  have h1 := path_cases 1 (P 1) (hP 1)
  have h2 := path_cases 2 (P 2) (hP 2)
  have hsu := hadm 0 1
  have huv := hadm 1 2
  have hvw := hadm 2 3
  rcases h0 with e0 | e0 <;> rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2 <;>
    simp only [unsplitLoad, totalCost, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, e0, e1, e2]
      at hsu huv hvw ⊢ <;>
    simp [ rPath, zPath, arcsOf, d, fracLoad, fracFlow, N, costFn] at hsu huv hvw ⊢ <;>
    linarith

/-- **Goemans's unsplittable-flow conjecture is false.** -/
theorem not_goemansConjecture : ¬ GoemansConjecture := by
  intro h
  obtain ⟨P, hP, hadm, hcost⟩ := h (Fin 7) N 2 t d d_pos fracFlow fracFlow_isFlow
  rw [maxDemand_eq] at hadm
  have := unsplittable_bad P hP hadm
  rw [fracCost_eq] at hcost
  linarith

end OpenProblemsLab.Goemans
