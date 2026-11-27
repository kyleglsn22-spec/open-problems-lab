import Lab.LocalAntimagic.Basic

/-!
# Degree-separated caterpillars have `χ_la = |V|`

For `r ≥ 2` and degrees `d : Fin r → ℕ` (all `≥ 2`), `Cat d` is the caterpillar with spine
`v₀ – v₁ – ⋯ – v_{r−1}` where `vᵢ` carries `pᵢ` leaves, `pᵢ = dᵢ − 1` at the two ends and
`dᵢ − 2` in the middle, so that `deg vᵢ = dᵢ`. It has `m = ∑ dᵢ − r + 1` edges.

If `2m < d₀(d₀+1)` (so every spine weight exceeds every leaf weight) and, for consecutive spine
vertices, `2dᵢm + dᵢ < d_{i+1}(d_{i+1}+1) + dᵢ²` (the weight interval of `vᵢ` lies below that of
`v_{i+1}`), then under every labelling all vertex weights are distinct (Brondani–França,
arXiv:2610.22783, Corollary 3.3 and Proposition 5.1 in the case of increasing degrees). Hence
`χ_la(Cat d) = |V| = ℓ + r`.
-/

namespace OpenProblemsLab.LocalAntimagic

open Finset SimpleGraph

variable {r : ℕ} (d : Fin r → ℕ)

/-- Number of leaves at spine vertex `i`. -/
def pl (i : Fin r) : ℕ := if i.1 = 0 ∨ i.1 + 1 = r then d i - 1 else d i - 2

/-- Vertices: the spine `Fin r` and the leaves `(i, t)`. -/
abbrev CV := Fin r ⊕ (Σ i : Fin r, Fin (pl d i))

/-- Adjacency of the caterpillar. -/
def catAdj : CV d → CV d → Prop
  | .inl i, .inl j => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1
  | .inl i, .inr x => x.1 = i
  | .inr x, .inl i => x.1 = i
  | .inr _, .inr _ => False

instance : DecidableRel (catAdj d) := fun a b => by
  rcases a with a | a <;> rcases b with b | b <;> simp only [catAdj] <;> infer_instance

/-- The caterpillar `Cat d`. -/
def Cat : SimpleGraph (CV d) where
  Adj := catAdj d
  symm := ⟨fun a b h => by
    rcases a with a | a <;> rcases b with b | b <;> simp only [catAdj] at h ⊢ <;> tauto⟩
  loopless := ⟨fun a h => by rcases a with a | a <;> simp only [catAdj] at h; omega⟩

instance : DecidableRel (Cat d).Adj := inferInstanceAs (DecidableRel (catAdj d))

variable {d}

@[simp] theorem adj_ll (i j : Fin r) :
    (Cat d).Adj (.inl i) (.inl j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 := Iff.rfl
@[simp] theorem adj_lr (i : Fin r) (x : Σ i : Fin r, Fin (pl d i)) :
    (Cat d).Adj (.inl i) (.inr x) ↔ x.1 = i := Iff.rfl
@[simp] theorem adj_rl (i : Fin r) (x : Σ i : Fin r, Fin (pl d i)) :
    (Cat d).Adj (.inr x) (.inl i) ↔ x.1 = i := Iff.rfl
@[simp] theorem not_adj_rr (x y : Σ i : Fin r, Fin (pl d i)) :
    ¬ (Cat d).Adj (.inr x) (.inr y) := id

/-! ### Degrees -/

/-- Number of spine neighbours of spine vertex `i`. -/
theorem spine_count (i : ℕ) :
    (∑ j ∈ range r, if i + 1 = j ∨ j + 1 = i then 1 else 0) =
      (if i + 1 < r then 1 else 0) + (if 1 ≤ i ∧ i - 1 < r then 1 else 0) := by
  have h : ∀ j, (if i + 1 = j ∨ j + 1 = i then 1 else 0) =
      (if i + 1 = j then 1 else 0) + (if i - 1 = j ∧ 1 ≤ i then 1 else 0) := by
    intro j; split_ifs <;> omega
  rw [sum_congr rfl fun j _ => h j, sum_add_distrib, sum_ite_eq]
  congr 1
  · simp
  · by_cases hi : 1 ≤ i
    · simp only [hi, and_true, sum_ite_eq, mem_range, true_and]
    · simp [hi]

theorem degree_spine (hr : 2 ≤ r) (hd : ∀ i, 2 ≤ d i) (i : Fin r) :
    (Cat d).degree (.inl i) = d i := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter,
    Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [adj_ll, adj_lr]
  rw [Fin.sum_univ_eq_sum_range (fun j => if i.1 + 1 = j ∨ j + 1 = i.1 then 1 else 0),
    spine_count]
  have hp : (∑ j : Fin r, ∑ _t : Fin (pl d j), if j = i then 1 else 0) = pl d i := by
    simp
  rw [hp, pl]
  have := hd i; have := i.2
  split_ifs <;> omega

theorem degree_leaf (x : Σ i : Fin r, Fin (pl d i)) : (Cat d).degree (.inr x) = 1 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter,
    Fintype.sum_sum_type]
  simp

/-! ### Counting -/

theorem card_CV : Fintype.card (CV d) = r + ∑ i, pl d i := by
  simp [Fintype.card_sigma]

theorem numLeaves_eq (hr : 2 ≤ r) (hd : ∀ i, 2 ≤ d i) : numLeaves (Cat d) = ∑ i, pl d i := by
  rw [numLeaves, card_filter, Fintype.sum_sum_type]
  simp only [degree_spine hr hd, degree_leaf]
  have : ∀ i, (if d i = 1 then 1 else 0) = 0 := fun i => by have := hd i; simp; omega
  simp [this, Fintype.card_sigma]

/-- `∑ dᵢ = ∑ pᵢ + 2(r − 1)`. -/
theorem sum_d (hr : 2 ≤ r) (hd : ∀ i, 2 ≤ d i) : ∑ i, d i = ∑ i, pl d i + 2 * (r - 1) := by
  have h : ∀ i : Fin r, d i = pl d i + ((if i.1 + 1 < r then 1 else 0) +
      (if 1 ≤ i.1 then 1 else 0)) := by
    intro i; have := hd i; have := i.2; unfold pl; split_ifs <;> omega
  rw [sum_congr rfl fun i _ => h i, sum_add_distrib, sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i + 1 < r then 1 else 0),
    Fin.sum_univ_eq_sum_range (fun i => if 1 ≤ i then 1 else 0), sum_boole, sum_boole]
  have h1 : ((range r).filter fun i => i + 1 < r) = range (r - 1) := by
    ext i; simp; omega
  have h2 : ((range r).filter fun i => 1 ≤ i) = Ico 1 r := by
    ext i; simp; omega
  rw [h1, h2]
  simp
  omega

/-- The number of edges: `2m = ∑ deg = ∑ dᵢ + ∑ pᵢ`. -/
theorem two_card_edges (hr : 2 ≤ r) (hd : ∀ i, 2 ≤ d i) :
    2 * Fintype.card (Cat d).edgeSet = ∑ i, d i + ∑ i, pl d i := by
  have h := (Cat d).sum_degrees_eq_twice_card_edges
  rw [edgeFinset_card] at h
  rw [← h, Fintype.sum_sum_type]
  simp only [degree_spine hr hd, degree_leaf]
  simp [Fintype.card_sigma]

theorem card_edges (hr : 2 ≤ r) (hd : ∀ i, 2 ≤ d i) :
    Fintype.card (Cat d).edgeSet + r = ∑ i, d i + 1 := by
  have := two_card_edges hr hd
  have := sum_d hr hd
  omega

/-! ### Tree -/

theorem cat_connected (hr : 2 ≤ r) : (Cat d).Connected := by
  have : Nonempty (CV d) := ⟨.inl ⟨0, by omega⟩⟩
  have h0 : ∀ i : Fin r, (Cat d).Reachable (.inl ⟨0, by omega⟩) (.inl i) := by
    rintro ⟨i, hi⟩
    induction i with
    | zero => rfl
    | succ n ih =>
      exact (ih (by omega)).trans (Adj.reachable (by simp))
  have h : ∀ x : CV d, (Cat d).Reachable (.inl ⟨0, by omega⟩) x := by
    rintro (i | x)
    · exact h0 i
    · exact (h0 x.1).trans (Adj.reachable (by simp))
  exact ⟨fun x y => (h x).symm.trans (h y)⟩

theorem cat_isTree (hr : 2 ≤ r) (hd : ∀ i, 2 ≤ d i) : (Cat d).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨cat_connected hr, ?_⟩
  simp only [Nat.card_eq_fintype_card]
  have := card_edges hr hd
  have := sum_d hr hd
  rw [card_CV]
  omega

/-! ### All weights distinct -/

/-- Hypotheses: degrees at least 2, every spine weight above every leaf weight, and the weight
intervals of consecutive spine vertices disjoint and increasing. -/
structure Separated (d : Fin r → ℕ) : Prop where
  two_le : 2 ≤ r
  deg : ∀ i, 2 ≤ d i
  low : ∀ i, 2 * (∑ j, d j + 1 - r) < d i * (d i + 1)
  sep : ∀ i j : Fin r, i.1 + 1 = j.1 →
    2 * d i * (∑ j, d j + 1 - r) + d i < d j * (d j + 1) + d i * d i

theorem wt_injective (hS : Separated d) (f : Labelling (Cat d)) : Function.Injective (wt f) := by
  have hm : Fintype.card (Cat d).edgeSet = ∑ j, d j + 1 - r := by
    have := card_edges hS.two_le hS.deg; omega
  -- spine weights exceed `m`
  have hspine : ∀ i, Fintype.card (Cat d).edgeSet < wt f (.inl i) := by
    intro i
    have h := (wt_bounds f (.inl i)).1
    rw [degree_spine hS.two_le hS.deg] at h
    have := hS.low i
    rw [← hm] at this
    omega
  -- spine weights strictly increase
  have hstep : ∀ i j : Fin r, i.1 + 1 = j.1 → wt f (.inl i) < wt f (.inl j) := by
    intro i j hij
    have h1 := (wt_bounds f (.inl i)).2
    have h2 := (wt_bounds f (.inl j)).1
    rw [degree_spine hS.two_le hS.deg] at h1 h2
    have := hS.sep i j hij
    rw [← hm] at this
    nlinarith
  have hlt : ∀ k, ∀ i j : Fin r, j.1 = i.1 + k + 1 → wt f (.inl i) < wt f (.inl j) := by
    intro k
    induction k with
    | zero => intro i j h; exact hstep i j (by omega)
    | succ k ih =>
      intro i j h
      exact (ih i ⟨j.1 - 1, by omega⟩ (by simp; omega)).trans (hstep _ _ (by simp; omega))
  have hmono : Function.Injective fun i : Fin r => wt f (.inl i) := by
    intro i j h
    by_contra hij
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h' | h'
    · exact absurd h (hlt (j.1 - i.1 - 1) i j (by omega)).ne
    · exact absurd h (hlt (i.1 - j.1 - 1) j i (by omega)).ne'
  rintro (i | x) (j | y) h
  · exact congrArg _ (hmono h)
  · have := hspine i; have := wt_leaf_le f _ (degree_leaf y); omega
  · have := hspine j; have := wt_leaf_le f _ (degree_leaf x); omega
  · by_contra hxy
    exact wt_leaf_ne f (degree_leaf x) (degree_leaf y) hxy (not_adj_rr x y) h

/-- **Every labelling of a separated caterpillar is antimagic**, and `χ_la = |V| = ℓ + r`. -/
theorem chiLA_eq (hS : Separated d) : chiLA (Cat d) = numLeaves (Cat d) + r := by
  have hall : ∀ f : Labelling (Cat d), (univ.image (wt f)).card = Fintype.card (CV d) :=
    fun f => by rw [card_image_of_injective _ (wt_injective hS f), card_univ]
  have hV : Fintype.card (CV d) = numLeaves (Cat d) + r := by
    rw [card_CV, numLeaves_eq hS.two_le hS.deg]; omega
  let f0 : Labelling (Cat d) := Fintype.equivFin _
  have hf0 : IsLocalAntimagic (Cat d) f0 := fun u v huv h => huv.ne (wt_injective hS f0 h)
  apply le_antisymm
  · exact Nat.sInf_le ⟨f0, hf0, (hall f0).trans hV⟩
  · refine le_csInf ⟨_, f0, hf0, rfl⟩ ?_
    rintro n ⟨f, -, rfl⟩
    rw [hall f, hV]

theorem three_le_card (hS : Separated d) : 3 ≤ Fintype.card (CV d) := by
  have := sum_d hS.two_le hS.deg
  have := hS.deg ⟨0, by have := hS.two_le; omega⟩
  rw [card_CV]
  have h0 : 1 ≤ pl d ⟨0, by have := hS.two_le; omega⟩ := by simp [pl]; omega
  have := single_le_sum (f := pl d) (fun _ _ => Nat.zero_le _) (mem_univ ⟨0, by have := hS.two_le; omega⟩)
  have := hS.two_le
  omega

end OpenProblemsLab.LocalAntimagic
