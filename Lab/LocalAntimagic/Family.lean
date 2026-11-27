import Lab.LocalAntimagic.Caterpillar

/-!
# The leaf conjecture is false, and `χ_la(T) − ℓ(T)` is unbounded

Brondani–França (arXiv:2610.22783, Theorem 5.2 and Corollary 5.3). For `r ≥ 2` and `t ≥ 1` let
`aᵢ = 4^(2^r − 2^(r−i))` (`1 ≤ i ≤ r`; here indexed from `0`) and `dᵢ = t·aᵢ`. The caterpillar
`H_{r,t}` with spine degrees `d₁, …, d_r` is separated in the sense of `Caterpillar.lean`, so every
labelling is antimagic and `χ_la(H_{r,t}) = ℓ(H_{r,t}) + r`.

* `family`: `H_{r,t}` is a tree with at least three vertices and `χ_la = ℓ + r`, and every
  labelling has pairwise distinct vertex weights;
* `not_leafConjecture`: the leaf conjecture `χ_la(T) ≤ ℓ(T) + 2` is false (`r = 3`, `t = 1`);
* `no_constant`: for every `C` some tree with at least three vertices has `χ_la > ℓ + C`.

The arithmetic follows the paper: `a₁² = 4A`, `a_{i+1}² = 4A·aᵢ` with `A = a_r`, `a_{i+1} ≥ 4aᵢ`,
hence `3∑aᵢ < 4A` and `m < 4tA/3`.
-/

namespace OpenProblemsLab.LocalAntimagic

open Finset SimpleGraph

/-- `a r i = 4^(2^r − 2^(r−(i+1)))`, the paper's `a_{i+1}`. -/
def a (r i : ℕ) : ℕ := 4 ^ (2 ^ r - 2 ^ (r - (i + 1)))

/-- The spine degrees of `H_{r,t}`. -/
def hd (r t : ℕ) (i : Fin r) : ℕ := t * a r i.1

theorem two_pow_succ_sub {r i : ℕ} (h : i + 2 ≤ r) :
    2 ^ (r - (i + 1)) = 2 * 2 ^ (r - (i + 2)) := by
  rw [← pow_succ']; congr 1; omega

theorem pow_sub_le {r i : ℕ} : 2 ^ (r - i) ≤ 2 ^ r :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `a₁² = 4A`. -/
theorem a_zero_sq {r : ℕ} (hr : 1 ≤ r) : a r 0 * a r 0 = 4 * a r (r - 1) := by
  unfold a
  rw [← pow_add, ← pow_succ']
  congr 1
  have h1 : 2 ^ (r - (0 + 1)) * 2 = 2 ^ r := by rw [← pow_succ]; congr 1; omega
  have h2 : r - (r - 1 + 1) = 0 := by omega
  rw [h2, pow_zero]
  have : 1 ≤ 2 ^ (r - (0 + 1)) := Nat.one_le_two_pow
  omega

/-- `a_{i+1}² = 4A·aᵢ`. -/
theorem a_succ_sq {r i : ℕ} (h : i + 2 ≤ r) :
    a r (i + 1) * a r (i + 1) = 4 * a r (r - 1) * a r i := by
  unfold a
  rw [← pow_add, ← pow_succ', ← pow_add]
  congr 1
  have h1 := two_pow_succ_sub h
  have h2 : r - (r - 1 + 1) = 0 := by omega
  rw [h2, pow_zero, show r - (i + 1 + 1) = r - (i + 2) by omega]
  have h3 : 2 ^ (r - (i + 1)) ≤ 2 ^ r := pow_sub_le
  have h4 : 1 ≤ 2 ^ (r - (i + 2)) := Nat.one_le_two_pow
  have h5 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  omega

theorem four_mul_a_le {r i : ℕ} (h : i + 2 ≤ r) : 4 * a r i ≤ a r (i + 1) := by
  unfold a
  rw [← pow_succ']
  apply Nat.pow_le_pow_right (by norm_num)
  have h1 := two_pow_succ_sub h
  rw [show r - (i + 1 + 1) = r - (i + 2) by omega]
  have h3 : 2 ^ (r - (i + 1)) ≤ 2 ^ r := pow_sub_le
  have h4 : 1 ≤ 2 ^ (r - (i + 2)) := Nat.one_le_two_pow
  omega

theorem a_pos (r i : ℕ) : 1 ≤ a r i := Nat.one_le_pow _ _ (by norm_num)

theorem four_le_a {r i : ℕ} (hi : i < r) : 4 ≤ a r i := by
  unfold a
  have : 2 ^ (r - (i + 1)) < 2 ^ r := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact Nat.le_self_pow (by omega) 4

theorem a_mono {r i j : ℕ} (hij : i ≤ j) (hj : j < r) : a r i ≤ a r j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (ih (by omega)).trans (by have := four_mul_a_le (r := r) (i := n) (by omega); omega)

/-- `3 ∑_{i ≤ k} aᵢ < 4 a_k`. -/
theorem three_sum_lt {r : ℕ} : ∀ k, k < r → 3 * ∑ i ∈ range (k + 1), a r i < 4 * a r k := by
  intro k
  induction k with
  | zero => intro _; simp; have := a_pos r 0; omega
  | succ n ih =>
    intro hk
    rw [sum_range_succ]
    have := ih (by omega)
    have := four_mul_a_le (r := r) (i := n) (by omega)
    omega

theorem three_sum_lt' {r : ℕ} (hr : 1 ≤ r) : 3 * ∑ i : Fin r, a r i.1 < 4 * a r (r - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => a r i), show r = r - 1 + 1 by omega]
  simpa using three_sum_lt (r - 1 + 1 - 1) (by omega)

theorem hd_separated {r t : ℕ} (hr : 2 ≤ r) (ht : 1 ≤ t) : Separated (hd r t) := by
  set A := a r (r - 1)
  set S := ∑ i : Fin r, a r i.1
  have hS : 3 * S < 4 * A := three_sum_lt' (by omega)
  have hsum : ∑ j : Fin r, hd r t j = t * S := by simp [hd, S, mul_sum]
  set m := ∑ j : Fin r, hd r t j + 1 - r
  have hm : 2 * m < 4 * t * A := by
    have : m ≤ t * S := by omega
    have : 3 * (t * S) < 4 * t * A := by nlinarith
    omega
  have hd0 : ∀ i : Fin r, 4 * t * A ≤ hd r t i * hd r t i := by
    intro i
    have h0 := a_zero_sq (r := r) (by omega)
    have hmono := a_mono (r := r) (Nat.zero_le i.1) i.2
    simp only [hd]
    calc 4 * t * A = t * (a r 0 * a r 0) := by rw [h0]; ring
      _ ≤ t * t * (a r 0 * a r 0) := by
          apply Nat.mul_le_mul_right; nlinarith
      _ ≤ t * t * (a r i * a r i) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hmono hmono)
      _ = t * a r i * (t * a r i) := by ring
  refine ⟨hr, fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
  · have := four_le_a i.2
    simp only [hd]; nlinarith
  · have := hd0 i; nlinarith
  · have hsq := a_succ_sq (r := r) (i := i.1) (by omega)
    rw [show i.1 + 1 = j.1 from hij] at hsq
    have hlt : hd r t i < hd r t j := by
      simp only [hd]
      have := four_mul_a_le (r := r) (i := i.1) (by omega)
      rw [hij] at this
      have := a_pos r i.1
      nlinarith
    have key : 2 * hd r t i * m < hd r t j * hd r t j := by
      have hpos : 0 < hd r t i := by simp only [hd]; have := a_pos r i.1; positivity
      calc 2 * hd r t i * m = hd r t i * (2 * m) := by ring
        _ < hd r t i * (4 * t * A) := Nat.mul_lt_mul_of_pos_left hm hpos
        _ = t * t * (4 * A * a r i.1) := by simp only [hd]; ring
        _ = hd r t j * hd r t j := by rw [← hsq]; simp only [hd]; ring
    nlinarith

/-- **Brondani–França, Theorem 5.2.** For `r ≥ 2`, `t ≥ 1`, the caterpillar `H_{r,t}` is a tree
with at least three vertices, every labelling has pairwise distinct weights, and
`χ_la(H_{r,t}) = ℓ(H_{r,t}) + r`. -/
theorem family {r t : ℕ} (hr : 2 ≤ r) (ht : 1 ≤ t) :
    (Cat (hd r t)).IsTree ∧ 3 ≤ Fintype.card (CV (hd r t)) ∧
      (∀ f : Labelling (Cat (hd r t)), Function.Injective (wt f)) ∧
      chiLA (Cat (hd r t)) = numLeaves (Cat (hd r t)) + r := by
  have hS := hd_separated hr ht
  exact ⟨cat_isTree hS.two_le hS.deg, three_le_card hS, wt_injective hS, chiLA_eq hS⟩

/-- **The leaf conjecture is false** (`H_{3,1}` has `χ_la = ℓ + 3`). -/
theorem not_leafConjecture : ¬ LeafConjecture := by
  intro h
  obtain ⟨h1, h2, -, h4⟩ := family (r := 3) (t := 1) (by norm_num) le_rfl
  have := h _ (Cat (hd 3 1)) h1 h2
  omega

/-- **Brondani–França, Corollary 5.3.** No constant `C` gives `χ_la(T) ≤ ℓ(T) + C` for all trees
with at least three vertices. -/
theorem no_constant (C : ℕ) : ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (T : SimpleGraph V)
    (_ : DecidableRel T.Adj), T.IsTree ∧ 3 ≤ Fintype.card V ∧ numLeaves T + C < chiLA T := by
  obtain ⟨h1, h2, -, h4⟩ := family (r := C + 2) (t := 1) (by omega) le_rfl
  exact ⟨_, inferInstance, inferInstance, _, inferInstance, h1, h2, by omega⟩

end OpenProblemsLab.LocalAntimagic
