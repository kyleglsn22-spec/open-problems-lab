import Mathlib

/-!
# The Edmonds–Johnson property: definitions and a duality-free closure criterion

Definitions follow Del Pia, *The Gerards–Schrijver conjecture on the Edmonds–Johnson property is
false* (arXiv:2611.28580, v1, 20 Nov 2026), Section 1.

* `poly A b c l u` is `P(A; b, c, l, u) = {x ∈ ℝⁿ : b ≤ Ax ≤ c, l ≤ x ≤ u}`.
* `chvatalClosure P` is the set of points of `P` satisfying every Chvátal–Gomory cut
  `w·x ≤ ⌊δ⌋` with `w ∈ ℤⁿ`, `δ ∈ ℝ` and `w·x ≤ δ` valid for `P`.
* `integerHull P` is `conv(P ∩ ℤⁿ)`.
* `HasEJProperty A`: for all integral `b, c, l, u`, the Chvátal closure equals the integer hull.

## The criterion (no LP duality)

`mem_chvatalClosure_of_witness`: a point `z ∈ P` lies in the Chvátal closure as soon as, for every
integral `w`, some point `v ∈ P` has `w·v ≥ ⌈w·z⌉`. Indeed a valid `w·x ≤ δ` then gives
`δ ≥ w·v ≥ ⌈w·z⌉`, an integer, so `⌊δ⌋ ≥ ⌈w·z⌉ ≥ w·z`. The instance files supply `v` among
finitely many points of `P` and check the resulting statement about integers.
-/

namespace EdmondsJohnson

open Finset

variable {m n : ℕ}

/-- `P(A; b, c, l, u) = {x ∈ ℝⁿ : b ≤ Ax ≤ c, l ≤ x ≤ u}`. -/
def poly (A : Matrix (Fin m) (Fin n) ℤ) (b c : Fin m → ℤ) (l u : Fin n → ℤ) :
    Set (Fin n → ℝ) :=
  {x | (∀ i, (b i : ℝ) ≤ ∑ j, (A i j : ℝ) * x j ∧ ∑ j, (A i j : ℝ) * x j ≤ c i) ∧
       ∀ j, (l j : ℝ) ≤ x j ∧ x j ≤ u j}

/-- The (first) Chvátal closure of `P`: the points of `P` that satisfy every Chvátal–Gomory cut
`w·x ≤ ⌊δ⌋`, where `w ∈ ℤⁿ` and `w·x ≤ δ` is valid for `P`. -/
def chvatalClosure (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | x ∈ P ∧ ∀ (w : Fin n → ℤ) (δ : ℝ), (∀ y ∈ P, ∑ j, (w j : ℝ) * y j ≤ δ) →
        ∑ j, (w j : ℝ) * x j ≤ ⌊δ⌋}

/-- The integer hull `P_I = conv(P ∩ ℤⁿ)`. -/
def integerHull (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  convexHull ℝ {x | x ∈ P ∧ ∀ j, ∃ k : ℤ, x j = k}

/-- An integral matrix `A` has the Edmonds–Johnson property if, for all integral vectors
`b, c, l, u`, the first Chvátal closure of `P(A; b, c, l, u)` equals its integer hull. -/
def HasEJProperty (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∀ (b c : Fin m → ℤ) (l u : Fin n → ℤ),
    chvatalClosure (poly A b c l u) = integerHull (poly A b c l u)

/-- Membership of `y / D` in `P(A; b, c, l, u)`, written in integers. -/
def IntMem (A : Matrix (Fin m) (Fin n) ℤ) (b c : Fin m → ℤ) (l u : Fin n → ℤ)
    (D : ℤ) (y : Fin n → ℤ) : Prop :=
  (∀ i, D * b i ≤ ∑ j, A i j * y j ∧ ∑ j, A i j * y j ≤ D * c i) ∧
    ∀ j, D * l j ≤ y j ∧ y j ≤ D * u j

instance (A : Matrix (Fin m) (Fin n) ℤ) (b c : Fin m → ℤ) (l u : Fin n → ℤ) (D : ℤ)
    (y : Fin n → ℤ) : Decidable (IntMem A b c l u D y) := by
  unfold IntMem; infer_instance

lemma mem_poly_of_intMem {A : Matrix (Fin m) (Fin n) ℤ} {b c : Fin m → ℤ} {l u : Fin n → ℤ}
    {D : ℤ} (hD : 0 < D) {y : Fin n → ℤ} (h : IntMem A b c l u D y) :
    (fun j => (y j : ℝ) / D) ∈ poly A b c l u := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hsum : ∀ i, ∑ j, (A i j : ℝ) * ((y j : ℝ) / D) = ((∑ j, A i j * y j : ℤ) : ℝ) / D := by
    intro i; push_cast; rw [Finset.sum_div]; congr 1; ext j; ring
  refine ⟨fun i => ?_, fun j => ?_⟩
  · obtain ⟨h1, h2⟩ := h.1 i
    rw [hsum i, le_div_iff₀ hD', div_le_iff₀ hD']
    generalize ∑ j, A i j * y j = S at h1 h2 ⊢
    constructor
    · have : ((D * b i : ℤ) : ℝ) ≤ (S : ℝ) := by exact_mod_cast h1
      push_cast at this; linarith
    · have : (S : ℝ) ≤ ((D * c i : ℤ) : ℝ) := by exact_mod_cast h2
      push_cast at this; linarith
  · obtain ⟨h1, h2⟩ := h.2 j
    rw [le_div_iff₀ hD', div_le_iff₀ hD']
    constructor
    · have : ((D * l j : ℤ) : ℝ) ≤ (y j : ℝ) := by exact_mod_cast h1
      push_cast at this; linarith
    · have : (y j : ℝ) ≤ ((D * u j : ℤ) : ℝ) := by exact_mod_cast h2
      push_cast at this; linarith

/-- An integral point of `P(A; b, c, l, u)` satisfies the integer form of the constraints. -/
lemma intMem_of_mem {A : Matrix (Fin m) (Fin n) ℤ} {b c : Fin m → ℤ} {l u : Fin n → ℤ}
    {k : Fin n → ℤ} (h : (fun j => (k j : ℝ)) ∈ poly A b c l u) : IntMem A b c l u 1 k := by
  refine ⟨fun i => ?_, fun j => ?_⟩
  · obtain ⟨h1, h2⟩ := h.1 i
    have e : ∑ j, (A i j : ℝ) * (k j : ℝ) = ((∑ j, A i j * k j : ℤ) : ℝ) := by push_cast; rfl
    rw [e] at h1 h2
    exact ⟨by simpa using (show b i ≤ ∑ j, A i j * k j by exact_mod_cast h1),
      by simpa using (show ∑ j, A i j * k j ≤ c i by exact_mod_cast h2)⟩
  · obtain ⟨h1, h2⟩ := h.2 j
    simp only at h1 h2
    exact ⟨by simpa using (show l j ≤ k j by exact_mod_cast h1),
      by simpa using (show k j ≤ u j by exact_mod_cast h2)⟩

/-- **Duality-free criterion.** If `z ∈ P` and every integral `w` has a point `v ∈ P` with
`⌈w·z⌉ ≤ w·v`, then `z` lies in the Chvátal closure of `P`. -/
lemma mem_chvatalClosure_of_witness {P : Set (Fin n → ℝ)} {z : Fin n → ℝ} (hz : z ∈ P)
    (h : ∀ w : Fin n → ℤ, ∃ v ∈ P,
      ((⌈∑ j, (w j : ℝ) * z j⌉ : ℤ) : ℝ) ≤ ∑ j, (w j : ℝ) * v j) :
    z ∈ chvatalClosure P := by
  refine ⟨hz, fun w δ hvalid => ?_⟩
  obtain ⟨v, hv, hle⟩ := h w
  have hkδ : ((⌈∑ j, (w j : ℝ) * z j⌉ : ℤ) : ℝ) ≤ δ := hle.trans (hvalid v hv)
  calc ∑ j, (w j : ℝ) * z j ≤ ⌈∑ j, (w j : ℝ) * z j⌉ := Int.le_ceil _
    _ ≤ ⌊δ⌋ := by exact_mod_cast Int.le_floor.mpr hkδ

/-- The criterion for `z = y / 3`, with witnesses `V i / D`, reduced to a statement about
integers: whenever `3k ≤ w·y + 2` (that is, `k ≤ ⌈w·y / 3⌉`), some `i` has `D·k ≤ w·V i`. -/
lemma mem_chvatalClosure_of_int {A : Matrix (Fin m) (Fin n) ℤ} {b c : Fin m → ℤ}
    {l u : Fin n → ℤ} {N : ℕ} (y : Fin n → ℤ) (V : Fin N → Fin n → ℤ) (D : ℤ) (hD : 0 < D)
    (hy : IntMem A b c l u 3 y) (hV : ∀ i, IntMem A b c l u D (V i))
    (hkey : ∀ (w : Fin n → ℤ) (k : ℤ), 3 * k ≤ ∑ j, w j * y j + 2 →
      ∃ i, D * k ≤ ∑ j, w j * V i j) :
    (fun j => (y j : ℝ) / 3) ∈ chvatalClosure (poly A b c l u) := by
  have hy' := mem_poly_of_intMem (by norm_num) hy
  push_cast at hy'
  refine mem_chvatalClosure_of_witness hy' (fun w => ?_)
  set s := ∑ j, (w j : ℝ) * ((y j : ℝ) / 3) with hs
  have hs' : s = ((∑ j, w j * y j : ℤ) : ℝ) / 3 := by
    rw [hs]; push_cast; rw [Finset.sum_div]; congr 1; ext j; ring
  set k := ⌈s⌉
  have hk1 : (k : ℝ) < s + 1 := Int.ceil_lt_add_one s
  have h3 : 3 * k ≤ ∑ j, w j * y j + 2 := by
    rw [hs'] at hk1
    generalize ∑ j, w j * y j = T at hk1 ⊢
    have : ((3 * k : ℤ) : ℝ) < ((T + 3 : ℤ) : ℝ) := by push_cast; linarith
    have : 3 * k < T + 3 := by exact_mod_cast this
    omega
  obtain ⟨i, hi⟩ := hkey w k h3
  refine ⟨_, mem_poly_of_intMem hD (hV i), ?_⟩
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hsum : ∑ j, (w j : ℝ) * ((V i j : ℝ) / D) = ((∑ j, w j * V i j : ℤ) : ℝ) / D := by
    push_cast; rw [Finset.sum_div]; congr 1; ext j; ring
  rw [hsum, le_div_iff₀ hD']
  generalize ∑ j, w j * V i j = S at hi ⊢
  have : ((D * k : ℤ) : ℝ) ≤ (S : ℝ) := by exact_mod_cast hi
  push_cast at this; linarith

/-- If every integral point of `P` satisfies `w·x ≤ r`, so does every point of `P_I`. -/
lemma integerHull_le {P : Set (Fin n → ℝ)} (w : Fin n → ℤ) (r : ℤ)
    (h : ∀ k : Fin n → ℤ, (fun j => (k j : ℝ)) ∈ P → ∑ j, w j * k j ≤ r)
    {x : Fin n → ℝ} (hx : x ∈ integerHull P) : ∑ j, (w j : ℝ) * x j ≤ r := by
  have hlin : IsLinearMap ℝ (fun y : Fin n → ℝ => ∑ j, (w j : ℝ) * y j) :=
    ⟨fun y y' => by simp [mul_add, Finset.sum_add_distrib],
     fun a y => by simp [Finset.mul_sum]; congr 1; ext j; ring⟩
  have hconv : Convex ℝ {y : Fin n → ℝ | ∑ j, (w j : ℝ) * y j ≤ r} := convex_halfSpace_le hlin _
  refine convexHull_min (fun y hy => ?_) hconv hx
  obtain ⟨hyP, hint⟩ := hy
  choose k hk using hint
  have hyk : y = fun j => (k j : ℝ) := funext hk
  subst hyk
  have := h k hyP
  show ∑ j, (w j : ℝ) * (k j : ℝ) ≤ r
  exact_mod_cast this

end EdmondsJohnson
