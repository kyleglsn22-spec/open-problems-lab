import Mathlib

/-!
# The Chow–Rimanić lonely runner conjecture over function fields is false (claim LR-1)

S. Chow and L. Rimanić (Mathematika 65 (2019), "Lonely runners in function fields") introduced a
function-field model of the lonely runner problem. Over `𝔽_q`, write a "time" as a power series
`α = ∑_{n ≥ 1} α_n T^{-n}` and, for a "speed" `f ∈ 𝔽_q[T]`, let `‖α f‖ = q^{-m}` where `T^{-m}` is
the highest power with a nonzero coefficient in the fractional part of `α f` (and `‖α f‖ = 0` if
the fractional part vanishes). The loneliness of a finite family `F` of nonzero polynomials is
`δ(F) = sup_α min_{f ∈ F} ‖α f‖`.

**Conjecture** (Chow–Rimanić): if `|F| < 1 + q + ⋯ + q^k` then `δ(F) ≥ q^{-k}`.

X. Hu (arXiv:2608.18818, Theorem 1.2) found 13 monic polynomials over `𝔽₂` with
`δ(F*) = 2^{-4} < 2^{-3}`, although `13 < 1 + 2 + 4 + 8 = 15`. We formalize the case `q = 2` of the
conjecture (`ChowRimanicConjectureTwo`) and prove it false (`not_chowRimanicConjectureTwo`) by
showing `δ(F*) ≤ 2^{-4}` (`delta_Fstar_le`).

The key finite fact (`cover`): for every choice of the seven coefficients `α_1, …, α_7`, some
`f ∈ F*` has vanishing coefficients at `T^{-1}, T^{-2}, T^{-3}` in `α f` (the paper's covering of
`𝔽₂⁷` by thirteen partial-circulant kernels), checked by the kernel over all 128 choices.
-/

namespace OpenProblemsLab.LonelyRunner

open Polynomial Finset

/-! ## Statement -/

/-- The coefficient of `T^{-m}` (`m ≥ 1`) in the fractional part of `α f`, where `α n` is the
coefficient of `T^{-n}` in `α` (the value `α 0` is never used). -/
def fracCoeff (α : ℕ → ZMod 2) (f : (ZMod 2)[X]) (m : ℕ) : ZMod 2 :=
  ∑ j ∈ range (f.natDegree + 1), f.coeff j * α (m + j)

open Classical in
/-- The distance `‖α f‖` from `α f` to the polynomial ring: `2^{-m}` for the least `m ≥ 1` with a
nonzero coefficient of `T^{-m}`, and `0` if there is none. -/
noncomputable def lonelyNorm (α : ℕ → ZMod 2) (f : (ZMod 2)[X]) : ℝ :=
  if h : ∃ m, 1 ≤ m ∧ fracCoeff α f m ≠ 0 then (2 : ℝ) ^ (-(Nat.find h : ℤ)) else 0

/-- The loneliness `δ(F) = sup_α min_{f ∈ F} ‖α f‖` of a nonempty finite family of speeds. -/
noncomputable def delta (F : Finset (ZMod 2)[X]) (hne : F.Nonempty) : ℝ :=
  sSup (Set.range fun α : ℕ → ZMod 2 => F.inf' hne (lonelyNorm α))

/-- **Chow–Rimanić conjecture, case `q = 2`**: a nonempty family of fewer than
`1 + 2 + ⋯ + 2^k` nonzero polynomials over `𝔽₂` has loneliness at least `2^{-k}`. -/
def ChowRimanicConjectureTwo : Prop :=
  ∀ (k : ℕ) (F : Finset (ZMod 2)[X]) (hne : F.Nonempty), 1 ≤ k → (∀ f ∈ F, f ≠ 0) →
    F.card < ∑ i ∈ range (k + 1), 2 ^ i → (2 : ℝ) ^ (-(k : ℤ)) ≤ delta F hne

/-! ## Hu's family -/

/-- The polynomial with coefficient vector `v` (degree at most 4). -/
noncomputable def poly (v : Fin 5 → ZMod 2) : (ZMod 2)[X] := ∑ j : Fin 5, C (v j) * X ^ (j : ℕ)

/-- Coefficient vectors (constant term first) of Hu's thirteen polynomials:
`1, T²+T, T²+T+1, T³, T³+T²+1, T³+T+1, T³+T²+T+1, T⁴+T², T⁴+T, T⁴+T³+1, T⁴+T²+1, T⁴+T+1,
T⁴+T³+T²+T+1`. -/
def tbl : Fin 13 → Fin 5 → ZMod 2 :=
  ![![1, 0, 0, 0, 0], ![0, 1, 1, 0, 0], ![1, 1, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 1, 1, 0],
    ![1, 1, 0, 1, 0], ![1, 1, 1, 1, 0], ![0, 0, 1, 0, 1], ![0, 1, 0, 0, 1], ![1, 0, 0, 1, 1],
    ![1, 0, 1, 0, 1], ![1, 1, 0, 0, 1], ![1, 1, 1, 1, 1]]

open Classical in
/-- Hu's family `F*` of thirteen polynomials over `𝔽₂`. -/
noncomputable def Fstar : Finset (ZMod 2)[X] := univ.image fun i => poly (tbl i)

theorem coeff_poly (v : Fin 5 → ZMod 2) (n : ℕ) :
    (poly v).coeff n = if h : n < 5 then v ⟨n, h⟩ else 0 := by
  simp only [poly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩]
    · simp
    · intro b _ hb
      have : n ≠ (b : ℕ) := fun e => hb (Fin.ext e.symm)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun b _ => ?_
    have : n ≠ (b : ℕ) := by omega
    simp [this]

theorem natDegree_poly_le (v : Fin 5 → ZMod 2) : (poly v).natDegree ≤ 4 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_poly, dif_neg (by omega)]

theorem fracCoeff_poly (α : ℕ → ZMod 2) (v : Fin 5 → ZMod 2) (m : ℕ) :
    fracCoeff α (poly v) m = ∑ j : Fin 5, v j * α (m + j) := by
  unfold fracCoeff
  have hd := natDegree_poly_le v
  rw [Finset.sum_subset (s₂ := range 5) (fun x hx => by simp at hx ⊢; omega)
    (fun x hx hx' => by
      simp at hx hx'
      rw [coeff_poly, dif_pos hx]
      have : (poly v).coeff x = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [coeff_poly, dif_pos hx] at this
      rw [this, zero_mul])]
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_poly, dif_pos j.isLt]

theorem poly_injective : Function.Injective poly := by
  intro v w h
  funext j
  have := congrArg (fun p => p.coeff j) h
  simp only [coeff_poly, dif_pos j.isLt] at this
  exact this

theorem tbl_injective : Function.Injective tbl := by decide +kernel

theorem card_Fstar : Fstar.card = 13 := by
  classical
  unfold Fstar
  rw [Finset.card_image_of_injective _
    (show Function.Injective (fun i => poly (tbl i)) from poly_injective.comp tbl_injective)]
  simp

theorem Fstar_nonempty : Fstar.Nonempty := by
  classical
  exact ⟨poly (tbl 0), Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩⟩

theorem tbl_ne_zero : ∀ i, ∃ j, tbl i j ≠ 0 := by decide +kernel

theorem Fstar_ne_zero : ∀ f ∈ Fstar, f ≠ 0 := by
  classical
  intro f hf h0
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hf
  obtain ⟨j, hj⟩ := tbl_ne_zero i
  have := congrArg (fun p => p.coeff j) h0
  simp only [coeff_poly, dif_pos j.isLt, coeff_zero] at this
  exact hj this

/-- **The covering certificate** (Hu, Proposition 3.1): the thirteen partial-circulant kernels
cover `𝔽₂⁷`. -/
theorem cover : ∀ a : Fin 7 → ZMod 2, ∃ i : Fin 13, ∀ s : Fin 3,
    ∑ j : Fin 5, tbl i j * a ⟨s.val + j.val, by omega⟩ = 0 := by
  decide +kernel

/-- For every time `α`, some speed in `F*` has `‖α f‖ ≤ 2^{-4}`. -/
theorem exists_small (α : ℕ → ZMod 2) : ∃ f ∈ Fstar, lonelyNorm α f ≤ (2 : ℝ) ^ (-(4 : ℤ)) := by
  classical
  obtain ⟨i, hi⟩ := cover fun t => α (t.val + 1)
  refine ⟨poly (tbl i), Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
  have hz : ∀ m, 1 ≤ m → m ≤ 3 → fracCoeff α (poly (tbl i)) m = 0 := by
    intro m h1 h3
    rw [fracCoeff_poly]
    have := hi ⟨m - 1, by omega⟩
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    simp only
    omega
  unfold lonelyNorm
  split_ifs with h
  · have hm := Nat.find_spec h
    have h4 : 4 ≤ Nat.find h := by
      by_contra hc
      exact hm.2 (hz _ hm.1 (by omega))
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  · positivity

/-- **Hu's theorem (upper bound)**: `δ(F*) ≤ 2^{-4}`. -/
theorem delta_Fstar_le : delta Fstar Fstar_nonempty ≤ (2 : ℝ) ^ (-(4 : ℤ)) := by
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨α, rfl⟩
  obtain ⟨f, hf, hle⟩ := exists_small α
  exact Finset.inf'_le_of_le _ hf hle

/-- **The Chow–Rimanić conjecture (case `q = 2`, hence the general conjecture) is false.** -/
theorem not_chowRimanicConjectureTwo : ¬ ChowRimanicConjectureTwo := by
  intro h
  have h1 := h 3 Fstar Fstar_nonempty (by norm_num) Fstar_ne_zero (by rw [card_Fstar]; decide)
  have h2 := delta_Fstar_le
  have : (2 : ℝ) ^ (-(3 : ℤ)) ≤ (2 : ℝ) ^ (-(4 : ℤ)) := by exact_mod_cast h1.trans h2
  norm_num at this

end OpenProblemsLab.LonelyRunner
