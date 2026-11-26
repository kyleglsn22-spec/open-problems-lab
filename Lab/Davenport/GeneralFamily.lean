import Mathlib
import Lab.Davenport.VanEmdeBoasKruyswijk

/-!
# The Gao–Geroldinger–Wang–Zeng family: `D(C_n^r) > r(n-1) + 1` for all `n ≡ 2 (mod 4)`, `n ≥ 6`

Gao, Geroldinger, Wang and Zeng (arXiv:2611.24775 v3, Theorem 1.1 and its proof) construct, for
`n = 2k` with `k ≥ 3` odd, a zero-sumfree sequence of length `5k(n-1) + 1` over `C_n^{5k}`.
We formalize the construction for every such `n` (written `k = 2t + 1`, `n = 4t + 2`, `t ≥ 1`),
padded with `n - 1` copies of `b` further basis vectors. This proves the "in particular" part of
their Theorem 1.1: for every `r ≥ 5n/2` there is a zero-sumfree sequence of length `r(n-1) + 1`
over `C_n^r`, so `D(C_n^r) ≥ r(n-1) + 2`.

The `n = 6` case is `Lab/Davenport/VanEmdeBoasKruyswijk.lean`; this file generalizes it.
The sharper bound `D(C_n^r) ≥ r(n-1) + 1 + ⌊(r-1)/(5k-1)⌋` (their replacement step) is not
formalized here.

## Layout (coordinates `Idx t b`, element kinds `Kind t b`)

* Blocks `i : Fin k` with coordinates `(i, 0..3)` = `e₁, e₂, e₃, f` carrying
  `W = z f^{n-3} ∏ⱼ eⱼ^{k-1} (eⱼ + f)^k`, `z = e₁ + e₂ + e₃ + (1 - 3k) f`.
* `Fᵢ` for `i : Fin (k-1)` (multiplicity `n - 2`), the coordinate `u`, padding `Fin b`.
* Center `u + Σᵢ s fᵢ + (1 - v) Σᵢ Fᵢ` with `s = (1-k)/2 = -t`, `v = (k+1)/2 = t+1`.
* Leaves `u + aᵢ + k Fᵢ`, `u + dᵢ + k Fᵢ` (no `F` part for the last block), and
  `(u + v Fᵢ)²` for `i : Fin (k-1)`, with `aᵢ = e₂ - e₁ + s f`, `dᵢ = e₃ - e₂ + s f`.
* Padding: `n - 1` copies of each extra basis vector.
-/

namespace OpenProblemsLab.Davenport.Family

open Finset


/-- A multiple of `4t+2` in a window. -/
theorem dvd_cases (t : ℤ) (ht : 0 ≤ t) (y : ℤ) (h : (4 * t + 2) ∣ y)
    (lo : -3 * (4 * t + 2) < y) (hi : y < 3 * (4 * t + 2)) :
    y = -2 * (4 * t + 2) ∨ y = -(4 * t + 2) ∨ y = 0 ∨ y = 4 * t + 2 ∨ y = 2 * (4 * t + 2) := by
  obtain ⟨q, rfl⟩ := h
  have hq1 : -3 < q := by
    by_contra hc; push Not at hc; nlinarith
  have hq2 : q < 3 := by
    by_contra hc; push Not at hc; nlinarith
  interval_cases q <;> omega

theorem block (t z f e1 e2 e3 g1 g2 g3 x α δ : ℤ) (ht : 1 ≤ t)
    (hz : 0 ≤ z ∧ z ≤ 1) (hf : 0 ≤ f ∧ f ≤ 4 * t - 1)
    (he1 : 0 ≤ e1 ∧ e1 ≤ 2 * t) (he2 : 0 ≤ e2 ∧ e2 ≤ 2 * t) (he3 : 0 ≤ e3 ∧ e3 ≤ 2 * t)
    (hg1 : 0 ≤ g1 ∧ g1 ≤ 2 * t + 1) (hg2 : 0 ≤ g2 ∧ g2 ≤ 2 * t + 1)
    (hg3 : 0 ≤ g3 ∧ g3 ≤ 2 * t + 1)
    (hx : 0 ≤ x ∧ x ≤ 1) (hα : 0 ≤ α ∧ α ≤ 1) (hδ : 0 ≤ δ ∧ δ ≤ 1)
    (h1 : (4 * t + 2) ∣ z + e1 + g1 - α)
    (h2 : (4 * t + 2) ∣ z + e2 + g2 + α - δ)
    (h3 : (4 * t + 2) ∣ z + e3 + g3 + δ)
    (h4 : (4 * t + 2) ∣ (-6 * t - 2) * z + f + g1 + g2 + g3 - t * (x + α + δ)) :
    x + α + δ ≠ 2 ∧ (x + α + δ = 0 → z = 0 ∧ f = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ e3 = 0 ∧
      g1 = 0 ∧ g2 = 0 ∧ g3 = 0) := by
  obtain ⟨hz0, hz1⟩ := hz; obtain ⟨hx0, hx1⟩ := hx; obtain ⟨ha0, ha1⟩ := hα
  obtain ⟨hd0, hd1⟩ := hδ
  have q1 := dvd_cases t (by omega) _ h1 (by omega) (by omega)
  have q2 := dvd_cases t (by omega) _ h2 (by omega) (by omega)
  have q3 := dvd_cases t (by omega) _ h3 (by omega) (by omega)
  have q4 := dvd_cases t (by omega) _ h4 (by nlinarith) (by nlinarith)
  interval_cases z <;> interval_cases x <;> interval_cases α <;> interval_cases δ <;>
  · norm_num at q4 ⊢ <;> omega


theorem leafF (t x B A F : ℤ) (ht : 1 ≤ t) (hx : 0 ≤ x ∧ x ≤ 1) (hB0 : 0 ≤ B) (hB2 : B ≤ 2)
    (hA : 0 ≤ A ∧ A ≤ 2) (hF : 0 ≤ F ∧ F ≤ 4 * t) (hxB : x + B ≠ 2)
    (h : (4 * t + 2) ∣ F - t * x + (2 * t + 1) * B + (t + 1) * A) :
    (x = 0 → B + A ≤ 2 ∧ (B + A = 0 → F = 0)) ∧
      (x = 1 → (B = 0 ∨ B = 2) ∧ (A = 0 ∨ A = 2)) := by
  obtain ⟨hx0, hx1⟩ := hx; obtain ⟨hA0, hA2⟩ := hA; obtain ⟨hF0, hF1⟩ := hF
  have q := dvd_cases t (by omega) _ h (by nlinarith) (by nlinarith)
  interval_cases x <;> interval_cases B <;> interval_cases A <;> omega

theorem global (t : ℕ) (ht : 1 ≤ t) (x : ℤ) (B : Fin (2 * t + 1) → ℤ) (A F : Fin (2 * t) → ℤ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hB : ∀ i, 0 ≤ B i ∧ B i ≤ 2) (hA : ∀ i, 0 ≤ A i ∧ A i ≤ 2)
    (hFb : ∀ i, 0 ≤ F i ∧ F i ≤ 4 * t) (hxB : ∀ i, x + B i ≠ 2)
    (hF : ∀ i, (4 * (t : ℤ) + 2) ∣ F i - t * x + (2 * t + 1) * B i.castSucc + (t + 1) * A i)
    (hU : (4 * (t : ℤ) + 2) ∣ x + ∑ i, B i + ∑ i, A i) :
    x = 0 ∧ (∀ i, B i = 0) ∧ (∀ i, A i = 0) ∧ ∀ i, F i = 0 := by
  have L := fun i => leafF t x (B i.castSucc) (A i) (F i) (by exact_mod_cast ht) hx
    (hB _).1 (hB _).2 (hA i) (hFb i) (hxB _) (hF i)
  rw [Fin.sum_univ_castSucc] at hU
  obtain ⟨hx0, hx1⟩ := hx
  have hlast := hB (Fin.last _)
  have hxl := hxB (Fin.last _)
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl
  · -- no center
    have hle : ∑ i : Fin (2 * t), (B i.castSucc + A i) ≤ ∑ _i : Fin (2 * t), (2 : ℤ) :=
      Finset.sum_le_sum fun i _ => ((L i).1 rfl).1
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin (2 * t))), 0 ≤ B i.castSucc + A i :=
      fun i _ => by have := hB i.castSucc; have := hA i; omega
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
    have hsplit : (0 : ℤ) + (∑ i : Fin (2 * t), B i.castSucc + B (Fin.last _)) + ∑ i, A i =
        ∑ i : Fin (2 * t), (B i.castSucc + A i) + B (Fin.last _) := by
      rw [Finset.sum_add_distrib]; ring
    rw [hsplit] at hU
    have h0 : 0 ≤ ∑ i : Fin (2 * t), (B i.castSucc + A i) := Finset.sum_nonneg hnn
    have q := dvd_cases t (by omega) _ hU (by push_cast at hle; nlinarith) (by push_cast at hle; nlinarith)
    have hlz : B (Fin.last _) = 0 := by omega
    have hsz : ∑ i : Fin (2 * t), (B i.castSucc + A i) = 0 := by omega
    rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at hsz
    have hBi : ∀ i : Fin (2 * t), B i.castSucc = 0 ∧ A i = 0 := fun i => by
      have := hsz i (Finset.mem_univ _); have := hB i.castSucc; have := hA i; omega
    refine ⟨rfl, ?_, fun i => (hBi i).2, fun i => ((L i).1 rfl).2 (by have := hBi i; omega)⟩
    intro i
    induction i using Fin.lastCases with
    | last => exact hlz
    | cast i => exact (hBi i).1
  · -- center chosen: total is odd
    exfalso
    have hev : Even (∑ i : Fin (2 * t), B i.castSucc + B (Fin.last _) + ∑ i, A i) := by
      refine Even.add (Even.add (Finset.even_sum _ fun i _ => ?_) ?_) (Finset.even_sum _ fun i _ => ?_)
      · rcases ((L i).2 rfl).1 with h | h <;> rw [h] <;> decide
      · rcases (show B (Fin.last _) = 0 ∨ B (Fin.last _) = 2 by omega) with h | h <;> rw [h] <;> decide
      · rcases ((L i).2 rfl).2 with h | h <;> rw [h] <;> decide
    obtain ⟨m, hm⟩ := hev
    have h2 : (2 : ℤ) ∣ 4 * (t : ℤ) + 2 := ⟨2 * t + 1, by ring⟩
    obtain ⟨q, hq⟩ := dvd_trans h2 hU
    omega


variable (t b : ℕ)

/-- Coordinates: block coordinates `(i, j)`, `Fᵢ`, `u`, padding. -/
abbrev Idx := (Fin (2 * t + 1) × Fin 4) ⊕ (Fin (2 * t) ⊕ (Unit ⊕ Fin b))

/-- Kinds of elements: `W`-terms `(i, s)`, `Fᵢ`, center, leaves `(i, e)`, `A`-leaves, padding. -/
abbrev Kind := (Fin (2 * t + 1) × Fin 8) ⊕ (Fin (2 * t) ⊕ (Unit ⊕ ((Fin (2 * t + 1) × Fin 2) ⊕
  (Fin (2 * t) ⊕ Fin b))))

/-- Rows of `W`: `z, f, e₁, e₁+f, e₂, e₂+f, e₃, e₃+f` with `z = e₁+e₂+e₃+(1-3k)f`, `k = 2t+1`. -/
def wcoef : Fin 8 → Fin 4 → ℤ := ![![1, 1, 1, -6 * t - 2], ![0, 0, 0, 1], ![1, 0, 0, 0],
  ![1, 0, 0, 1], ![0, 1, 0, 0], ![0, 1, 0, 1], ![0, 0, 1, 0], ![0, 0, 1, 1]]

/-- Block parts of the leaves `a = e₂ - e₁ + s f`, `d = e₃ - e₂ + s f`, `s = (1-k)/2 = -t`. -/
def lcoef : Fin 2 → Fin 4 → ℤ := ![![-1, 1, 0, -t], ![0, -1, 1, -t]]

/-- Block part of the center: `c = s f`. -/
def ccoef : Fin 4 → ℤ := ![0, 0, 0, -t]

/-- Integer coordinates of each kind of element. -/
def vZ : Kind t b → Idx t b → ℤ
  | .inl (i, s), .inl (i', j) => if i = i' then wcoef t s j else 0
  | .inr (.inl i), .inr (.inl i') => if i = i' then 1 else 0
  | .inr (.inr (.inl _)), .inl (_, j) => ccoef t j
  | .inr (.inr (.inl _)), .inr (.inl _) => -t
  | .inr (.inr (.inl _)), .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr (.inl (i, e)))), .inl (i', j) => if i = i' then lcoef t e j else 0
  | .inr (.inr (.inr (.inl (i, _)))), .inr (.inl i') => if i = i'.castSucc then 2 * t + 1 else 0
  | .inr (.inr (.inr (.inl _))), .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr (.inr (.inl i)))), .inr (.inl i') => if i = i' then t + 1 else 0
  | .inr (.inr (.inr (.inr (.inl _)))), .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr (.inr (.inr i)))), .inr (.inr (.inr i')) => if i = i' then 1 else 0
  | _, _ => 0

/-- Multiplicities. -/
def mult : Kind t b → ℕ
  | .inl (_, s) => ![1, 4 * t - 1, 2 * t, 2 * t + 1, 2 * t, 2 * t + 1, 2 * t, 2 * t + 1] s
  | .inr (.inl _) => 4 * t
  | .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr (.inl _))) => 1
  | .inr (.inr (.inr (.inr (.inl _)))) => 2
  | .inr (.inr (.inr (.inr (.inr _)))) => 4 * t + 1

variable {t b}

abbrev cW (c : Kind t b → ℕ) (i : Fin (2 * t + 1)) (s : Fin 8) : ℤ := c (.inl (i, s))
abbrev cF (c : Kind t b → ℕ) (i : Fin (2 * t)) : ℤ := c (.inr (.inl i))
abbrev cX (c : Kind t b → ℕ) : ℤ := c (.inr (.inr (.inl ())))
abbrev cL (c : Kind t b → ℕ) (i : Fin (2 * t + 1)) (e : Fin 2) : ℤ :=
  c (.inr (.inr (.inr (.inl (i, e)))))
abbrev cA (c : Kind t b → ℕ) (i : Fin (2 * t)) : ℤ := c (.inr (.inr (.inr (.inr (.inl i)))))
abbrev cP (c : Kind t b → ℕ) (i : Fin b) : ℤ := c (.inr (.inr (.inr (.inr (.inr i)))))

theorem coord_blk (c : Kind t b → ℕ) (i : Fin (2 * t + 1)) (j : Fin 4) :
    ∑ k, (c k : ℤ) * vZ t b k (.inl (i, j)) =
      ∑ s, cW c i s * wcoef t s j + cX c * ccoef t j + ∑ e, cL c i e * lcoef t e j := by
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, vZ, cW, cX, cL]
  ring

theorem coord_F (c : Kind t b → ℕ) (i : Fin (2 * t)) :
    ∑ k, (c k : ℤ) * vZ t b k (.inr (.inl i)) =
      cF c i - t * cX c + (2 * t + 1) * (cL c i.castSucc 0 + cL c i.castSucc 1) +
        (t + 1) * cA c i := by
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, vZ, Fin.sum_univ_two, ← ite_add_zero,
    Finset.sum_ite_eq', cF, cX, cL, cA]
  ring

theorem coord_U (c : Kind t b → ℕ) :
    ∑ k, (c k : ℤ) * vZ t b k (.inr (.inr (.inl ()))) =
      cX c + ∑ i, (cL c i 0 + cL c i 1) + ∑ i, cA c i := by
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, vZ, Fin.sum_univ_two, cX, cL, cA]
  ring

theorem coord_P (c : Kind t b → ℕ) (i : Fin b) :
    ∑ k, (c k : ℤ) * vZ t b k (.inr (.inr (.inr i))) = cP c i := by
  simp [Fintype.sum_sum_type, vZ, cP]


/-! ### The group, the sequence, and its length -/

variable (t b) in
/-- The group `C_n^{5k + b}`, coordinates indexed by `Idx t b`. -/
abbrev Grp := Idx t b → ZMod (4 * t + 2)

variable (t b) in
/-- The element of each kind. -/
def v (k : Kind t b) : Grp t b := fun x => (vZ t b k x : ZMod (4 * t + 2))

variable (t b) in
/-- The GGWZ sequence (padded). -/
def S : Multiset (Grp t b) := ∑ k, Multiset.replicate (mult t b k) (v t b k)

theorem card_S (ht : 1 ≤ t) : (S t b).card = (10 * t + 5 + b) * (4 * t + 1) + 1 := by
  simp only [S, Multiset.card_sum, Multiset.card_replicate]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, mult, Fin.sum_univ_eight]
  zify [show 1 ≤ 4 * t by omega]
  ring

/-! ### From a vanishing weighted sum to divisibilities -/

theorem coord_dvd (c : Kind t b → ℕ) (h : ∑ k, c k • v t b k = 0) (x : Idx t b) :
    (4 * (t : ℤ) + 2) ∣ ∑ k, (c k : ℤ) * vZ t b k x := by
  have hx := congrFun h x
  simp only [Finset.sum_apply, nsmul_eq_mul, Pi.zero_apply] at hx
  have h' : ((∑ k, (c k : ℤ) * vZ t b k x : ℤ) : ZMod (4 * t + 2)) = 0 := by
    push_cast; exact hx
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'
  exact_mod_cast this

/-! ### The core: bounded counts with vanishing weighted sum are zero -/

theorem core (ht : 1 ≤ t) (c : Kind t b → ℕ) (hc : ∀ k, c k ≤ mult t b k)
    (h : ∑ k, c k • v t b k = 0) : ∀ k, c k = 0 := by
  have hd := coord_dvd c h
  have htz : (1 : ℤ) ≤ t := by exact_mod_cast ht
  -- bounds
  have bW : ∀ i s, 0 ≤ (c (.inl (i, s)) : ℤ) ∧ (c (.inl (i, s)) : ℤ) ≤
      ![1, 4 * (t : ℤ) - 1, 2 * t, 2 * t + 1, 2 * t, 2 * t + 1, 2 * t, 2 * t + 1] s := by
    intro i s
    have := hc (.inl (i, s))
    refine ⟨by positivity, ?_⟩
    fin_cases s <;> simp [mult] at this ⊢ <;> omega
  have bF : ∀ i, 0 ≤ cF c i ∧ cF c i ≤ 4 * t := fun i => by
    have := hc (.inr (.inl i)); simp [mult] at this; exact ⟨by positivity, by simp only [cF]; omega⟩
  have bX : 0 ≤ cX c ∧ cX c ≤ 1 := by
    have := hc (.inr (.inr (.inl ()))); simp [mult] at this
    exact ⟨by positivity, by simp only [cX]; omega⟩
  have bL : ∀ i e, 0 ≤ cL c i e ∧ cL c i e ≤ 1 := fun i e => by
    have := hc (.inr (.inr (.inr (.inl (i, e))))); simp [mult] at this
    exact ⟨by positivity, by simp only [cL]; omega⟩
  have bA : ∀ i, 0 ≤ cA c i ∧ cA c i ≤ 2 := fun i => by
    have := hc (.inr (.inr (.inr (.inr (.inl i))))); simp [mult] at this
    exact ⟨by positivity, by simp only [cA]; omega⟩
  have bP : ∀ i, 0 ≤ cP c i ∧ cP c i ≤ 4 * t + 1 := fun i => by
    have := hc (.inr (.inr (.inr (.inr (.inr i))))); simp [mult] at this
    exact ⟨by positivity, by simp only [cP]; omega⟩
  -- the blocks
  have hblk : ∀ i, cX c + cL c i 0 + cL c i 1 ≠ 2 ∧ (cX c + cL c i 0 + cL c i 1 = 0 →
      cW c i 0 = 0 ∧ cW c i 1 = 0 ∧ cW c i 2 = 0 ∧ cW c i 4 = 0 ∧ cW c i 6 = 0 ∧
      cW c i 3 = 0 ∧ cW c i 5 = 0 ∧ cW c i 7 = 0) := by
    intro i
    have e := fun j => coord_blk (b := b) c i j ▸ hd (.inl (i, j))
    have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3
    simp [Fin.sum_univ_eight, Fin.sum_univ_two, wcoef, lcoef, ccoef] at e0 e1 e2 e3
    have w0 := bW i 0; have w1 := bW i 1; have w2 := bW i 2; have w3 := bW i 3
    have w4 := bW i 4; have w5 := bW i 5; have w6 := bW i 6; have w7 := bW i 7
    simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one] at w0 w1 w2 w3 w4 w5 w6 w7
    exact block t (cW c i 0) (cW c i 1) (cW c i 2) (cW c i 4) (cW c i 6) (cW c i 3) (cW c i 5)
      (cW c i 7) (cX c) (cL c i 0) (cL c i 1) htz w0 w1 w2 w4 w6 w3 w5 w7 bX (bL i 0) (bL i 1)
      (by convert e0 using 1; try ring) (by convert e1 using 1; try ring)
      (by convert e2 using 1; try ring) (by convert e3 using 1; try ring)
  -- the leaves
  have G := global t ht (cX c) (fun i => cL c i 0 + cL c i 1) (cA c) (cF c) bX
    (fun i => ⟨by linarith [(bL i 0).1, (bL i 1).1], by linarith [(bL i 0).2, (bL i 1).2]⟩)
    bA bF (fun i => by have := (hblk i).1; omega)
    (fun i => coord_F (b := b) c i ▸ hd (.inr (.inl i)))
    (coord_U (b := b) c ▸ hd (.inr (.inr (.inl ()))))
  obtain ⟨hx0, hB0, hA0, hF0⟩ := G
  have hL0 : ∀ i, cL c i 0 = 0 ∧ cL c i 1 = 0 := fun i => by
    have h : cL c i 0 + cL c i 1 = 0 := hB0 i
    have := bL i 0; have := bL i 1
    omega
  have hW0 := fun i => (hblk i).2 (by rw [hx0, (hL0 i).1, (hL0 i).2]; norm_num)
  have hP0 : ∀ i, cP c i = 0 := fun i => by
    have e := coord_P (b := b) c i ▸ hd (.inr (.inr (.inr i)))
    have := dvd_cases t (by omega) _ e (by nlinarith [(bP i).1]) (by nlinarith [(bP i).2])
    have := bP i; omega
  intro k
  rcases k with ⟨i, s⟩ | i | ⟨⟩ | ⟨i, e⟩ | i | i
  · obtain ⟨h0, h1, h2, h4, h6, h3, h5, h7⟩ := hW0 i
    fin_cases s
    · exact_mod_cast h0
    · exact_mod_cast h1
    · exact_mod_cast h2
    · exact_mod_cast h3
    · exact_mod_cast h4
    · exact_mod_cast h5
    · exact_mod_cast h6
    · exact_mod_cast h7
  · exact_mod_cast hF0 i
  · exact_mod_cast hx0
  · fin_cases e
    · exact_mod_cast (hL0 i).1
    · exact_mod_cast (hL0 i).2
  · exact_mod_cast hA0 i
  · exact_mod_cast hP0 i

/-! ### From counts to sub-multisets -/

theorem le_sum_decomp {J α : Type*} [DecidableEq J] [DecidableEq α] (A : J → Multiset α) :
    ∀ (s : Finset J) (T : Multiset α), T ≤ ∑ j ∈ s, A j →
      ∃ U : J → Multiset α, (∀ j ∈ s, U j ≤ A j) ∧ T = ∑ j ∈ s, U j := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro T hT
    refine ⟨fun _ => 0, by simp, ?_⟩
    simpa using hT
  | insert a s ha ih =>
    intro T hT
    rw [Finset.sum_insert ha] at hT
    have h2 : T - T ∩ A a ≤ ∑ j ∈ s, A j := by
      rw [Multiset.le_iff_count] at hT ⊢
      intro x
      have := hT x
      rw [Multiset.count_add] at this
      rw [Multiset.count_sub, Multiset.count_inter]
      omega
    obtain ⟨U, hU, hTU⟩ := ih _ h2
    refine ⟨Function.update U a (T ∩ A a), ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · simp [Multiset.inter_le_right]
      · rw [Function.update_of_ne (by rintro rfl; exact ha hj')]; exact hU j hj'
    · rw [Finset.sum_insert ha, Function.update_self]
      rw [Finset.sum_congr rfl (fun j hj => Function.update_of_ne
        (show j ≠ a by rintro rfl; exact ha hj) _ _), ← hTU]
      exact (add_tsub_cancel_of_le (Multiset.inter_le_left)).symm

theorem zeroSumFree_of_core {J H : Type*} [Fintype J] [DecidableEq J] [DecidableEq H]
    [AddCommMonoid H] (w : J → H) (m : J → ℕ)
    (hcore : ∀ c : J → ℕ, (∀ j, c j ≤ m j) → ∑ j, c j • w j = 0 → ∀ j, c j = 0) :
    ZeroSumFree (∑ j, Multiset.replicate (m j) (w j)) := by
  intro T hT hne hsum
  obtain ⟨U, hU, rfl⟩ := le_sum_decomp _ _ T hT
  have hrep : ∀ j, U j = Multiset.replicate (U j).card (w j) := fun j =>
    Multiset.eq_replicate_of_mem fun x hx =>
      Multiset.eq_of_mem_replicate (Multiset.mem_of_le (hU j (Finset.mem_univ _)) hx)
  have hcard : ∀ j, (U j).card ≤ m j := fun j => by
    simpa using Multiset.card_mono (hU j (Finset.mem_univ _))
  have hs : ∑ j, (U j).card • w j = 0 := by
    rw [Multiset.sum_sum] at hsum
    rw [← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [hrep j]
    rw [Multiset.sum_replicate]
  have h0 := hcore _ hcard hs
  apply hne
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [hrep j, h0 j, Multiset.replicate_zero]

theorem zeroSumFree_S (ht : 1 ≤ t) : ZeroSumFree (S t b) :=
  zeroSumFree_of_core _ _ (core ht)

/-! ### Transport to `Fin r → ZMod n` -/

theorem zeroSumFree_map {H K : Type*} [AddCommMonoid H] [AddCommMonoid K] (T : Multiset H)
    (hT : ZeroSumFree T) (φ : H → K) (ψ : K →+ H) (hψ : ∀ x, ψ (φ x) = x) :
    ZeroSumFree (T.map φ) := by
  intro U hU hne hsum
  have h1 : U.map ψ ≤ T := by
    have := Multiset.map_le_map (f := ψ) hU
    rwa [Multiset.map_map, show (⇑ψ ∘ φ) = id from funext hψ, Multiset.map_id] at this
  refine hT _ h1 (by simpa using hne) ?_
  rw [← map_multiset_sum, hsum, map_zero]

theorem card_Idx : Fintype.card (Idx t b) = 10 * t + 5 + b := by
  simp [Fintype.card_sum]; ring

/-- **GGWZ, in Lean.** For `n = 4t + 2 ≥ 6` and every `b`, there is a zero-sumfree sequence of
length `r(n-1) + 1` over `C_n^r`, `r = 5(2t+1) + b`. -/
theorem exists_zeroSumFree_family (t b : ℕ) (ht : 1 ≤ t) :
    ∃ T : Multiset (Fin (10 * t + 5 + b) → ZMod (4 * t + 2)),
      T.card = (10 * t + 5 + b) * (4 * t + 2 - 1) + 1 ∧ ZeroSumFree T := by
  let e : Idx t b ≃ Fin (10 * t + 5 + b) := Fintype.equivFinOfCardEq card_Idx
  let ψ : (Fin (10 * t + 5 + b) → ZMod (4 * t + 2)) →+ Grp t b :=
    { toFun := fun g => g ∘ e, map_zero' := rfl, map_add' := fun _ _ => rfl }
  refine ⟨(S t b).map (fun f => f ∘ e.symm), ?_, ?_⟩
  · rw [Multiset.card_map, card_S ht]; congr 2
  · exact zeroSumFree_map _ (zeroSumFree_S ht) _ ψ
      (fun f => by funext x; simp [ψ])

/-- **Theorem 1.1 of GGWZ ("in particular" part), in Lean.** If `n ≡ 2 (mod 4)`, `n ≥ 6`
and `2r ≥ 5n`, then `C_n^r` has a zero-sumfree sequence of length `r(n-1) + 1`; hence
`D(C_n^r) > r(n-1) + 1` and the van Emde Boas–Kruyswijk conjecture fails for all these `(n, r)`. -/
theorem ggwz (n r : ℕ) (hn : n % 4 = 2) (h6 : 6 ≤ n) (hr : 5 * n ≤ 2 * r) :
    ∃ T : Multiset (Fin r → ZMod n), T.card = r * (n - 1) + 1 ∧ ZeroSumFree T := by
  obtain ⟨t, rfl⟩ : ∃ t, n = 4 * t + 2 := ⟨n / 4, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, r = 10 * t + 5 + b := ⟨r - (10 * t + 5), by omega⟩
  exact exists_zeroSumFree_family t b (by omega)

/-- The van Emde Boas–Kruyswijk conjecture fails for every `n ≡ 2 (mod 4)`, `n ≥ 6`, and every
rank `r ≥ 5n/2`. -/
theorem vEBK_fails (n r : ℕ) (hn : n % 4 = 2) (h6 : 6 ≤ n) (hr : 5 * n ≤ 2 * r) :
    ∃ T : Multiset (Fin r → ZMod n), r * (n - 1) + 1 ≤ T.card ∧
      ∀ U ≤ T, U ≠ 0 → U.sum ≠ 0 := by
  obtain ⟨T, hc, hT⟩ := ggwz n r hn h6 hr
  exact ⟨T, hc.ge, hT⟩

end OpenProblemsLab.Davenport.Family
