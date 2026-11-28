import Lab.EdmondsJohnson.Basic

/-!
# Del Pia's counterexample `A₆` does not have the Edmonds–Johnson property

Del Pia, arXiv:2611.28580 (v1), Proposition 3.3, with the paper's data `(3)`.

Data: `b = [0, 2, 1, 1, 0]`, `c = [2, 4, 3, 3, 2]`, `l = [-1, 0, -1, 0, -1, -1]`, `u = [1, 2, 1, 2, 2, 2]`, and the point `z = y / 3` with
`y = [2, 1, 2, 1, 2, 1]`. `z` lies in the Chvátal closure of `P = P(A6; b, c, l, u)`
(`z_mem_chvatalClosure`), but every integral point of `P` satisfies `w₀·x ≤ 0` with
`w₀ = [1, -1, 0, 0, 0, 0]`, while `w₀·z > 0` (`z_not_mem_integerHull`).

The closure step uses the duality-free criterion `mem_chvatalClosure_of_int` with
18 vertices of `P` (listed as `2v` in `V`). The integer statement `key` is checked by
bounding a would-be counterexample `w` to a box of
9 points and running `omega` on each.
-/

namespace EdmondsJohnson

/-- The matrix `A6`. -/
def A6 : Matrix (Fin 5) (Fin 6) ℤ :=
  !![0, 0, 1, -1, 0, 0;
     0, 1, 1, 0, 2, 0;
     0, 1, 0, 1, 0, 2;
     1, 0, 1, 0, 2, 0;
     1, 0, 0, 1, 0, 2]

namespace A6Data

def bv : Fin 5 → ℤ := ![0, 2, 1, 1, 0]
def cv : Fin 5 → ℤ := ![2, 4, 3, 3, 2]
def lv : Fin 6 → ℤ := ![-1, 0, -1, 0, -1, -1]
def uv : Fin 6 → ℤ := ![1, 2, 1, 2, 2, 2]
/-- `3z`. -/
def y : Fin 6 → ℤ := ![2, 1, 2, 1, 2, 1]
/-- `2v` for 18 vertices `v` of `P`. -/
def V : Fin 18 → Fin 6 → ℤ :=
  ![![-2, 0, 0, 0, 2, 1],
    ![-2, 0, 0, 0, 2, 3],
    ![-2, 0, 0, 0, 4, 1],
    ![-2, 0, 2, 0, 1, 1],
    ![-2, 0, 2, 0, 3, 1],
    ![-2, 0, 2, 2, 1, 0],
    ![-2, 0, 2, 2, 1, 2],
    ![-2, 0, 2, 2, 3, 2],
    ![-2, 4, 0, 0, 2, 1],
    ![2, 0, 0, 0, 2, 1],
    ![2, 0, 2, 0, 1, 1],
    ![2, 0, 2, 2, 1, 0],
    ![2, 4, 0, 0, 0, -1],
    ![2, 4, 0, 0, 2, 1],
    ![2, 4, 2, 0, 1, 1],
    ![2, 4, 2, 2, -1, 0],
    ![2, 4, 2, 2, 1, -2],
    ![2, 4, 2, 2, 1, 0]]
/-- The separating inequality `w₀·x ≤ 0` of the integer hull. -/
def w₀ : Fin 6 → ℤ := ![1, -1, 0, 0, 0, 0]

lemma y_mem : IntMem A6 bv cv lv uv 3 y := by decide

lemma V_mem : ∀ i, IntMem A6 bv cv lv uv 2 (V i) := by decide

set_option maxHeartbeats 4000000 in
/-- The integer core, on coordinates. -/
lemma key_coords (w0 w1 w2 w3 w4 w5 k : ℤ) (hz : 3 * k ≤ (2) * w0 + (1) * w1 + (2) * w2 + (1) * w3 + (2) * w4 + (1) * w5 + 2)
    (h0 : (-2) * w0 + (0) * w1 + (0) * w2 + (0) * w3 + (2) * w4 + (1) * w5 ≤ 2 * k - 1)
    (h1 : (-2) * w0 + (0) * w1 + (0) * w2 + (0) * w3 + (2) * w4 + (3) * w5 ≤ 2 * k - 1)
    (h2 : (-2) * w0 + (0) * w1 + (0) * w2 + (0) * w3 + (4) * w4 + (1) * w5 ≤ 2 * k - 1)
    (h3 : (-2) * w0 + (0) * w1 + (2) * w2 + (0) * w3 + (1) * w4 + (1) * w5 ≤ 2 * k - 1)
    (h4 : (-2) * w0 + (0) * w1 + (2) * w2 + (0) * w3 + (3) * w4 + (1) * w5 ≤ 2 * k - 1)
    (h5 : (-2) * w0 + (0) * w1 + (2) * w2 + (2) * w3 + (1) * w4 + (0) * w5 ≤ 2 * k - 1)
    (h6 : (-2) * w0 + (0) * w1 + (2) * w2 + (2) * w3 + (1) * w4 + (2) * w5 ≤ 2 * k - 1)
    (h7 : (-2) * w0 + (0) * w1 + (2) * w2 + (2) * w3 + (3) * w4 + (2) * w5 ≤ 2 * k - 1)
    (h8 : (-2) * w0 + (4) * w1 + (0) * w2 + (0) * w3 + (2) * w4 + (1) * w5 ≤ 2 * k - 1)
    (h9 : (2) * w0 + (0) * w1 + (0) * w2 + (0) * w3 + (2) * w4 + (1) * w5 ≤ 2 * k - 1)
    (h10 : (2) * w0 + (0) * w1 + (2) * w2 + (0) * w3 + (1) * w4 + (1) * w5 ≤ 2 * k - 1)
    (h11 : (2) * w0 + (0) * w1 + (2) * w2 + (2) * w3 + (1) * w4 + (0) * w5 ≤ 2 * k - 1)
    (h12 : (2) * w0 + (4) * w1 + (0) * w2 + (0) * w3 + (0) * w4 + (-1) * w5 ≤ 2 * k - 1)
    (h13 : (2) * w0 + (4) * w1 + (0) * w2 + (0) * w3 + (2) * w4 + (1) * w5 ≤ 2 * k - 1)
    (h14 : (2) * w0 + (4) * w1 + (2) * w2 + (0) * w3 + (1) * w4 + (1) * w5 ≤ 2 * k - 1)
    (h15 : (2) * w0 + (4) * w1 + (2) * w2 + (2) * w3 + (-1) * w4 + (0) * w5 ≤ 2 * k - 1)
    (h16 : (2) * w0 + (4) * w1 + (2) * w2 + (2) * w3 + (1) * w4 + (-2) * w5 ≤ 2 * k - 1)
    (h17 : (2) * w0 + (4) * w1 + (2) * w2 + (2) * w3 + (1) * w4 + (0) * w5 ≤ 2 * k - 1) : False := by
  have b0l : 0 ≤ w0 := by omega
  have b0u : w0 ≤ 0 := by omega
  have b1l : 0 ≤ w1 := by omega
  have b1u : w1 ≤ 0 := by omega
  have b2l : 0 ≤ w2 := by omega
  have b2u : w2 ≤ 0 := by omega
  have b3l : 0 ≤ w3 := by omega
  have b3u : w3 ≤ 0 := by omega
  have b4l : -1 ≤ w4 := by omega
  have b4u : w4 ≤ 1 := by omega
  have b5l : -1 ≤ w5 := by omega
  have b5u : w5 ≤ 1 := by omega
  interval_cases w4 <;> interval_cases w5 <;> omega

lemma key (w : Fin 6 → ℤ) (k : ℤ) (hz : 3 * k ≤ ∑ j, w j * y j + 2) :
    ∃ i, 2 * k ≤ ∑ j, w j * V i j := by
  by_contra hc
  push Not at hc
  simp [y, Fin.sum_univ_succ] at hz
  exact key_coords (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) k (by linarith)
    (by have := hc 0; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 1; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 2; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 3; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 4; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 5; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 6; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 7; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 8; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 9; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 10; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 11; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 12; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 13; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 14; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 15; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 16; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 17; simp [V, Fin.sum_univ_succ] at this; linarith)

/-- `z = y / 3` lies in the Chvátal closure of `P`. -/
theorem z_mem_chvatalClosure :
    (fun j => (y j : ℝ) / 3) ∈ chvatalClosure (poly A6 bv cv lv uv) :=
  mem_chvatalClosure_of_int y V 2 (by norm_num) y_mem V_mem key

/-- Every integral point of `P` satisfies `w₀·x ≤ 0`. -/
lemma int_le (k : Fin 6 → ℤ) (hk : (fun j => (k j : ℝ)) ∈ poly A6 bv cv lv uv) :
    ∑ j, w₀ j * k j ≤ 0 := by
  obtain ⟨hr, hb⟩ := intMem_of_mem hk
  have r0 := hr 0
  simp [A6, bv, cv, Fin.sum_univ_succ] at r0
  have r1 := hr 1
  simp [A6, bv, cv, Fin.sum_univ_succ] at r1
  have r2 := hr 2
  simp [A6, bv, cv, Fin.sum_univ_succ] at r2
  have r3 := hr 3
  simp [A6, bv, cv, Fin.sum_univ_succ] at r3
  have r4 := hr 4
  simp [A6, bv, cv, Fin.sum_univ_succ] at r4
  have q0 := hb 0
  simp [lv, uv] at q0
  have q1 := hb 1
  simp [lv, uv] at q1
  have q2 := hb 2
  simp [lv, uv] at q2
  have q3 := hb 3
  simp [lv, uv] at q3
  have q4 := hb 4
  simp [lv, uv] at q4
  have q5 := hb 5
  simp [lv, uv] at q5
  simp [w₀, Fin.sum_univ_succ]
  omega

/-- `z` is not in the integer hull of `P`. -/
theorem z_not_mem_integerHull :
    (fun j => (y j : ℝ) / 3) ∉ integerHull (poly A6 bv cv lv uv) := by
  intro h
  have := integerHull_le w₀ 0 int_le h
  simp [w₀, y, Fin.sum_univ_succ] at this
  norm_num at this

end A6Data

/-- **`A6` does not have the Edmonds–Johnson property.** -/
theorem not_hasEJProperty_A6 : ¬ HasEJProperty A6 := fun h =>
  A6Data.z_not_mem_integerHull (h A6Data.bv A6Data.cv A6Data.lv A6Data.uv ▸ A6Data.z_mem_chvatalClosure)

end EdmondsJohnson
