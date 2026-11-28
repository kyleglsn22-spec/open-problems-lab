import Lab.EdmondsJohnson.Basic

/-!
# The matrix `A₇` does not have the Edmonds–Johnson property

Del Pia, arXiv:2611.28580 (v1), Section 6, states this without proof ("We do not include these
proofs here"). The data below are ours, found by computer search.

Data: `b = [-1, -2, -2, -1, -1]`, `c = [1, 0, 0, 1, 1]`, `l = [-1, -2, -1, -1, -1, -1, -1]`, `u = [1, 0, 1, 1, 2, 2, 2]`, and the point `z = y / 3` with
`y = [-2, -1, -2, -2, 1, 1, 1]`. `z` lies in the Chvátal closure of `P = P(A7; b, c, l, u)`
(`z_mem_chvatalClosure`), but every integral point of `P` satisfies `w₀·x ≤ 1` with
`w₀ = [-1, 1, 0, -1, 1, -1, 1]`, while `w₀·z > 1` (`z_not_mem_integerHull`).

The closure step uses the duality-free criterion `mem_chvatalClosure_of_int` with
42 vertices of `P` (listed as `2v` in `V`). The integer statement `key` is checked by
bounding a would-be counterexample `w` to a box of
18 points and running `omega` on each.
-/

namespace EdmondsJohnson

/-- The matrix `A7`. -/
def A7 : Matrix (Fin 5) (Fin 7) ℤ :=
  !![0, 0, 1, -1, 2, -2, 2;
     0, 1, 1, 0, 2, 0, 0;
     0, 1, 0, 1, 0, 2, 0;
     1, 0, 1, 0, 2, 0, 0;
     1, 0, 0, 1, 0, 2, 0]

namespace A7Data

def bv : Fin 5 → ℤ := ![-1, -2, -2, -1, -1]
def cv : Fin 5 → ℤ := ![1, 0, 0, 1, 1]
def lv : Fin 7 → ℤ := ![-1, -2, -1, -1, -1, -1, -1]
def uv : Fin 7 → ℤ := ![1, 0, 1, 1, 2, 2, 2]
/-- `3z`. -/
def y : Fin 7 → ℤ := ![-2, -1, -2, -2, 1, 1, 1]
/-- `2v` for 42 vertices `v` of `P`. -/
def V : Fin 42 → Fin 7 → ℤ :=
  ![![-2, -4, -2, -2, 1, 1, 1],
    ![-2, -4, -2, -2, 1, 3, 1],
    ![-2, -4, -2, -2, 2, 1, -2],
    ![-2, -4, -2, -2, 3, 1, -1],
    ![-2, -4, -2, 2, 1, -1, -1],
    ![-2, -4, -2, 2, 1, -1, 1],
    ![-2, -4, -2, 2, 1, 1, 1],
    ![-2, -4, -2, 2, 1, 1, 3],
    ![-2, -4, 2, -2, -1, 1, -1],
    ![-2, -4, 2, -2, -1, 1, 1],
    ![-2, -4, 2, -2, 1, 1, -1],
    ![-2, -4, 2, -2, 1, 3, 1],
    ![-2, -4, 2, 2, -1, -1, -1],
    ![-2, -4, 2, 2, -1, -1, 1],
    ![-2, -4, 2, 2, -1, 1, 1],
    ![-2, -4, 2, 2, -1, 1, 3],
    ![-2, -4, 2, 2, 1, 1, -1],
    ![-2, -4, 2, 2, 1, 1, 1],
    ![-2, 0, -2, -2, 1, 1, -1],
    ![-2, 0, -2, -2, 1, 1, 1],
    ![-2, 0, -2, 2, 1, -1, -1],
    ![-2, 0, 2, -2, -1, 1, 1],
    ![-2, 0, 2, 2, -1, -1, -1],
    ![0, -2, -2, 2, 0, -2, 1],
    ![0, -2, -2, 2, 2, -2, -1],
    ![0, -2, 2, 2, 0, -2, -1],
    ![0, 0, 2, -2, -2, 1, 0],
    ![0, 0, 2, 2, -2, -1, 0],
    ![2, -4, -2, -2, 1, 1, 1],
    ![2, 0, -2, -2, -1, -1, -1],
    ![2, 0, -2, -2, 1, -1, -1],
    ![2, 0, -2, -2, 1, 1, -1],
    ![2, 0, -2, -2, 1, 1, 1],
    ![2, 0, -2, 2, -1, -2, 2],
    ![2, 0, -2, 2, -1, -1, 1],
    ![2, 0, -2, 2, 1, -1, -1],
    ![2, 0, 0, -2, -2, 1, 1],
    ![2, 0, 2, -2, -1, 1, -1],
    ![2, 0, 2, -2, -1, 1, 1],
    ![2, 0, 2, 0, -1, -2, -1],
    ![2, 0, 2, 2, -1, -1, -1],
    ![2, 0, 2, 2, -1, -1, 1]]
/-- The separating inequality `w₀·x ≤ 1` of the integer hull. -/
def w₀ : Fin 7 → ℤ := ![-1, 1, 0, -1, 1, -1, 1]

lemma y_mem : IntMem A7 bv cv lv uv 3 y := by decide

lemma V_mem : ∀ i, IntMem A7 bv cv lv uv 2 (V i) := by decide

set_option maxHeartbeats 4000000 in
/-- The integer core, on coordinates. -/
lemma key_coords (w0 w1 w2 w3 w4 w5 w6 k : ℤ) (hz : 3 * k ≤ (-2) * w0 + (-1) * w1 + (-2) * w2 + (-2) * w3 + (1) * w4 + (1) * w5 + (1) * w6 + 2)
    (h0 : (-2) * w0 + (-4) * w1 + (-2) * w2 + (-2) * w3 + (1) * w4 + (1) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h1 : (-2) * w0 + (-4) * w1 + (-2) * w2 + (-2) * w3 + (1) * w4 + (3) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h2 : (-2) * w0 + (-4) * w1 + (-2) * w2 + (-2) * w3 + (2) * w4 + (1) * w5 + (-2) * w6 ≤ 2 * k - 1)
    (h3 : (-2) * w0 + (-4) * w1 + (-2) * w2 + (-2) * w3 + (3) * w4 + (1) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h4 : (-2) * w0 + (-4) * w1 + (-2) * w2 + (2) * w3 + (1) * w4 + (-1) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h5 : (-2) * w0 + (-4) * w1 + (-2) * w2 + (2) * w3 + (1) * w4 + (-1) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h6 : (-2) * w0 + (-4) * w1 + (-2) * w2 + (2) * w3 + (1) * w4 + (1) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h7 : (-2) * w0 + (-4) * w1 + (-2) * w2 + (2) * w3 + (1) * w4 + (1) * w5 + (3) * w6 ≤ 2 * k - 1)
    (h8 : (-2) * w0 + (-4) * w1 + (2) * w2 + (-2) * w3 + (-1) * w4 + (1) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h9 : (-2) * w0 + (-4) * w1 + (2) * w2 + (-2) * w3 + (-1) * w4 + (1) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h10 : (-2) * w0 + (-4) * w1 + (2) * w2 + (-2) * w3 + (1) * w4 + (1) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h11 : (-2) * w0 + (-4) * w1 + (2) * w2 + (-2) * w3 + (1) * w4 + (3) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h12 : (-2) * w0 + (-4) * w1 + (2) * w2 + (2) * w3 + (-1) * w4 + (-1) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h13 : (-2) * w0 + (-4) * w1 + (2) * w2 + (2) * w3 + (-1) * w4 + (-1) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h14 : (-2) * w0 + (-4) * w1 + (2) * w2 + (2) * w3 + (-1) * w4 + (1) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h15 : (-2) * w0 + (-4) * w1 + (2) * w2 + (2) * w3 + (-1) * w4 + (1) * w5 + (3) * w6 ≤ 2 * k - 1)
    (h16 : (-2) * w0 + (-4) * w1 + (2) * w2 + (2) * w3 + (1) * w4 + (1) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h17 : (-2) * w0 + (-4) * w1 + (2) * w2 + (2) * w3 + (1) * w4 + (1) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h18 : (-2) * w0 + (0) * w1 + (-2) * w2 + (-2) * w3 + (1) * w4 + (1) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h19 : (-2) * w0 + (0) * w1 + (-2) * w2 + (-2) * w3 + (1) * w4 + (1) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h20 : (-2) * w0 + (0) * w1 + (-2) * w2 + (2) * w3 + (1) * w4 + (-1) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h21 : (-2) * w0 + (0) * w1 + (2) * w2 + (-2) * w3 + (-1) * w4 + (1) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h22 : (-2) * w0 + (0) * w1 + (2) * w2 + (2) * w3 + (-1) * w4 + (-1) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h23 : (0) * w0 + (-2) * w1 + (-2) * w2 + (2) * w3 + (0) * w4 + (-2) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h24 : (0) * w0 + (-2) * w1 + (-2) * w2 + (2) * w3 + (2) * w4 + (-2) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h25 : (0) * w0 + (-2) * w1 + (2) * w2 + (2) * w3 + (0) * w4 + (-2) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h26 : (0) * w0 + (0) * w1 + (2) * w2 + (-2) * w3 + (-2) * w4 + (1) * w5 + (0) * w6 ≤ 2 * k - 1)
    (h27 : (0) * w0 + (0) * w1 + (2) * w2 + (2) * w3 + (-2) * w4 + (-1) * w5 + (0) * w6 ≤ 2 * k - 1)
    (h28 : (2) * w0 + (-4) * w1 + (-2) * w2 + (-2) * w3 + (1) * w4 + (1) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h29 : (2) * w0 + (0) * w1 + (-2) * w2 + (-2) * w3 + (-1) * w4 + (-1) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h30 : (2) * w0 + (0) * w1 + (-2) * w2 + (-2) * w3 + (1) * w4 + (-1) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h31 : (2) * w0 + (0) * w1 + (-2) * w2 + (-2) * w3 + (1) * w4 + (1) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h32 : (2) * w0 + (0) * w1 + (-2) * w2 + (-2) * w3 + (1) * w4 + (1) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h33 : (2) * w0 + (0) * w1 + (-2) * w2 + (2) * w3 + (-1) * w4 + (-2) * w5 + (2) * w6 ≤ 2 * k - 1)
    (h34 : (2) * w0 + (0) * w1 + (-2) * w2 + (2) * w3 + (-1) * w4 + (-1) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h35 : (2) * w0 + (0) * w1 + (-2) * w2 + (2) * w3 + (1) * w4 + (-1) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h36 : (2) * w0 + (0) * w1 + (0) * w2 + (-2) * w3 + (-2) * w4 + (1) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h37 : (2) * w0 + (0) * w1 + (2) * w2 + (-2) * w3 + (-1) * w4 + (1) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h38 : (2) * w0 + (0) * w1 + (2) * w2 + (-2) * w3 + (-1) * w4 + (1) * w5 + (1) * w6 ≤ 2 * k - 1)
    (h39 : (2) * w0 + (0) * w1 + (2) * w2 + (0) * w3 + (-1) * w4 + (-2) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h40 : (2) * w0 + (0) * w1 + (2) * w2 + (2) * w3 + (-1) * w4 + (-1) * w5 + (-1) * w6 ≤ 2 * k - 1)
    (h41 : (2) * w0 + (0) * w1 + (2) * w2 + (2) * w3 + (-1) * w4 + (-1) * w5 + (1) * w6 ≤ 2 * k - 1) : False := by
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
  have b6l : 0 ≤ w6 := by omega
  have b6u : w6 ≤ 1 := by omega
  interval_cases w4 <;> interval_cases w5 <;> interval_cases w6 <;> omega

lemma key (w : Fin 7 → ℤ) (k : ℤ) (hz : 3 * k ≤ ∑ j, w j * y j + 2) :
    ∃ i, 2 * k ≤ ∑ j, w j * V i j := by
  by_contra hc
  push Not at hc
  simp [y, Fin.sum_univ_succ] at hz
  exact key_coords (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) k (by linarith)
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
    (by have := hc 18; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 19; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 20; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 21; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 22; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 23; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 24; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 25; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 26; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 27; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 28; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 29; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 30; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 31; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 32; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 33; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 34; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 35; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 36; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 37; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 38; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 39; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 40; simp [V, Fin.sum_univ_succ] at this; linarith)
    (by have := hc 41; simp [V, Fin.sum_univ_succ] at this; linarith)

/-- `z = y / 3` lies in the Chvátal closure of `P`. -/
theorem z_mem_chvatalClosure :
    (fun j => (y j : ℝ) / 3) ∈ chvatalClosure (poly A7 bv cv lv uv) :=
  mem_chvatalClosure_of_int y V 2 (by norm_num) y_mem V_mem key

/-- Every integral point of `P` satisfies `w₀·x ≤ 1`. -/
lemma int_le (k : Fin 7 → ℤ) (hk : (fun j => (k j : ℝ)) ∈ poly A7 bv cv lv uv) :
    ∑ j, w₀ j * k j ≤ 1 := by
  obtain ⟨hr, hb⟩ := intMem_of_mem hk
  have r0 := hr 0
  simp [A7, bv, cv, Fin.sum_univ_succ] at r0
  have r1 := hr 1
  simp [A7, bv, cv, Fin.sum_univ_succ] at r1
  have r2 := hr 2
  simp [A7, bv, cv, Fin.sum_univ_succ] at r2
  have r3 := hr 3
  simp [A7, bv, cv, Fin.sum_univ_succ] at r3
  have r4 := hr 4
  simp [A7, bv, cv, Fin.sum_univ_succ] at r4
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
  have q6 := hb 6
  simp [lv, uv] at q6
  simp [w₀, Fin.sum_univ_succ]
  omega

/-- `z` is not in the integer hull of `P`. -/
theorem z_not_mem_integerHull :
    (fun j => (y j : ℝ) / 3) ∉ integerHull (poly A7 bv cv lv uv) := by
  intro h
  have := integerHull_le w₀ 1 int_le h
  simp [w₀, y, Fin.sum_univ_succ] at this
  norm_num at this

end A7Data

/-- **`A7` does not have the Edmonds–Johnson property.** -/
theorem not_hasEJProperty_A7 : ¬ HasEJProperty A7 := fun h =>
  A7Data.z_not_mem_integerHull (h A7Data.bv A7Data.cv A7Data.lv A7Data.uv ▸ A7Data.z_mem_chvatalClosure)

end EdmondsJohnson
