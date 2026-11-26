import Mathlib

/-!
# The non-abelian Gyarmati–Matolcsi–Ruzsa inequality fails in a group of order 2¹⁷

Gyarmati, Matolcsi and Ruzsa (Combinatorica 2010, Problem 1.3) asked whether, for finite nonempty
sets `A₁, …, Aₙ` in an arbitrary group,
`|A₁ ⋯ Aₙ|^(n-1) ≤ ∏ᵢ Nᵢ`, where `Nᵢ = max_{a ∈ Aᵢ} |A₁ ⋯ Aᵢ₋₁ a Aᵢ₊₁ ⋯ Aₙ|`.
Nair–Namayandeh–Zhu (arXiv:2611.00156) disproved this for `n = 4` in `D₄¹⁴`; Elsholtz
(arXiv:2611.12776) found many more counterexamples, the smallest four-set one in a group of order
`518 400`, and a class-two `2`-group of order `2²³` (his Theorem 6.7).

Here we give a four-set (hence, padding with `{1}`, also five-set) counterexample in a class-two group of order `2¹⁷ = 131 072`.
It is Elsholtz's sparse single-coordinate template (his Proposition 6.8) with the incidence pattern
"three disjoint full `3 × 3` blocks", realised with each block using only a `2`-dimensional space
of rows and of columns:

* `V = 𝔽₂⁶`, `W = 𝔽₂⁵`, and a bilinear map `ω : V × V → W`, block diagonal in three `2 × 2` blocks.
* `G = V × V × W` with `(c, b, w) (c', b', w') = (c + c', b + b', w + w' + ω b c')`.
* `A = {(c,0,0)}`, `D = {(0,b,0)}` (two subgroups of order `64`),
  `B = {(0,y,0) : y ∈ Bs}`, `C = {(z,0,0) : z ∈ Bs}`, where `Bs` (10 vectors) is `0` together with
  the three nonzero vectors of each of the three coordinate planes.
* The 27 labels `ω y z` (`y, z` nonzero in the same plane) are distinct and nonzero.

Then `|ABCD| = 64·64·28`, `N₂, N₃ ≤ 64·64·4`, `N₁, N₄ ≤ 64·37`, and
`(64²·28)³ > (64·37)²·(64²·4)²` (the ratio is `28³ / (37²·16) = 1372/1369`).

Main results: `not_nonAbelianGMR` and `exists_counterexample_card`.
-/

namespace OpenProblemsLab.GMR


open Finset Pointwise

/-! ### The statement -/

/-- `Nᵢ`: the largest product obtained by replacing `Aᵢ` with one of its elements. -/
def sliceMax {G : Type} [Group G] [DecidableEq G] {n : ℕ} (A : Fin n → Finset G) (i : Fin n) :
    ℕ :=
  (A i).sup fun a => (List.ofFn (Function.update A i {a})).prod.card

/-- The non-abelian Gyarmati–Matolcsi–Ruzsa inequality (GMR 2010, Problem 1.3), for all groups
and all `n`. -/
def NonAbelianGMR : Prop :=
  ∀ (G : Type) [Group G] [DecidableEq G] (n : ℕ) (A : Fin n → Finset G),
    (∀ i, (A i).Nonempty) → (List.ofFn A).prod.card ^ (n - 1) ≤ ∏ i, sliceMax A i

/-! ### The group -/

/-- `𝔽₂⁶`. -/
abbrev V := Fin 6 → ZMod 2
/-- `𝔽₂⁵`. -/
abbrev W := Fin 5 → ZMod 2

/-- The `5`-bit vector with binary digits of `n`. -/
def bits (n : ℕ) : W := fun k => ((n / 2 ^ k.val % 2 : ℕ) : ZMod 2)

/-- `ω` on basis vectors: three `2 × 2` blocks on coordinates `{0,1}, {2,3}, {4,5}`. -/
def T : Fin 6 → Fin 6 → W :=
  ![![bits 2, bits 5, 0, 0, 0, 0],
    ![bits 8, bits 12, 0, 0, 0, 0],
    ![0, 0, bits 6, bits 17, 0, 0],
    ![0, 0, bits 19, bits 11, 0, 0],
    ![0, 0, 0, 0, bits 1, bits 28],
    ![0, 0, 0, 0, bits 30, bits 14]]

/-- The bilinear map `ω : V × V → W`. -/
def ω (y z : V) : W := ∑ i, ∑ j, (y i * z j) • T i j

lemma ω_add_left (y y' z : V) : ω (y + y') z = ω y z + ω y' z := by
  simp only [ω, Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib]

lemma ω_add_right (y z z' : V) : ω y (z + z') = ω y z + ω y z' := by
  simp only [ω, Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]

@[simp] lemma ω_zero_left (z : V) : ω 0 z = 0 := by simp [ω]

@[simp] lemma ω_zero_right (y : V) : ω y 0 = 0 := by simp [ω]

lemma ω_neg_left (y z : V) : ω (-y) z = -ω y z := by
  have h := ω_add_left y (-y) z
  rw [add_neg_cancel, ω_zero_left] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- Elements of the class-two group `V × V × W`. -/
@[ext] structure H where
  c : V
  b : V
  w : W
  deriving DecidableEq

/-- `H ≃ V × V × W`. -/
def H.equiv : H ≃ V × V × W where
  toFun g := (g.c, g.b, g.w)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype H := Fintype.ofEquiv _ H.equiv.symm

/-- The multiplication `(c, b, w) (c', b', w') = (c + c', b + b', w + w' + ω b c')`. -/
def hmul (g h : H) : H := ⟨g.c + h.c, g.b + h.b, g.w + h.w + ω g.b h.c⟩
/-- The identity `(0, 0, 0)`. -/
def hone : H := ⟨0, 0, 0⟩
/-- The inverse `(c, b, w)⁻¹ = (-c, -b, -w + ω b c)`. -/
def hinv (g : H) : H := ⟨-g.c, -g.b, -g.w + ω g.b g.c⟩

/-- All of `*`, `1`, `⁻¹` on `H` come from this one instance (this keeps kernel checks cheap). -/
instance : Group H where
  mul := hmul
  one := hone
  inv := hinv
  mul_assoc a b c := by
    ext : 1
    · show a.c + b.c + c.c = a.c + (b.c + c.c); abel
    · show a.b + b.b + c.b = a.b + (b.b + c.b); abel
    · show a.w + b.w + ω a.b b.c + c.w + ω (a.b + b.b) c.c
        = a.w + (b.w + c.w + ω b.b c.c) + ω a.b (b.c + c.c)
      rw [ω_add_left, ω_add_right]; abel
  one_mul a := by
    ext : 1
    · show 0 + a.c = a.c; simp
    · show 0 + a.b = a.b; simp
    · show 0 + a.w + ω 0 a.c = a.w; simp
  mul_one a := by
    ext : 1
    · show a.c + 0 = a.c; simp
    · show a.b + 0 = a.b; simp
    · show a.w + 0 + ω a.b 0 = a.w; simp
  inv_mul_cancel a := by
    ext : 1
    · show -a.c + a.c = 0; simp
    · show -a.b + a.b = 0; simp
    · show -a.w + ω a.b a.c + a.w + ω (-a.b) a.c = 0
      rw [ω_neg_left]; abel

@[simp] lemma mul_c (g h : H) : (g * h).c = g.c + h.c := rfl
@[simp] lemma mul_b (g h : H) : (g * h).b = g.b + h.b := rfl
@[simp] lemma mul_w (g h : H) : (g * h).w = g.w + h.w + ω g.b h.c := rfl
@[simp] lemma one_c : (1 : H).c = 0 := rfl
@[simp] lemma one_b : (1 : H).b = 0 := rfl
@[simp] lemma one_w : (1 : H).w = 0 := rfl

lemma card_H : Fintype.card H = 131072 := by
  rw [Fintype.card_congr H.equiv]; simp [Fintype.card_prod, Fintype.card_pi, ZMod.card]

/-! ### The four sets -/

/-- `0` and the three nonzero vectors of each coordinate plane `{0,1}, {2,3}, {4,5}`. -/
def Bs : Finset V :=
  {![0, 0, 0, 0, 0, 0],
   ![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0],
   ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 0, 0],
   ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 1]}

def A : Finset H := univ.image fun c => ⟨c, 0, 0⟩
def B : Finset H := Bs.image fun y => ⟨0, y, 0⟩
def C : Finset H := Bs.image fun z => ⟨z, 0, 0⟩
def D : Finset H := univ.image fun b => ⟨0, b, 0⟩

/-- All labels `ω y z`. -/
def labels : Finset W := (Bs ×ˢ Bs).image fun p => ω p.1 p.2
/-- Labels in row `y`. -/
def row (y : V) : Finset W := Bs.image fun z => ω y z
/-- Labels in column `z`. -/
def col (z : V) : Finset W := Bs.image fun y => ω y z
/-- Pairs (column, label). -/
def colPairs : Finset (V × W) := (Bs ×ˢ Bs).image fun p => (p.2, ω p.1 p.2)
/-- Pairs (row, label). -/
def rowPairs : Finset (V × W) := (Bs ×ˢ Bs).image fun p => (p.1, ω p.1 p.2)

/-! ### The finite label computations -/

lemma card_labels : labels.card = 28 := by decide +kernel
lemma card_row_le : ∀ y ∈ Bs, (row y).card ≤ 4 := by decide +kernel
lemma card_col_le : ∀ z ∈ Bs, (col z).card ≤ 4 := by decide +kernel
lemma card_colPairs : colPairs.card = 37 := by decide +kernel
lemma card_rowPairs : rowPairs.card = 37 := by decide +kernel

lemma zero_mem_Bs : (0 : V) ∈ Bs := by decide +kernel

attribute [irreducible] T ω Bs labels row col colPairs rowPairs

/-! ### Membership in the four sets -/

lemma mem_A {g : H} : g ∈ A ↔ g.b = 0 ∧ g.w = 0 := by
  simp only [A, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩; simp
  · rintro ⟨hb, hw⟩; exact ⟨g.c, by ext <;> simp [hb, hw]⟩

lemma mem_B {g : H} : g ∈ B ↔ g.c = 0 ∧ g.b ∈ Bs ∧ g.w = 0 := by
  simp only [B, mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; simp [hy]
  · rintro ⟨hc, hb, hw⟩; exact ⟨g.b, hb, by ext <;> simp [hc, hw]⟩

lemma mem_C {g : H} : g ∈ C ↔ g.c ∈ Bs ∧ g.b = 0 ∧ g.w = 0 := by
  simp only [C, mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩; simp [hz]
  · rintro ⟨hc, hb, hw⟩; exact ⟨g.c, hc, by ext <;> simp [hb, hw]⟩

lemma mem_D {g : H} : g ∈ D ↔ g.c = 0 ∧ g.w = 0 := by
  simp only [D, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨b, rfl⟩; simp
  · rintro ⟨hc, hw⟩; exact ⟨g.b, by ext <;> simp [hc, hw]⟩

lemma mem_mul4 {X Y Z U : Finset H} {g : H} :
    g ∈ X * (Y * (Z * (U * 1))) ↔ ∃ x ∈ X, ∃ y ∈ Y, ∃ z ∈ Z, ∃ u ∈ U, x * (y * (z * u)) = g := by
  simp only [mul_one, mem_mul]
  constructor
  · rintro ⟨x, hx, _, ⟨y, hy, _, ⟨z, hz, u, hu, rfl⟩, rfl⟩, rfl⟩
    exact ⟨x, hx, y, hy, z, hz, u, hu, rfl⟩
  · rintro ⟨x, hx, y, hy, z, hz, u, hu, rfl⟩
    exact ⟨x, hx, _, ⟨y, hy, _, ⟨z, hz, u, hu, rfl⟩, rfl⟩, rfl⟩

/-! ### Counting sets of the form "all `c`, all `b`, `w` restricted" -/

/-- `mk (c, b, w) = ⟨c, b, w⟩`. -/
def mk (p : V × V × W) : H := ⟨p.1, p.2.1, p.2.2⟩

lemma mk_injective : Function.Injective mk := fun p q h => by
  simp only [mk, H.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact Prod.ext h1 (Prod.ext h2 h3)

lemma card_V : Fintype.card V = 64 := by simp [Fintype.card_pi, ZMod.card]

lemma card_box (R : Finset W) : ((univ ×ˢ univ ×ˢ R).image mk).card = 64 * 64 * R.card := by
  rw [card_image_of_injective _ mk_injective, card_product, card_product, card_univ, card_V,
    mul_assoc]

/-- `(c, w)` restricted to `P`, `b` free. -/
def mkCW (p : (V × W) × V) : H := ⟨p.1.1, p.2, p.1.2⟩
/-- `(b, w)` restricted to `P`, `c` free. -/
def mkBW (p : (V × W) × V) : H := ⟨p.2, p.1.1, p.1.2⟩

lemma card_cw_le (P : Finset (V × W)) : ((P ×ˢ univ).image mkCW).card ≤ P.card * 64 := by
  refine (card_image_le).trans ?_; rw [card_product, card_univ, card_V]

lemma card_bw_le (P : Finset (V × W)) : ((P ×ˢ univ).image mkBW).card ≤ P.card * 64 := by
  refine (card_image_le).trans ?_; rw [card_product, card_univ, card_V]

/-! ### The product set and the four slices -/

/-- `ABCD ⊇ V × V × labels`. -/
lemma box_labels_subset : (univ ×ˢ univ ×ˢ labels).image mk ⊆ A * (B * (C * (D * 1))) := by
  intro g hg
  rw [mem_image] at hg
  obtain ⟨⟨u, v, l⟩, hp, hg⟩ := hg
  subst hg
  have hl : l ∈ labels := (mem_product.1 (mem_product.1 hp).2).2
  rw [labels, mem_image] at hl
  obtain ⟨⟨y, z⟩, hyz, hl⟩ := hl
  rw [mem_product] at hyz
  rw [mem_mul4]
  refine ⟨⟨u - z, 0, 0⟩, mem_A.2 ⟨rfl, rfl⟩, ⟨0, y, 0⟩, mem_B.2 ⟨rfl, hyz.1, rfl⟩,
    ⟨z, 0, 0⟩, mem_C.2 ⟨hyz.2, rfl, rfl⟩, ⟨0, v - y, 0⟩, mem_D.2 ⟨rfl, rfl⟩, ?_⟩
  simp only [mk] at hl ⊢
  ext : 1
  · simp
  · simp
  · simp [← hl]

lemma card_S : 64 * 64 * 28 ≤ (A * (B * (C * (D * 1)))).card := by
  rw [← card_labels, ← card_box]; exact card_le_card box_labels_subset

/-- `N₂`: fixing `b = (0, y, 0)` leaves only the labels of row `y`. -/
lemma slice2_le {b : H} (hb : b ∈ B) : (A * ({b} * (C * (D * 1)))).card ≤ 64 * 64 * 4 := by
  obtain ⟨hbc, hbB, hbw⟩ := mem_B.1 hb
  refine le_trans (card_le_card (t := (univ ×ˢ univ ×ˢ row b.b).image mk) ?_) ?_
  · intro g hg
    obtain ⟨x, hx, b', hb', z, hz, u, hu, rfl⟩ := mem_mul4.1 hg
    rw [mem_singleton] at hb'; subst hb'
    obtain ⟨hxb, hxw⟩ := mem_A.1 hx
    obtain ⟨hzc, hzb, hzw⟩ := mem_C.1 hz
    obtain ⟨huc, huw⟩ := mem_D.1 hu
    refine mem_image.2 ⟨(x.c + z.c, b'.b + u.b, ω b'.b z.c), ?_, ?_⟩
    · simp only [mem_product, mem_univ, true_and, row, mem_image]; exact ⟨z.c, hzc, rfl⟩
    · ext : 1 <;> simp [mk, hbc, hbw, hxb, hxw, hzb, hzw, huc, huw]
  · rw [card_box]; exact Nat.mul_le_mul_left _ (card_row_le _ hbB)

/-- `N₃`: fixing `c = (z, 0, 0)` leaves only the labels of column `z`. -/
lemma slice3_le {c : H} (hc : c ∈ C) : (A * (B * ({c} * (D * 1)))).card ≤ 64 * 64 * 4 := by
  obtain ⟨hcB, hcb, hcw⟩ := mem_C.1 hc
  refine le_trans (card_le_card (t := (univ ×ˢ univ ×ˢ col c.c).image mk) ?_) ?_
  · intro g hg
    obtain ⟨x, hx, y, hy, c', hc', u, hu, rfl⟩ := mem_mul4.1 hg
    rw [mem_singleton] at hc'; subst hc'
    obtain ⟨hxb, hxw⟩ := mem_A.1 hx
    obtain ⟨hyc, hyB, hyw⟩ := mem_B.1 hy
    obtain ⟨huc, huw⟩ := mem_D.1 hu
    refine mem_image.2 ⟨(x.c + c'.c, y.b + u.b, ω y.b c'.c), ?_, ?_⟩
    · simp only [mem_product, mem_univ, true_and, col, mem_image]; exact ⟨y.b, hyB, rfl⟩
    · ext : 1 <;> simp [mk, hcb, hcw, hxb, hxw, hyc, hyw, huc, huw]
  · rw [card_box]; exact Nat.mul_le_mul_left _ (card_col_le _ hcB)

/-- `N₁ = |{a}BCD|`: elements are determined by `b` (free) and a pair (column, label). -/
lemma slice1_le {a : H} (ha : a ∈ A) : ({a} * (B * (C * (D * 1)))).card ≤ 37 * 64 := by
  obtain ⟨hab, haw⟩ := mem_A.1 ha
  refine le_trans (card_le_card (t := ((colPairs.image fun p => (a.c + p.1, p.2)) ×ˢ univ).image
    mkCW) ?_) ?_
  · intro g hg
    obtain ⟨a', ha', y, hy, z, hz, u, hu, rfl⟩ := mem_mul4.1 hg
    rw [mem_singleton] at ha'; subst ha'
    obtain ⟨hyc, hyB, hyw⟩ := mem_B.1 hy
    obtain ⟨hzc, hzb, hzw⟩ := mem_C.1 hz
    obtain ⟨huc, huw⟩ := mem_D.1 hu
    refine mem_image.2 ⟨((a'.c + z.c, ω y.b z.c), y.b + u.b), ?_, ?_⟩
    · simp only [mem_product, mem_univ, and_true, mem_image, colPairs]
      exact ⟨(z.c, ω y.b z.c), ⟨(y.b, z.c), by simp [hyB, hzc], rfl⟩, rfl⟩
    · ext : 1 <;> simp [mkCW, hab, haw, hyc, hyw, hzb, hzw, huc, huw]
  · refine (card_cw_le _).trans (Nat.mul_le_mul_right _ ?_)
    exact card_image_le.trans card_colPairs.le

/-- `N₄ = |ABC{d}|`: elements are determined by `c` (free) and a pair (row, label). -/
lemma slice4_le {d : H} (hd : d ∈ D) : (A * (B * (C * ({d} * 1)))).card ≤ 37 * 64 := by
  obtain ⟨hdc, hdw⟩ := mem_D.1 hd
  refine le_trans (card_le_card (t := ((rowPairs.image fun p => (p.1 + d.b, p.2)) ×ˢ univ).image
    mkBW) ?_) ?_
  · intro g hg
    obtain ⟨x, hx, y, hy, z, hz, d', hd', rfl⟩ := mem_mul4.1 hg
    rw [mem_singleton] at hd'; subst hd'
    obtain ⟨hxb, hxw⟩ := mem_A.1 hx
    obtain ⟨hyc, hyB, hyw⟩ := mem_B.1 hy
    obtain ⟨hzc, hzb, hzw⟩ := mem_C.1 hz
    refine mem_image.2 ⟨((y.b + d'.b, ω y.b z.c), x.c + z.c), ?_, ?_⟩
    · simp only [mem_product, mem_univ, and_true, mem_image, rowPairs]
      exact ⟨(y.b, ω y.b z.c), ⟨(y.b, z.c), by simp [hyB, hzc], rfl⟩, rfl⟩
    · ext : 1 <;> simp [mkBW, hdc, hdw, hxb, hxw, hyc, hyw, hzb, hzw]
  · refine (card_bw_le _).trans (Nat.mul_le_mul_right _ ?_)
    exact card_image_le.trans card_rowPairs.le

/-! ### The counterexample -/

/-- The four sets, as a family indexed by `Fin 4`. -/
def F : Fin 4 → Finset H := ![A, B, C, D]

lemma F_nonempty : ∀ i, (F i).Nonempty := by
  intro i
  fin_cases i
  · exact ⟨1, mem_A.2 ⟨rfl, rfl⟩⟩
  · exact ⟨1, mem_B.2 ⟨rfl, zero_mem_Bs, rfl⟩⟩
  · exact ⟨1, mem_C.2 ⟨zero_mem_Bs, rfl, rfl⟩⟩
  · exact ⟨1, mem_D.2 ⟨rfl, rfl⟩⟩

lemma ofFn_F : (List.ofFn F).prod = A * (B * (C * (D * 1))) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]; rfl

lemma ofFn_F0 (a : H) : (List.ofFn (Function.update F 0 {a})).prod = {a} * (B * (C * (D * 1))) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]; rfl

lemma ofFn_F1 (b : H) : (List.ofFn (Function.update F 1 {b})).prod = A * ({b} * (C * (D * 1))) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]; rfl

lemma ofFn_F2 (c : H) : (List.ofFn (Function.update F 2 {c})).prod = A * (B * ({c} * (D * 1))) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]; rfl

lemma ofFn_F3 (d : H) : (List.ofFn (Function.update F 3 {d})).prod = A * (B * (C * ({d} * 1))) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]; rfl

/-- The final arithmetic: `(37·64)²·(64²·4)² < (64²·28)³`. Stated for an arbitrary `f` so that
the kernel never has to compute the actual slice sizes. -/
lemma arith (f : Fin 4 → ℕ) (s : ℕ) (hs : 64 * 64 * 28 ≤ s) (h0 : f 0 ≤ 37 * 64)
    (h1 : f 1 ≤ 64 * 64 * 4) (h2 : f 2 ≤ 64 * 64 * 4) (h3 : f 3 ≤ 37 * 64) :
    ∏ i, f i < s ^ (4 - 1) := by
  rw [Fin.prod_univ_four]
  calc f 0 * f 1 * f 2 * f 3 ≤ (37 * 64) * (64 * 64 * 4) * (64 * 64 * 4) * (37 * 64) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2) h3
    _ < (64 * 64 * 28) ^ (4 - 1) := by norm_num
    _ ≤ s ^ (4 - 1) := Nat.pow_le_pow_left hs _

/-- The four sets violate the inequality: `|ABCD|³ > N₁N₂N₃N₄`. -/
theorem counterexample :
    ∏ i, sliceMax F i < (List.ofFn F).prod.card ^ (4 - 1) := by
  have hS : 64 * 64 * 28 ≤ (List.ofFn F).prod.card := by rw [ofFn_F]; exact card_S
  have h0 : sliceMax F 0 ≤ 37 * 64 :=
    Finset.sup_le fun a ha => by rw [ofFn_F0]; exact slice1_le ha
  have h1 : sliceMax F 1 ≤ 64 * 64 * 4 :=
    Finset.sup_le fun b hb => by rw [ofFn_F1]; exact slice2_le hb
  have h2 : sliceMax F 2 ≤ 64 * 64 * 4 :=
    Finset.sup_le fun c hc => by rw [ofFn_F2]; exact slice3_le hc
  have h3 : sliceMax F 3 ≤ 37 * 64 :=
    Finset.sup_le fun d hd => by rw [ofFn_F3]; exact slice4_le hd
  exact arith (sliceMax F) _ hS h0 h1 h2 h3

/-- Stated on variables, so the kernel never evaluates the actual cardinalities. -/
lemma absurd_aux (x y : ℕ) (h1 : x ≤ y) (h2 : y < x) : False := absurd h1 (not_le.2 h2)

/-- **The non-abelian Gyarmati–Matolcsi–Ruzsa inequality is false.** -/
theorem not_nonAbelianGMR : ¬ NonAbelianGMR := fun h =>
  absurd_aux _ _ (h H 4 F F_nonempty) counterexample

/-- A four-set counterexample exists in a group of order `2¹⁷ = 131 072`. -/
theorem exists_counterexample_card :
    ∃ (G : Type) (_ : Group G) (_ : DecidableEq G) (_ : Fintype G) (A : Fin 4 → Finset G),
      Fintype.card G = 131072 ∧ (∀ i, (A i).Nonempty) ∧
      ∏ i, sliceMax A i < (List.ofFn A).prod.card ^ (4 - 1) :=
  ⟨H, instGroupH, instDecidableEqH, instFintypeH, F, card_H, F_nonempty, counterexample⟩

end OpenProblemsLab.GMR
