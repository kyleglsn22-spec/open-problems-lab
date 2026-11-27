import Mathlib
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.List

/-!
# The Partial List Colouring Conjecture is false

Let `G` be a finite graph on `n` vertices with list chromatic number (choice number) `k ≥ 2`, and
let `1 ≤ ℓ < k`. The **Partial List Colouring Conjecture** (Albertson–Grossman–Haas, Discrete
Math. 214 (2000)) says that for every assignment `L` of lists of `ℓ` colours to the vertices, at
least `n · ℓ / k` vertices can be properly coloured from their lists.

Noel (arXiv:2609.23291, Sep 2026, Theorem 1) disproves it with `k = 3`, `ℓ = 2`, `n = 14`: a graph
`G` with `χ_ℓ(G) = 3` and a 2-list assignment from which at most `9 < 28/3` vertices can be
properly coloured. We formalize his proof:

* `listChromaticNumber_G : G.listChromaticNumber = 3`;
* `partial_le_nine`: every proper partial colouring from Noel's lists colours at most 9 vertices;
* `not_partialListColouringConjecture`: the conjecture is false.

We use `SimpleGraph.IsKChoosable` and `SimpleGraph.listChromaticNumber` from DeepMind's
formal-conjectures (pinned commit). `IsKChoosable G k` asks for lists of exactly `k` colours from
`ℕ`, and `listChromaticNumber G = sInf {k | G.IsKChoosable k}`.

## The graph (vertices are `Fin 14`)

* `0` and `1` are the terminals `s₁`, `s₂` (not adjacent);
* triangle `Tᵢ` (`i = 0,1,2,3`) has vertices `3i+2` (the private vertex `pᵢ`), `3i+3`, `3i+4`;
* both terminals are joined to the two non-private vertices of every triangle.

Noel's lists: `L(s₁) = {1,2}`, `L(s₂) = {3,4}`, and the triangles get `{1,3}`, `{1,4}`, `{2,3}`,
`{2,4}` (every list on `Tᵢ` is the same).

## Proof (following the paper)

1. At most 9 vertices: a triangle with a 2-list has at most 2 coloured vertices; if both terminals
   are coloured, the triangle whose list is `{c(s₁), c(s₂)}` has no coloured non-private vertex.
2. `G` is 3-choosable: pick colours `c ∈ L(s₁)`, `d ∈ L(s₂)` such that no triangle's first
   non-private vertex has both `c` and `d` in its list (if the lists of `s₁, s₂` meet, take
   `c = d`; otherwise count: at most `4 · 2 = 8` of the `9` pairs are bad). Then colour each
   triangle greedily.
3. `G` contains a triangle, so it is not 2-choosable.
-/

namespace OpenProblemsLab.PartialList

open Finset SimpleGraph

/-! ### The conjecture -/

/-- **The Partial List Colouring Conjecture** (Albertson–Grossman–Haas 2000): for a finite graph
`G` on `n` vertices with list chromatic number `k` and `1 ≤ ℓ < k`, for every assignment `L` of
lists of `ℓ` colours, some set `S` of at least `n ℓ / k` vertices can be properly coloured from
the lists (written without division: `n · ℓ ≤ |S| · k`). -/
def PartialListColouringConjecture : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (ℓ : ℕ), 1 ≤ ℓ → ℓ < G.listChromaticNumber →
    ∀ L : V → Finset ℕ, (∀ v, (L v).card = ℓ) →
      ∃ S : Finset V, ∃ c : V → ℕ, (∀ v ∈ S, c v ∈ L v) ∧
        (∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v) ∧
        Fintype.card V * ℓ ≤ S.card * G.listChromaticNumber

/-! ### The graph -/

/-- Adjacency, as a Boolean function. -/
def adjB (u v : Fin 14) : Bool :=
  if u.val < 2 then decide (2 ≤ v.val) && decide ((v.val - 2) % 3 ≠ 0)
  else if v.val < 2 then decide ((u.val - 2) % 3 ≠ 0)
  else decide (u ≠ v) && decide ((u.val - 2) / 3 = (v.val - 2) / 3)

/-- Noel's graph: four triangles and two terminals joined to the non-private triangle
vertices. -/
def G : SimpleGraph (Fin 14) where
  Adj u v := adjB u v = true
  symm := by
    refine ⟨?_⟩
    intro u v
    revert u v
    decide
  loopless := by
    refine ⟨?_⟩
    intro v
    revert v
    decide

instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (adjB u v = true))

/-- The edge list, for the reader (and checked): 4 triangles (12 edges) and 16 terminal
edges. -/
theorem G_edges : ∀ u v : Fin 14, G.Adj u v ↔
    ((u.val < 2 ∧ 2 ≤ v.val ∧ (v.val - 2) % 3 ≠ 0) ∨ (v.val < 2 ∧ 2 ≤ u.val ∧ (u.val - 2) % 3 ≠ 0)
      ∨ (2 ≤ u.val ∧ 2 ≤ v.val ∧ u ≠ v ∧ (u.val - 2) / 3 = (v.val - 2) / 3)) := by
  decide

/-- Noel's 2-list assignment. -/
def Ln (v : Fin 14) : Finset ℕ :=
  if v.val = 0 then {1, 2} else if v.val = 1 then {3, 4}
  else {1 + (v.val - 2) / 3 / 2, 3 + (v.val - 2) / 3 % 2}

theorem Ln_card : ∀ v, (Ln v).card = 2 := by decide

/-! ### At most 9 vertices can be coloured from Noel's lists -/

section Partial

variable {S : Finset (Fin 14)} {c : Fin 14 → ℕ}

/-- Three elements of a 2-element set: two of them coincide. -/
theorem two_pigeon {T : Finset ℕ} (hT : T.card = 2) {x y z : ℕ} (hx : x ∈ T) (hy : y ∈ T)
    (hz : z ∈ T) : x = y ∨ x = z ∨ y = z := by
  by_contra hne
  push Not at hne
  obtain ⟨hxy, hxz, hyz⟩ := hne
  have hsub : ({x, y, z} : Finset ℕ) ⊆ T := by
    intro q hq; simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [card_insert_of_notMem (by simp [hxy, hxz]), card_insert_of_notMem (by simp [hyz]),
    card_singleton] at this
  omega

/-- Indicator of `v ∈ S`. -/
def ind (S : Finset (Fin 14)) (v : Fin 14) : ℕ := if v ∈ S then 1 else 0

theorem ind_le (v : Fin 14) : ind S v ≤ 1 := by unfold ind; split_ifs <;> omega

theorem ind_eq_one {v : Fin 14} (h : v ∈ S) : ind S v = 1 := by simp [ind, h]

theorem ind_eq_zero {v : Fin 14} (h : v ∉ S) : ind S v = 0 := by simp [ind, h]

theorem card_eq_sum_ind (S : Finset (Fin 14)) : S.card =
    ind S 0 + (ind S 1 + (ind S 2 + (ind S 3 + (ind S 4 + (ind S 5 + (ind S 6 + (ind S 7 +
      (ind S 8 + (ind S 9 + (ind S 10 + (ind S 11 + (ind S 12 + (ind S 13 + 0))))))))))))) := by
  have : S.card = ∑ v : Fin 14, ind S v := by simp [ind]
  rw [this]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]

variable (hL : ∀ v ∈ S, c v ∈ Ln v) (hP : ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v)
include hL hP

/-- A triangle whose three vertices share a 2-list has at most 2 coloured vertices. -/
theorem tri_le (x y z : Fin 14) (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z)
    (h1 : Ln y = Ln x) (h2 : Ln z = Ln x) : ind S x + ind S y + ind S z ≤ 2 := by
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · by_cases hz : z ∈ S
      · exfalso
        have cx := hL x hx
        have cy := hL y hy
        have cz := hL z hz
        rw [h1] at cy
        rw [h2] at cz
        rcases two_pigeon (Ln_card x) cx cy cz with h | h | h
        · exact hP x hx y hy hxy h
        · exact hP x hx z hz hxz h
        · exact hP y hy z hz hyz h
      · have := ind_le (S := S) x; have := ind_le (S := S) y; rw [ind_eq_zero hz]; omega
    · have := ind_le (S := S) x; have := ind_le (S := S) z; rw [ind_eq_zero hy]; omega
  · have := ind_le (S := S) y; have := ind_le (S := S) z; rw [ind_eq_zero hx]; omega

/-- If a non-private vertex `x` with list `{c(s₁), c(s₂)}` is coloured, it clashes with a
terminal. -/
theorem notMem_of_list (hs1 : (0 : Fin 14) ∈ S) (hs2 : (1 : Fin 14) ∈ S) (x : Fin 14)
    (h0 : G.Adj 0 x) (h1 : G.Adj 1 x) (hx : Ln x = {c 0, c 1}) : x ∉ S := by
  intro hxS
  have := hL x hxS
  rw [hx] at this
  simp only [mem_insert, mem_singleton] at this
  rcases this with h | h
  · exact hP 0 hs1 x hxS h0 h.symm
  · exact hP 1 hs2 x hxS h1 h.symm

/-- If both terminals are coloured, both non-private vertices of some triangle are uncoloured. -/
theorem terminals (hs1 : (0 : Fin 14) ∈ S) (hs2 : (1 : Fin 14) ∈ S) :
    (ind S 3 = 0 ∧ ind S 4 = 0) ∨ (ind S 6 = 0 ∧ ind S 7 = 0) ∨ (ind S 9 = 0 ∧ ind S 10 = 0) ∨
      (ind S 12 = 0 ∧ ind S 13 = 0) := by
  have c0 := hL 0 hs1
  have c1 := hL 1 hs2
  have e0 : Ln 0 = {1, 2} := by decide
  have e1 : Ln 1 = {3, 4} := by decide
  rw [e0] at c0
  rw [e1] at c1
  simp only [mem_insert, mem_singleton] at c0 c1
  have key := fun x h0 h1 hx => ind_eq_zero (notMem_of_list hL hP hs1 hs2 x h0 h1 hx)
  rcases c0 with h0 | h0 <;> rcases c1 with h1 | h1
  · left
    exact ⟨key 3 (by decide) (by decide) (by rw [h0, h1]; decide),
      key 4 (by decide) (by decide) (by rw [h0, h1]; decide)⟩
  · right; left
    exact ⟨key 6 (by decide) (by decide) (by rw [h0, h1]; decide),
      key 7 (by decide) (by decide) (by rw [h0, h1]; decide)⟩
  · right; right; left
    exact ⟨key 9 (by decide) (by decide) (by rw [h0, h1]; decide),
      key 10 (by decide) (by decide) (by rw [h0, h1]; decide)⟩
  · right; right; right
    exact ⟨key 12 (by decide) (by decide) (by rw [h0, h1]; decide),
      key 13 (by decide) (by decide) (by rw [h0, h1]; decide)⟩

/-- **At most 9 vertices** of `G` can be properly coloured from Noel's lists. -/
theorem partial_le_nine : S.card ≤ 9 := by
  rw [card_eq_sum_ind]
  have t0 := tri_le hL hP 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have t1 := tri_le hL hP 5 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)
  have t2 := tri_le hL hP 8 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
  have t3 := tri_le hL hP 11 12 13 (by decide) (by decide) (by decide) (by decide) (by decide)
  have b0 := ind_le (S := S) 0
  have b1 := ind_le (S := S) 1
  by_cases hs1 : (0 : Fin 14) ∈ S
  · by_cases hs2 : (1 : Fin 14) ∈ S
    · have := terminals hL hP hs1 hs2
      have := ind_le (S := S) 2; have := ind_le (S := S) 5
      have := ind_le (S := S) 8; have := ind_le (S := S) 11
      omega
    · rw [ind_eq_zero hs2]; omega
  · rw [ind_eq_zero hs1]; omega

end Partial

/-! ### `G` is 3-choosable -/

section Choosable

/-- An element of `s` outside `t`, when `t` is smaller. -/
theorem exists_mem_notMem {s t : Finset ℕ} (h : t.card < s.card) : ∃ x ∈ s, x ∉ t :=
  Finset.exists_mem_notMem_of_card_lt_card h

theorem card_pair_le (a b : ℕ) : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_le_two

/-- Greedy colouring of one triangle `p, u, w` after the terminals took colours `c, d`:
`w` avoids `c, d`; `u` avoids `c, d` and `w`'s colour; `p` avoids the other two. -/
theorem tri_extend {Lp Lu Lw : Finset ℕ} (hp : Lp.card = 3) (hw : Lw.card = 3) {c d : ℕ}
    (hu : 2 ≤ (Lu \ {c, d}).card) :
    ∃ z ∈ Lp, ∃ x ∈ Lu, ∃ y ∈ Lw, y ≠ c ∧ y ≠ d ∧ x ≠ c ∧ x ≠ d ∧ x ≠ y ∧ z ≠ x ∧ z ≠ y := by
  obtain ⟨y, hy, hy'⟩ := exists_mem_notMem (s := Lw) (t := {c, d})
    (by have := card_pair_le c d; omega)
  obtain ⟨x, hx, hx'⟩ := exists_mem_notMem (s := Lu \ {c, d}) (t := {y})
    (by rw [card_singleton]; omega)
  obtain ⟨z, hz, hz'⟩ := exists_mem_notMem (s := Lp) (t := {x, y})
    (by have := card_pair_le x y; omega)
  simp only [mem_insert, mem_singleton, not_or, mem_sdiff] at hy' hx hx' hz'
  exact ⟨z, hz, x, hx.1, y, hy, hy'.1, hy'.2, hx.2.1, hx.2.2, hx', hz'.1, hz'.2⟩

/-- `{x, x} \ ...`: removing one colour from a 3-list leaves at least 2. -/
theorem two_le_sdiff_one {s : Finset ℕ} (hs : s.card = 3) (x : ℕ) : 2 ≤ (s \ {x, x}).card := by
  have := Finset.le_card_sdiff ({x, x} : Finset ℕ) s
  rw [pair_eq_singleton, card_singleton] at this
  rw [pair_eq_singleton]
  omega

/-- Removing two colours `c, d`, not both in `s`, from a 3-list leaves at least 2. -/
theorem two_le_sdiff_two {s : Finset ℕ} (hs : s.card = 3) {c d : ℕ} (h : ¬ (c ∈ s ∧ d ∈ s)) :
    2 ≤ (s \ {c, d}).card := by
  have key := Finset.card_sdiff_add_card_inter s {c, d}
  have : (s ∩ {c, d}).card ≤ 1 := by
    by_cases hc : c ∈ s
    · have hd : d ∉ s := fun hd => h ⟨hc, hd⟩
      calc (s ∩ {c, d}).card ≤ ({c} : Finset ℕ).card := by
            apply card_le_card
            intro q hq
            simp only [mem_inter, mem_insert, mem_singleton] at hq ⊢
            rcases hq with ⟨hq, rfl | rfl⟩
            · rfl
            · exact absurd hq hd
        _ = 1 := card_singleton c
    · calc (s ∩ {c, d}).card ≤ ({d} : Finset ℕ).card := by
            apply card_le_card
            intro q hq
            simp only [mem_inter, mem_insert, mem_singleton] at hq ⊢
            rcases hq with ⟨hq, rfl | rfl⟩
            · exact absurd hq hc
            · rfl
        _ = 1 := card_singleton d
  omega

/-- `a + b ≤ 3` forces `a * b ≤ 2`. -/
theorem mul_le_two {a b : ℕ} (h : a + b ≤ 3) : a * b ≤ 2 := by
  have : a ≤ 3 := by omega
  interval_cases a <;> omega

/-- **Choosing the terminal colours.** There are `c ∈ L 0`, `d ∈ L 1` such that each first
non-private vertex `3, 6, 9, 12` keeps at least 2 colours after removing `c` and `d`. -/
theorem terminal_choice (L : Fin 14 → Finset ℕ) (hL : ∀ v, (L v).card = 3) :
    ∃ c ∈ L 0, ∃ d ∈ L 1, ∀ v ∈ ({3, 6, 9, 12} : Finset (Fin 14)), 2 ≤ (L v \ {c, d}).card := by
  by_cases hi : (L 0 ∩ L 1).Nonempty
  · obtain ⟨x, hx⟩ := hi
    rw [mem_inter] at hx
    exact ⟨x, hx.1, x, hx.2, fun v _ => two_le_sdiff_one (hL v) x⟩
  · rw [not_nonempty_iff_eq_empty] at hi
    -- bad pairs: both colours in the list of one of `3, 6, 9, 12`
    set U : Finset (Fin 14) := {3, 6, 9, 12} with hU
    set bad := U.biUnion (fun v => (L v ∩ L 0) ×ˢ (L v ∩ L 1)) with hbad
    have hcard : bad.card ≤ 8 := by
      calc bad.card ≤ ∑ v ∈ U, ((L v ∩ L 0) ×ˢ (L v ∩ L 1)).card := card_biUnion_le
        _ ≤ ∑ _v ∈ U, 2 := by
            apply sum_le_sum
            intro v _
            rw [card_product]
            apply mul_le_two
            have hdisj : Disjoint (L v ∩ L 0) (L v ∩ L 1) := by
              rw [disjoint_iff_inter_eq_empty]
              ext q
              simp only [mem_inter, notMem_empty, iff_false]
              intro hq
              have : q ∈ L 0 ∩ L 1 := mem_inter.2 ⟨hq.1.2, hq.2.2⟩
              rw [hi] at this
              exact notMem_empty q this
            rw [← card_union_of_disjoint hdisj, ← hL v]
            apply card_le_card
            intro q hq
            simp only [mem_union, mem_inter] at hq
            rcases hq with hq | hq
            · exact hq.1
            · exact hq.1
        _ = 8 := by simp [hU]
    have hall : (L 0 ×ˢ L 1).card = 9 := by rw [card_product, hL 0, hL 1]
    obtain ⟨⟨c, d⟩, hcd, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show bad.card < (L 0 ×ˢ L 1).card by omega)
    rw [mem_product] at hcd
    refine ⟨c, hcd.1, d, hcd.2, fun v hv => two_le_sdiff_two (hL v) ?_⟩
    intro h
    apply hnot
    rw [hbad, mem_biUnion]
    exact ⟨v, hv, mem_product.2 ⟨mem_inter.2 ⟨h.1, hcd.1⟩, mem_inter.2 ⟨h.2, hcd.2⟩⟩⟩

/-- **`G` is 3-choosable** (Noel, second half of the proof of Theorem 1). -/
theorem isKChoosable_three : G.IsKChoosable 3 := by
  intro L hL
  obtain ⟨c, hc, d, hd, hgood⟩ := terminal_choice L hL
  obtain ⟨z0, hz0, x0, hx0, y0, hy0, a0, b0, c0, d0, e0, f0, g0⟩ :=
    tri_extend (hL 2) (hL 4) (hgood 3 (by decide))
  obtain ⟨z1, hz1, x1, hx1, y1, hy1, a1, b1, c1, d1, e1, f1, g1⟩ :=
    tri_extend (hL 5) (hL 7) (hgood 6 (by decide))
  obtain ⟨z2, hz2, x2, hx2, y2, hy2, a2, b2, c2, d2, e2, f2, g2⟩ :=
    tri_extend (hL 8) (hL 10) (hgood 9 (by decide))
  obtain ⟨z3, hz3, x3, hx3, y3, hy3, a3, b3, c3, d3, e3, f3, g3⟩ :=
    tri_extend (hL 11) (hL 13) (hgood 12 (by decide))
  let col : Fin 14 → ℕ := ![c, d, z0, x0, y0, z1, x1, y1, z2, x2, y2, z3, x3, y3]
  refine ⟨Coloring.mk col ?_, ?_⟩
  · intro u v h
    fin_cases u <;> fin_cases v <;>
      first
      | exact absurd h (by decide)
      | (simp only [col, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
         first
         | assumption
         | exact fun e => absurd e.symm ‹_›)
  · intro v
    fin_cases v <;> simpa [col]

end Choosable

/-! ### The list chromatic number is 3 -/

/-- `G` has a triangle, so it is not 2-colourable, hence not `k`-choosable for `k ≤ 2`. -/
theorem not_isKChoosable_of_le_two {k : ℕ} (hk : k ≤ 2) : ¬ G.IsKChoosable k := by
  intro h
  obtain ⟨C⟩ := (IsKChoosable.colorable h).mono hk
  have h23 := C.valid (show G.Adj 2 3 by decide)
  have h24 := C.valid (show G.Adj 2 4 by decide)
  have h34 := C.valid (show G.Adj 3 4 by decide)
  generalize C 2 = p, C 3 = q, C 4 = r at h23 h24 h34
  fin_cases p <;> fin_cases q <;> fin_cases r <;> simp_all

theorem listChromaticNumber_G : G.listChromaticNumber = 3 := by
  apply le_antisymm (Nat.sInf_le isKChoosable_three)
  apply le_csInf ⟨3, isKChoosable_three⟩
  intro k hk
  by_contra h
  exact not_isKChoosable_of_le_two (by omega) hk

/-! ### The disproof -/

/-- **The Partial List Colouring Conjecture is false** (Noel 2026): `G` has 14 vertices and
`χ_ℓ(G) = 3`, but from Noel's 2-lists at most 9 vertices can be properly coloured, and
`9 · 3 = 27 < 28 = 14 · 2`. -/
theorem not_partialListColouringConjecture : ¬ PartialListColouringConjecture := by
  intro h
  obtain ⟨S, c, hL, hP, hcard⟩ := h (Fin 14) G 2 (by norm_num)
    (by rw [listChromaticNumber_G]; norm_num) Ln Ln_card
  have := partial_le_nine hL hP
  rw [listChromaticNumber_G, Fintype.card_fin] at hcard
  omega

/-- The explicit statement: a graph on 14 vertices with list chromatic number 3 and a 2-list
assignment from which every proper partial colouring colours at most 9 vertices. -/
theorem exists_counterexample :
    ∃ H : SimpleGraph (Fin 14), H.listChromaticNumber = 3 ∧
      ∃ L : Fin 14 → Finset ℕ, (∀ v, (L v).card = 2) ∧
        ∀ S : Finset (Fin 14), ∀ c : Fin 14 → ℕ, (∀ v ∈ S, c v ∈ L v) →
          (∀ u ∈ S, ∀ v ∈ S, H.Adj u v → c u ≠ c v) → S.card ≤ 9 :=
  ⟨G, listChromaticNumber_G, Ln, Ln_card, fun _ _ hL hP => partial_le_nine hL hP⟩

end OpenProblemsLab.PartialList
