import Mathlib
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.TotalColouring

/-!
# The List Total Colouring Conjecture is false

A *total colouring* of a graph colours its vertices and edges so that adjacent vertices, edges
sharing an endpoint, and each vertex with its own edges all get different colours. The
*list total chromatic number* `χ''_ℓ(G)` is the least `k` such that whatever list of `k` allowed
colours is given to each vertex and edge, a total colouring from the lists exists.

The **List Total Colouring Conjecture** (Borodin–Kostochka–Woodall 1997, Juvan–Mohar–Škrekovski
1998, Hilton–Johnson 1999) says `χ''_ℓ(G) = χ''(G)` for every multigraph `G`.

Noel (arXiv:2609.38417, 29 Sep 2026, Theorem 1.1) disproves it with a cubic graph on 20 vertices:
four copies `B₀, …, B₃` of `K_{2,3}`, with one *cross edge* between each pair of copies. We
formalize his proof:

* `totalChromaticNumber_G : G.totalChromaticNumber = 4` (an explicit 4-colouring; and 3 colours
  are too few because a vertex and its three edges need 4 different colours);
* `not_totalChoosable_four : ¬ G.TotalChoosable 4`: no total colouring exists
  from Noel's lists of size 4;
* `not_listTotalColouringConjecture`: the conjecture (even restricted to simple graphs) is false.

We use the definitions `SimpleGraph.IsTotalColoring`, `SimpleGraph.TotalColorable` and
`SimpleGraph.totalChromaticNumber` from DeepMind's formal-conjectures (pinned commit). The list
version (`TotalChoosable`, `listTotalChromaticNumber`) is defined here in the same style. Noel also
notes `χ''_ℓ(G) = 5` using a theorem of Juvan–Mohar–Škrekovski (cubic graphs are totally
5-choosable); that upper bound is not needed for the disproof and is not formalized.

## Layout (vertices are `Fin 20`)

Block `i ∈ {0,1,2,3}` has private vertices `a i = 5i`, `b i = 5i+1` and terminals
`t i k = 5i+2+k` (`k : Fin 3`). Terminal `k` of block `i` is joined by a cross edge to block
`j = k` if `k < i`, else `j = k + 1`. In the paper's numbering block `i` is `B_{i+1}`.

Lists (colours `1..5`): every vertex and edge inside block `i` gets `{1,…,5} \ {i+1}`. Cross edges:
`B₁B₂ ↦ ∖{3}`, `B₁B₃ ↦ ∖{5}`, `B₁B₄ ↦ ∖{2}`, `B₂B₃ ↦ ∖{4}`, `B₂B₄ ↦ ∖{5}`, `B₃B₄ ↦ ∖{1}`
(paper's numbering).

## Proof (following the paper)

1. `k23_private_eq` (Lemma 2.1): in a total colouring of `K_{2,3}` from 4 colours the two private
   vertices get the same colour `s`.
2. `cross_mem`: then each cross edge leaving block `i` has colour `i+1` or `s`, since the terminal,
   its two block edges, and `s` use up the other colours.
3. `final`: a finite check over the four values `s₀, …, s₃` (decided by the kernel) shows some cross
   edge has no allowed colour.
-/

namespace OpenProblemsLab.ListTotal

open Finset SimpleGraph

/-! ### List total colourings -/

section Defs

variable {V : Type*} (G : SimpleGraph V)

/-- `G` is **totally `k`-choosable** if for every assignment of lists of at least `k` colours
(natural numbers) to the vertices and edges, there is a total colouring choosing each colour from
its list. -/
def _root_.SimpleGraph.TotalChoosable (k : ℕ) : Prop :=
  ∀ L : V ⊕ G.edgeSet → Finset ℕ, (∀ x, k ≤ (L x).card) →
    ∃ c : V ⊕ G.edgeSet → ℕ, (∀ x, c x ∈ L x) ∧ G.IsTotalColoring c

/-- The **list total chromatic number** `χ''_ℓ(G)`: the least `k` with `G` totally `k`-choosable. -/
noncomputable def _root_.SimpleGraph.listTotalChromaticNumber : ℕ :=
  sInf {k | G.TotalChoosable k}

end Defs

/-- **The List Total Colouring Conjecture**, for finite simple graphs: `χ''_ℓ(G) = χ''(G)`.
(The original conjecture is for multigraphs; a simple graph is a special case, so a simple
counterexample refutes it.) -/
def ListTotalColouringConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.listTotalChromaticNumber = G.totalChromaticNumber

/-! ### The graph -/

/-- Block of a vertex. -/
def blk (v : Fin 20) : ℕ := v.val / 5

/-- Private vertices and terminals of block `i`. -/
def a (i : Fin 4) : Fin 20 := ⟨5 * i.val, by omega⟩
def b (i : Fin 4) : Fin 20 := ⟨5 * i.val + 1, by omega⟩
def t (i : Fin 4) (k : Fin 3) : Fin 20 := ⟨5 * i.val + 2 + k.val, by omega⟩

/-- The block that terminal `k` of block `i` points to. -/
def tgt (i : Fin 4) (k : Fin 3) : ℕ := if k.val < i.val then k.val else k.val + 1

/-- The terminal of block `j` that points to block `i`. -/
def idx (j i : ℕ) : ℕ := if i < j then i else i - 1

/-- Adjacency, as a Boolean function. -/
def adjB (u v : Fin 20) : Bool :=
  let i := u.val / 5; let p := u.val % 5
  let j := v.val / 5; let q := v.val % 5
  if i = j then (decide (p < 2) && decide (2 ≤ q)) || (decide (q < 2) && decide (2 ≤ p))
  else decide (2 ≤ p) && decide (2 ≤ q) && decide (j = (if p - 2 < i then p - 2 else p - 1)) &&
    decide (i = (if q - 2 < j then q - 2 else q - 1))

/-- Noel's graph: four copies of `K_{2,3}` joined pairwise by single cross edges. -/
def G : SimpleGraph (Fin 20) where
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

/-- The graph is cubic. -/
theorem G_cubic : ∀ v : Fin 20, ((Finset.univ : Finset (Fin 20)).filter (G.Adj v)).card = 3 := by
  decide

/-- Partner of terminal `k` of block `i` across its cross edge. -/
def partner (i : Fin 4) (k : Fin 3) : Fin 20 :=
  ⟨5 * tgt i k + 2 + idx (tgt i k) i.val, by
    unfold tgt idx; split_ifs <;> omega⟩

theorem adj_a_t : ∀ i k, G.Adj (a i) (t i k) := by decide
theorem adj_b_t : ∀ i k, G.Adj (b i) (t i k) := by decide
theorem adj_t_p : ∀ i k, G.Adj (t i k) (partner i k) := by decide

/-! ### Basic facts about total colourings -/

section Facts

variable {V : Type*} {H : SimpleGraph V} {ι : Type*} {c : V ⊕ H.edgeSet → ι}

/-- The edge `uv` as an element of `H.edgeSet`. -/
def ed (H : SimpleGraph V) {u v : V} (h : H.Adj u v) : H.edgeSet := ⟨s(u, v), h⟩

theorem tc_vv (hc : H.IsTotalColoring c) {u v : V} (h : H.Adj u v) :
    c (Sum.inl u) ≠ c (Sum.inl v) := hc.1 u v h

theorem tc_ve_left (hc : H.IsTotalColoring c) {u v : V} (h : H.Adj u v) :
    c (Sum.inl u) ≠ c (Sum.inr (ed H h)) := hc.2.2 u _ (Sym2.mem_mk_left u v)

theorem tc_ve_right (hc : H.IsTotalColoring c) {u v : V} (h : H.Adj u v) :
    c (Sum.inl v) ≠ c (Sum.inr (ed H h)) := hc.2.2 v _ (Sym2.mem_mk_right u v)

/-- Two edges at a common vertex `u` get different colours. -/
theorem tc_ee [DecidableEq V] (hc : H.IsTotalColoring c) {u v w : V} (h₁ : H.Adj u v)
    (h₂ : H.Adj u w) (hvw : v ≠ w) : c (Sum.inr (ed H h₁)) ≠ c (Sum.inr (ed H h₂)) := by
  refine hc.2.1 _ _ ?_ ⟨u, Sym2.mem_mk_left u v, Sym2.mem_mk_left u w⟩
  intro he
  have : s(u, v) = s(u, w) := congrArg Subtype.val he
  rcases Sym2.eq_iff.1 this with ⟨_, h⟩ | ⟨h1, h2⟩
  · exact hvw h
  · exact hvw (h2.trans h1)

/-- Two edges at a common vertex `u`, written with `u` second in the first edge. -/
theorem tc_ee' [DecidableEq V] (hc : H.IsTotalColoring c) {u v w : V} (h₁ : H.Adj v u)
    (h₂ : H.Adj u w) (hvw : v ≠ w) : c (Sum.inr (ed H h₁)) ≠ c (Sum.inr (ed H h₂)) := by
  have e : ed H h₁ = ed H h₁.symm := Subtype.ext (Sym2.eq_swap)
  rw [e]
  exact tc_ee hc h₁.symm h₂ hvw

end Facts

/-! ### Two pigeonhole lemmas -/

/-- Three different elements of a 3-element set fill it. -/
theorem three_fill {S : Finset ℕ} (hS : S.card = 3) {x y z w : ℕ} (hx : x ∈ S) (hy : y ∈ S)
    (hz : z ∈ S) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hw : w ∈ S) :
    w = x ∨ w = y ∨ w = z := by
  have hsub : ({x, y, z} : Finset ℕ) ⊆ S := by
    intro q hq; simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> assumption
  have hcard : S.card ≤ ({x, y, z} : Finset ℕ).card := by
    rw [hS, card_insert_of_notMem (by simp [hxy, hxz]), card_insert_of_notMem (by simp [hyz]),
      card_singleton]
  have := Finset.eq_of_subset_of_card_le hsub hcard
  rw [← this] at hw
  simpa using hw

/-- Three elements of a 2-element set: two of them coincide. -/
theorem two_pigeon {S : Finset ℕ} (hS : S.card = 2) {x y z : ℕ} (hx : x ∈ S) (hy : y ∈ S)
    (hz : z ∈ S) : x = y ∨ x = z ∨ y = z := by
  by_contra hne
  push Not at hne
  obtain ⟨hxy, hxz, hyz⟩ := hne
  have hsub : ({x, y, z} : Finset ℕ) ⊆ S := by
    intro q hq; simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [card_insert_of_notMem (by simp [hxy, hxz]), card_insert_of_notMem (by simp [hyz]),
    card_singleton] at this
  omega

/-! ### Lemma 2.1: `K_{2,3}` -/

/-- One case of Lemma 2.1: terminals `p` and `q` have the same colour `g`; `r` is the third. -/
theorem k23_case {P : Finset ℕ} (hP : P.card = 4) {A B g Xp Xq Xr Yp Yq Yr : ℕ}
    (hA : A ∈ P) (hg : g ∈ P) (hgA : g ≠ A) (hB : B ∈ P) (hgB : g ≠ B)
    (hXp : Xp ∈ P) (hXq : Xq ∈ P) (hXr : Xr ∈ P) (hYp : Yp ∈ P) (hYq : Yq ∈ P) (hYr : Yr ∈ P)
    (hAXp : A ≠ Xp) (hAXq : A ≠ Xq) (hAXr : A ≠ Xr) (hBYp : B ≠ Yp) (hBYq : B ≠ Yq)
    (hBYr : B ≠ Yr)
    (hgXp : g ≠ Xp) (hgXq : g ≠ Xq) (hgYp : g ≠ Yp) (hgYq : g ≠ Yq)
    (hX1 : Xp ≠ Xq) (hX2 : Xp ≠ Xr) (hX3 : Xq ≠ Xr) (hY1 : Yp ≠ Yq) (hY2 : Yp ≠ Yr)
    (hY3 : Yq ≠ Yr) (hXY : Xr ≠ Yr) : False := by
  have hcA : (P.erase A).card = 3 := by rw [card_erase_of_mem hA, hP]
  have hcB : (P.erase B).card = 3 := by rw [card_erase_of_mem hB, hP]
  have h1 := three_fill hcA (mem_erase.2 ⟨hAXp.symm, hXp⟩) (mem_erase.2 ⟨hAXq.symm, hXq⟩)
    (mem_erase.2 ⟨hAXr.symm, hXr⟩) hX1 hX2 hX3 (mem_erase.2 ⟨hgA, hg⟩)
  have h2 := three_fill hcB (mem_erase.2 ⟨hBYp.symm, hYp⟩) (mem_erase.2 ⟨hBYq.symm, hYq⟩)
    (mem_erase.2 ⟨hBYr.symm, hYr⟩) hY1 hY2 hY3 (mem_erase.2 ⟨hgB, hg⟩)
  rcases h1 with h1 | h1 | h1
  · exact hgXp h1
  · exact hgXq h1
  rcases h2 with h2 | h2 | h2
  · exact hgYp h2
  · exact hgYq h2
  exact hXY (h1 ▸ h2 ▸ rfl)

/-- **Lemma 2.1.** In a total colouring of `K_{2,3}` (private vertices `A`, `B`, terminals
`T₀, T₁, T₂`, edges `Xₖ = A Tₖ`, `Yₖ = B Tₖ`) from a 4-colour palette `P`, the two private
vertices get the same colour. -/
theorem k23_private_eq {P : Finset ℕ} (hP : P.card = 4) {A B T0 T1 T2 X0 X1 X2 Y0 Y1 Y2 : ℕ}
    (hA : A ∈ P) (hB : B ∈ P) (hT0 : T0 ∈ P) (hT1 : T1 ∈ P) (hT2 : T2 ∈ P)
    (hX0 : X0 ∈ P) (hX1 : X1 ∈ P) (hX2 : X2 ∈ P) (hY0 : Y0 ∈ P) (hY1 : Y1 ∈ P) (hY2 : Y2 ∈ P)
    (hAT0 : A ≠ T0) (hAT1 : A ≠ T1) (hAT2 : A ≠ T2) (hBT0 : B ≠ T0) (hBT1 : B ≠ T1)
    (hBT2 : B ≠ T2)
    (hAX0 : A ≠ X0) (hAX1 : A ≠ X1) (hAX2 : A ≠ X2) (hBY0 : B ≠ Y0) (hBY1 : B ≠ Y1)
    (hBY2 : B ≠ Y2)
    (hTX0 : T0 ≠ X0) (hTX1 : T1 ≠ X1) (hTX2 : T2 ≠ X2) (hTY0 : T0 ≠ Y0) (hTY1 : T1 ≠ Y1)
    (hTY2 : T2 ≠ Y2)
    (hX01 : X0 ≠ X1) (hX02 : X0 ≠ X2) (hX12 : X1 ≠ X2) (hY01 : Y0 ≠ Y1) (hY02 : Y0 ≠ Y2)
    (hY12 : Y1 ≠ Y2) (hXY0 : X0 ≠ Y0) (hXY1 : X1 ≠ Y1) (hXY2 : X2 ≠ Y2) : A = B := by
  by_contra hAB
  have hQ : ((P.erase A).erase B).card = 2 := by
    rw [card_erase_of_mem (mem_erase.2 ⟨fun h => hAB h.symm, hB⟩), card_erase_of_mem hA, hP]
  have m : ∀ T ∈ P, A ≠ T → B ≠ T → T ∈ (P.erase A).erase B := fun T hT h1 h2 =>
    mem_erase.2 ⟨fun h => h2 h.symm, mem_erase.2 ⟨fun h => h1 h.symm, hT⟩⟩
  rcases two_pigeon hQ (m _ hT0 hAT0 hBT0) (m _ hT1 hAT1 hBT1) (m _ hT2 hAT2 hBT2) with
    h | h | h
  · -- T0 = T1, third terminal 2
    exact k23_case hP hA hT0 hAT0.symm hB hBT0.symm hX0 hX1 hX2 hY0 hY1 hY2 hAX0 hAX1 hAX2
      hBY0 hBY1 hBY2 hTX0 (h ▸ hTX1) hTY0 (h ▸ hTY1) hX01 hX02 hX12 hY01 hY02 hY12 hXY2
  · -- T0 = T2, third terminal 1
    exact k23_case hP hA hT0 hAT0.symm hB hBT0.symm hX0 hX2 hX1 hY0 hY2 hY1 hAX0 hAX2 hAX1
      hBY0 hBY2 hBY1 hTX0 (h ▸ hTX2) hTY0 (h ▸ hTY2) hX02 hX01 hX12.symm hY02 hY01 hY12.symm hXY1
  · -- T1 = T2, third terminal 0
    exact k23_case hP hA hT1 hAT1.symm hB hBT1.symm hX1 hX2 hX0 hY1 hY2 hY0 hAX1 hAX2 hAX0
      hBY1 hBY2 hBY0 hTX1 (h ▸ hTX2) hTY1 (h ▸ hTY2) hX12 hX01.symm hX02.symm hY12 hY01.symm
      hY02.symm hXY0

/-- The colour of a cross edge leaving a block is the block's missing colour `m` or the private
colour `s`: the terminal `T` and its two block edges `X`, `Y` are three different colours of
`P ∖ {s}`, and the cross edge `E` (a colour in `{1,…,5} = P ∪ {m}`) avoids all three. -/
theorem cross_mem {m s T X Y E : ℕ} (hm : m ∈ Icc 1 5) (hs : s ∈ (Icc 1 5).erase m)
    (hT : T ∈ (Icc 1 5).erase m) (hX : X ∈ (Icc 1 5).erase m) (hY : Y ∈ (Icc 1 5).erase m)
    (hsT : s ≠ T) (hsX : s ≠ X) (hsY : s ≠ Y) (hTX : T ≠ X) (hTY : T ≠ Y) (hXY : X ≠ Y)
    (hE : E ∈ Icc 1 5) (hET : E ≠ T) (hEX : E ≠ X) (hEY : E ≠ Y) : E = m ∨ E = s := by
  by_contra hne
  push Not at hne
  have hc : (((Icc 1 5).erase m).erase s).card = 3 := by
    rw [card_erase_of_mem hs, card_erase_of_mem hm]; rfl
  have mm : ∀ q ∈ (Icc 1 5).erase m, s ≠ q → q ∈ ((Icc 1 5).erase m).erase s :=
    fun q hq h => mem_erase.2 ⟨fun e => h e.symm, hq⟩
  rcases three_fill hc (mm _ hT hsT) (mm _ hX hsX) (mm _ hY hsY) hTX hTY hXY
    (mem_erase.2 ⟨hne.2, mem_erase.2 ⟨hne.1, hE⟩⟩) with h | h | h
  · exact hET h
  · exact hEX h
  · exact hEY h

/-! ### The lists -/

/-- All colours. -/
def full : Finset ℕ := Icc 1 5

/-- List of a cross edge between blocks `i` and `j`. -/
def crossList (i j : ℕ) : Finset ℕ :=
  let p := min i j; let q := max i j
  full.erase
    (if p = 0 ∧ q = 1 then 3 else if p = 0 ∧ q = 2 then 5 else if p = 0 ∧ q = 3 then 2
     else if p = 1 ∧ q = 2 then 4 else if p = 1 ∧ q = 3 then 5 else 1)

/-- List of the edge `uv`. -/
def edgeList (u v : Fin 20) : Finset ℕ :=
  if blk u = blk v then full.erase (blk u + 1) else crossList (blk u) (blk v)

theorem edgeList_symm (u v : Fin 20) : edgeList u v = edgeList v u := by
  unfold edgeList crossList
  by_cases h : blk u = blk v
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h), min_comm, max_comm]

/-- Noel's list assignment. -/
def L : Fin 20 ⊕ G.edgeSet → Finset ℕ
  | Sum.inl v => full.erase (blk v + 1)
  | Sum.inr e => Sym2.lift ⟨edgeList, edgeList_symm⟩ e.val

theorem card_L : ∀ x, (L x).card = 4 := by
  rintro (v | ⟨e, he⟩)
  · simp only [L, full]
    rw [card_erase_of_mem (by simp [blk]; omega)]; rfl
  · induction e using Sym2.ind with
    | _ u v =>
      simp only [L, Sym2.lift_mk]
      revert u v
      decide

/-! ### The final finite check -/

/-- A cross edge between blocks `i` and `j` can be coloured only if some colour of its list lies in
both `{i+1, sᵢ}` and `{j+1, sⱼ}`. -/
def ok (s : Fin 4 → ℕ) (i j : Fin 4) : Prop :=
  ∃ e ∈ crossList i j, (e = i.val + 1 ∨ e = s i) ∧ (e = j.val + 1 ∨ e = s j)

instance (s : Fin 4 → ℕ) (i j : Fin 4) : Decidable (ok s i j) := by
  unfold ok; infer_instance

/-- No choice of private colours `sᵢ ∈ {1,…,5} ∖ {i+1}` lets all six cross edges be coloured. -/
theorem final : ∀ s0 ∈ full.erase 1, ∀ s1 ∈ full.erase 2, ∀ s2 ∈ full.erase 3,
    ∀ s3 ∈ full.erase 4, ¬ (ok ![s0, s1, s2, s3] 0 1 ∧ ok ![s0, s1, s2, s3] 0 2 ∧
      ok ![s0, s1, s2, s3] 0 3 ∧ ok ![s0, s1, s2, s3] 1 2 ∧ ok ![s0, s1, s2, s3] 1 3 ∧
      ok ![s0, s1, s2, s3] 2 3) := by
  decide

/-! ### No total colouring from Noel's lists -/

theorem blk_a : ∀ i : Fin 4, blk (a i) = i.val := by decide
theorem blk_b : ∀ i : Fin 4, blk (b i) = i.val := by decide
theorem blk_t : ∀ i k, blk (t i k) = i.val := by decide
theorem blk_p : ∀ i k, blk (partner i k) = tgt i k := by decide
theorem tgt_ne : ∀ i k, tgt i k ≠ i.val := by decide
theorem t_ne : ∀ (i : Fin 4) (k l : Fin 3), k ≠ l → t i k ≠ t i l := by decide
theorem a_ne_p : ∀ i k, a i ≠ partner i k := by decide
theorem b_ne_p : ∀ i k, b i ≠ partner i k := by decide
theorem a_ne_b : ∀ i, a i ≠ b i := by decide


section Main

variable {c : Fin 20 ⊕ G.edgeSet → ℕ} (hc : G.IsTotalColoring c) (hL : ∀ x, c x ∈ L x)
include hc hL

omit hc in
theorem L_inl (v : Fin 20) : c (Sum.inl v) ∈ full.erase (blk v + 1) := hL (Sum.inl v)

omit hc in
theorem L_ed {u v : Fin 20} (h : G.Adj u v) : c (Sum.inr (ed G h)) ∈ edgeList u v := hL _


omit hc in
/-- Colour of a cross edge as a natural number in `full`. -/
theorem cross_in_full (i : Fin 4) (k : Fin 3) :
    c (Sum.inr (ed G (adj_t_p i k))) ∈ full := by
  have h := L_ed hL (adj_t_p i k)
  unfold edgeList at h
  rw [blk_t, blk_p, if_neg (tgt_ne i k).symm] at h
  unfold crossList at h
  exact mem_of_mem_erase h

omit hc in
/-- The colour inside block `i`: vertex and edge colours lie in `full.erase (i+1)`. -/
theorem in_blk_ed {u v : Fin 20} (h : G.Adj u v) (hu : blk u = blk v) :
    c (Sum.inr (ed G h)) ∈ full.erase (blk u + 1) := by
  have := L_ed hL h
  unfold edgeList at this
  rwa [if_pos hu] at this

/-- **Block lemma.** In block `i` the two private vertices share a colour `s`, and every cross
edge leaving block `i` has colour `i+1` or `s`. -/
theorem block (i : Fin 4) :
    c (Sum.inl (a i)) = c (Sum.inl (b i)) ∧
      ∀ k, c (Sum.inr (ed G (adj_t_p i k))) = i.val + 1 ∨
        c (Sum.inr (ed G (adj_t_p i k))) = c (Sum.inl (a i)) := by
  have hP : (full.erase (i.val + 1)).card = 4 := by
    rw [card_erase_of_mem (by simp [full]; omega)]; rfl
  have va := L_inl hL (a i); rw [blk_a] at va
  have vb := L_inl hL (b i); rw [blk_b] at vb
  have vt : ∀ k, c (Sum.inl (t i k)) ∈ full.erase (i.val + 1) := fun k => by
    have := L_inl hL (t i k); rwa [blk_t] at this
  have ex : ∀ k, c (Sum.inr (ed G (adj_a_t i k))) ∈ full.erase (i.val + 1) := fun k => by
    have := in_blk_ed hL (adj_a_t i k) (by rw [blk_a, blk_t]); rwa [blk_a] at this
  have ey : ∀ k, c (Sum.inr (ed G (adj_b_t i k))) ∈ full.erase (i.val + 1) := fun k => by
    have := in_blk_ed hL (adj_b_t i k) (by rw [blk_b, blk_t]); rwa [blk_b] at this
  have tn := t_ne i
  -- edges at a common terminal
  have xy : ∀ k, c (Sum.inr (ed G (adj_a_t i k))) ≠ c (Sum.inr (ed G (adj_b_t i k))) :=
    fun k => by
      have e1 : ed G (adj_a_t i k) = ed G (adj_a_t i k).symm := Subtype.ext Sym2.eq_swap
      have e2 : ed G (adj_b_t i k) = ed G (adj_b_t i k).symm := Subtype.ext Sym2.eq_swap
      rw [e1, e2]
      exact tc_ee hc _ _ (a_ne_b i)
  have hab : c (Sum.inl (a i)) = c (Sum.inl (b i)) :=
    k23_private_eq hP va vb (vt 0) (vt 1) (vt 2) (ex 0) (ex 1) (ex 2) (ey 0) (ey 1) (ey 2)
      (tc_vv hc (adj_a_t i 0)) (tc_vv hc (adj_a_t i 1)) (tc_vv hc (adj_a_t i 2))
      (tc_vv hc (adj_b_t i 0)) (tc_vv hc (adj_b_t i 1)) (tc_vv hc (adj_b_t i 2))
      (tc_ve_left hc _) (tc_ve_left hc _) (tc_ve_left hc _)
      (tc_ve_left hc _) (tc_ve_left hc _) (tc_ve_left hc _)
      (tc_ve_right hc _) (tc_ve_right hc _) (tc_ve_right hc _)
      (tc_ve_right hc _) (tc_ve_right hc _) (tc_ve_right hc _)
      (tc_ee hc _ _ (tn 0 1 (by decide))) (tc_ee hc _ _ (tn 0 2 (by decide)))
      (tc_ee hc _ _ (tn 1 2 (by decide)))
      (tc_ee hc _ _ (tn 0 1 (by decide))) (tc_ee hc _ _ (tn 0 2 (by decide)))
      (tc_ee hc _ _ (tn 1 2 (by decide)))
      (xy 0) (xy 1) (xy 2)
  refine ⟨hab, fun k => ?_⟩
  have hm : i.val + 1 ∈ Icc 1 5 := by simp; omega
  refine cross_mem hm va (vt k) (ex k) (ey k) (tc_vv hc (adj_a_t i k))
    (tc_ve_left hc _) (hab ▸ tc_ve_left hc _) (tc_ve_right hc _) (tc_ve_right hc _) (xy k)
    (cross_in_full hL i k) (tc_ve_left hc _).symm ?_ ?_
  · exact (tc_ee' hc (adj_a_t i k) (adj_t_p i k) (a_ne_p i k)).symm
  · exact (tc_ee' hc (adj_b_t i k) (adj_t_p i k) (b_ne_p i k)).symm

end Main

theorem edgeList_cross : ∀ i k, edgeList (t i k) (partner i k) = crossList i (tgt i k) := by
  decide

/-- The cross edge between blocks `i` and `j`, seen from both sides (terminal `k` of block `i`,
terminal `k'` of block `j`), satisfies the condition `ok`. -/
theorem pair_ok {c : Fin 20 ⊕ G.edgeSet → ℕ} (hc : G.IsTotalColoring c) (hL : ∀ x, c x ∈ L x)
    (i j : Fin 4) (k k' : Fin 3) (hij : tgt i k = j.val)
    (hsame : s(t i k, partner i k) = s(t j k', partner j k')) :
    ok (fun i => c (Sum.inl (a i))) i j := by
  have he := L_ed hL (adj_t_p i k)
  rw [edgeList_cross, hij] at he
  have hsame' : ed G (adj_t_p i k) = ed G (adj_t_p j k') := Subtype.ext hsame
  refine ⟨_, he, (block hc hL i).2 k, ?_⟩
  rw [hsame']
  exact (block hc hL j).2 k'

/-- **No total colouring from Noel's list assignment.** -/
theorem no_coloring_from_L (c : Fin 20 ⊕ G.edgeSet → ℕ) (hc : G.IsTotalColoring c)
    (hL : ∀ x, c x ∈ L x) : False := by
  set s : Fin 4 → ℕ := fun i => c (Sum.inl (a i)) with hs
  have hv : ![s 0, s 1, s 2, s 3] = s := by
    ext i; fin_cases i <;> rfl
  have m : ∀ i : Fin 4, s i ∈ full.erase (i.val + 1) := fun i => by
    have := L_inl hL (a i); rwa [blk_a] at this
  have := final (s 0) (m 0) (s 1) (m 1) (s 2) (m 2) (s 3) (m 3)
  rw [hv] at this
  exact this ⟨pair_ok hc hL 0 1 0 0 (by decide) (by decide),
    pair_ok hc hL 0 2 1 0 (by decide) (by decide),
    pair_ok hc hL 0 3 2 0 (by decide) (by decide),
    pair_ok hc hL 1 2 1 1 (by decide) (by decide),
    pair_ok hc hL 1 3 2 1 (by decide) (by decide),
    pair_ok hc hL 2 3 2 2 (by decide) (by decide)⟩

/-- `G` is not totally 4-choosable. -/
theorem not_totalChoosable_four : ¬ G.TotalChoosable 4 := by
  intro h
  obtain ⟨c, hcL, hc⟩ := h L (fun x => (card_L x).ge)
  exact no_coloring_from_L c hc hcL

/-! ### `χ''(G) = 4` -/

/-- Vertex colours of Noel's total 4-colouring (`3` is the paper's colour 4). -/
def colV : Fin 20 → Fin 4 := ![3, 3, 1, 2, 0, 3, 3, 0, 2, 1, 3, 3, 0, 1, 2, 3, 3, 1, 2, 0]

/-- Colour of the block edge from private vertex `x` to terminal `y`: the colour after (from `a`)
or before (from `b`) the terminal's colour, cyclically in `{0,1,2}`. -/
def colPT (x y : Fin 20) : Fin 4 :=
  ⟨((colV y).val + (if x.val % 5 = 0 then 1 else 2)) % 3, by omega⟩

/-- Edge colours: cross edges get `3`. -/
def colE (u v : Fin 20) : Fin 4 :=
  if u.val / 5 = v.val / 5 then (if u.val % 5 < 2 then colPT u v else colPT v u) else 3

theorem colE_symm : ∀ u v, G.Adj u v → colE u v = colE v u := by decide

/-- Noel's total 4-colouring. -/
def col4 : Fin 20 ⊕ G.edgeSet → Fin 4
  | Sum.inl v => colV v
  | Sum.inr e => Sym2.lift ⟨fun u v => if G.Adj u v then colE u v else 0, fun u v => by
      show (if G.Adj u v then colE u v else 0) = (if G.Adj v u then colE v u else 0)
      by_cases h : G.Adj u v
      · rw [if_pos h, if_pos h.symm, colE_symm u v h]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]⟩ e.val

theorem col4_vv : ∀ u v, G.Adj u v → colV u ≠ colV v := by decide
theorem col4_ve : ∀ u v, G.Adj u v → colV u ≠ colE u v := by decide
theorem col4_ee : ∀ u v w, G.Adj u v → G.Adj u w → v ≠ w → colE u v ≠ colE u w := by decide

theorem col4_edge {u v : Fin 20} (h : G.Adj u v) (e : G.edgeSet) (he : e.val = s(u, v)) :
    col4 (Sum.inr e) = colE u v := by
  simp only [col4, he, Sym2.lift_mk, if_pos h]

theorem isTotalColoring_col4 : G.IsTotalColoring col4 := by
  refine ⟨fun u v h => col4_vv u v h, ?_, ?_⟩
  · rintro ⟨e, he⟩ ⟨f, hf⟩ hef ⟨v, hve, hvf⟩
    obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.1 hve
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 hvf
    have hx : G.Adj v x := he
    have hy : G.Adj v y := hf
    rw [col4_edge hx _ rfl, col4_edge hy _ rfl]
    refine col4_ee v x y hx hy ?_
    rintro rfl
    exact hef rfl
  · rintro v ⟨e, he⟩ hve
    obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.1 hve
    have hx : G.Adj v x := he
    rw [col4_edge hx _ rfl]
    exact col4_ve v x hx

theorem totalColorable_four : G.TotalColorable 4 := ⟨col4, isTotalColoring_col4⟩

/-- Three colours are too few: vertex `a 0` and its three edges need four different colours. -/
theorem not_totalColorable_of_lt {n : ℕ} (hn : n < 4) : ¬ G.TotalColorable n := by
  rintro ⟨c, hc⟩
  let f : Fin 4 → Fin n := ![c (Sum.inl (a 0)), c (Sum.inr (ed G (adj_a_t 0 0))),
    c (Sum.inr (ed G (adj_a_t 0 1))), c (Sum.inr (ed G (adj_a_t 0 2)))]
  have hf : Function.Injective f := by
    have h01 := tc_ve_left hc (adj_a_t 0 0)
    have h02 := tc_ve_left hc (adj_a_t 0 1)
    have h03 := tc_ve_left hc (adj_a_t 0 2)
    have h12 := tc_ee hc (adj_a_t 0 0) (adj_a_t 0 1) (t_ne 0 0 1 (by decide))
    have h13 := tc_ee hc (adj_a_t 0 0) (adj_a_t 0 2) (t_ne 0 0 2 (by decide))
    have h23 := tc_ee hc (adj_a_t 0 1) (adj_a_t 0 2) (t_ne 0 1 2 (by decide))
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [f]
  have := Fintype.card_le_of_injective f hf
  simp at this
  omega

theorem totalChromaticNumber_G : G.totalChromaticNumber = 4 := by
  apply le_antisymm (Nat.sInf_le totalColorable_four)
  apply le_csInf ⟨4, totalColorable_four⟩
  intro n hn
  by_contra h
  exact not_totalColorable_of_lt (by omega) hn

theorem listTotalChromaticNumber_G_ne : G.listTotalChromaticNumber ≠ 4 := by
  intro h
  have hne : {k | G.TotalChoosable k}.Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty] at he
    simp [SimpleGraph.listTotalChromaticNumber, he] at h
  have := Nat.sInf_mem hne
  rw [show sInf {k | G.TotalChoosable k} = 4 from h] at this
  exact not_totalChoosable_four this

/-- **The List Total Colouring Conjecture is false** (Noel 2026): Noel's cubic graph on 20
vertices has `χ''(G) = 4` but is not totally 4-choosable, so `χ''_ℓ(G) ≠ χ''(G)`. -/
theorem not_listTotalColouringConjecture : ¬ ListTotalColouringConjecture := by
  intro h
  have := h (Fin 20) G
  rw [totalChromaticNumber_G] at this
  exact listTotalChromaticNumber_G_ne this

/-- The explicit statement: a cubic graph on 20 vertices with `χ''(G) = 4` that is not totally
4-choosable. -/
theorem exists_counterexample :
    ∃ H : SimpleGraph (Fin 20), ∃ _ : DecidableRel H.Adj,
      (∀ v, ((Finset.univ : Finset (Fin 20)).filter (H.Adj v)).card = 3) ∧
      H.totalChromaticNumber = 4 ∧ ¬ H.TotalChoosable 4 :=
  ⟨G, inferInstance, G_cubic, totalChromaticNumber_G, not_totalChoosable_four⟩

end OpenProblemsLab.ListTotal
