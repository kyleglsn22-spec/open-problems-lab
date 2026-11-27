import Mathlib

/-!
# Local antimagic labellings: definitions and the degree bounds

For a finite graph `G` with `m` edges, a bijection `f : E(G) → {1,…,m}` induces vertex weights
`f⁺(v) = ∑_{e ∋ v} f(e)`. It is *local antimagic* if adjacent vertices get different weights, and
the *local antimagic chromatic number* `χ_la(G)` is the least number of distinct weights over all
local antimagic labellings. We write labellings as `f : G.edgeSet ≃ Fin m` and use the label
`f e + 1 ∈ {1,…,m}`.

The *leaf conjecture* (see Bača et al. 2022, Premalatha et al. 2020) says
`χ_la(T) ≤ ℓ(T) + 2` for every tree `T` with at least three vertices, `ℓ(T)` the number of leaves.

This file proves the degree bounds of Brondani–França (arXiv:2610.22783, Lemma 3.1): a vertex of
degree `d` has weight between `d(d+1)/2` and `d(2m−d+1)/2` (written without division), and that two
non-adjacent leaves always get different weights.
-/

namespace OpenProblemsLab.LocalAntimagic

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A labelling: a bijection from the edges to `Fin m`, `m` the number of edges. -/
abbrev Labelling := G.edgeSet ≃ Fin (Fintype.card G.edgeSet)

variable {G}

/-- The label `f e + 1 ∈ {1,…,m}` of an edge (and `0` off the edge set). -/
def lab (f : Labelling G) (e : Sym2 V) : ℕ :=
  if h : e ∈ G.edgeSet then (f ⟨e, h⟩ : ℕ) + 1 else 0

/-- The induced weight `f⁺(v)`: the sum of the labels of the edges at `v`. -/
def wt (f : Labelling G) (v : V) : ℕ := ∑ e ∈ G.incidenceFinset v, lab f e

variable (G)

/-- `f` is local antimagic: adjacent vertices get different weights. -/
def IsLocalAntimagic (f : Labelling G) : Prop := ∀ u v, G.Adj u v → wt f u ≠ wt f v

/-- The local antimagic chromatic number `χ_la(G)`: the least number of distinct vertex weights of
a local antimagic labelling. -/
noncomputable def chiLA : ℕ :=
  sInf {n | ∃ f : Labelling G, IsLocalAntimagic G f ∧ (univ.image (wt f)).card = n}

/-- The number of leaves (vertices of degree one). -/
def numLeaves : ℕ := (univ.filter fun v => G.degree v = 1).card

/-- **The leaf conjecture**: every tree `T` with at least three vertices has
`χ_la(T) ≤ ℓ(T) + 2`. -/
def LeafConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree → 3 ≤ Fintype.card V → chiLA T ≤ numLeaves T + 2

variable {G}

/-! ### Sums of distinct labels -/

theorem sum_lower (S : Finset ℕ) (h : ∀ x ∈ S, 1 ≤ x) :
    S.card * (S.card + 1) ≤ 2 * ∑ x ∈ S, x := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hn : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [card_insert_of_notMem hn, sum_insert hn]
    have ih' := ih fun x hx => h x (mem_insert_of_mem hx)
    have hc : s.card + 1 ≤ a := by
      have hsub : s ⊆ Icc 1 (a - 1) := fun x hx =>
        mem_Icc.2 ⟨h x (mem_insert_of_mem hx), by have := ha x hx; omega⟩
      have := card_le_card hsub
      simp only [Nat.card_Icc] at this
      have := h a (mem_insert_self a s)
      omega
    nlinarith

theorem sum_upper (S : Finset ℕ) (m : ℕ) (h : ∀ x ∈ S, x ≤ m) :
    2 * ∑ x ∈ S, x + S.card * S.card ≤ 2 * S.card * m + S.card := by
  induction S using Finset.induction_on_min with
  | empty => simp
  | insert a s ha ih =>
    have hn : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [card_insert_of_notMem hn, sum_insert hn]
    have ih' := ih fun x hx => h x (mem_insert_of_mem hx)
    have hc : a + s.card ≤ m := by
      have hsub : s ⊆ Icc (a + 1) m := fun x hx =>
        mem_Icc.2 ⟨by have := ha x hx; omega, h x (mem_insert_of_mem hx)⟩
      have := card_le_card hsub
      simp only [Nat.card_Icc] at this
      have := h a (mem_insert_self a s)
      omega
    nlinarith

/-! ### Degree bounds for weights -/

omit [DecidableEq V] in
theorem lab_injOn (f : Labelling G) : Set.InjOn (lab f) G.edgeSet := by
  intro e he e' he' h
  simp only [lab, he, he', dite_true, add_left_inj] at h
  exact congrArg Subtype.val (f.injective (Fin.ext h))

omit [DecidableEq V] in
theorem lab_mem (f : Labelling G) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    1 ≤ lab f e ∧ lab f e ≤ Fintype.card G.edgeSet := by
  simp only [lab, he, dite_true]
  exact ⟨by omega, (f ⟨e, he⟩).2⟩

/-- **Degree bounds** (Brondani–França, Lemma 3.1): with `d = deg v` and `m` edges,
`d(d+1) ≤ 2 f⁺(v)` and `2 f⁺(v) + d² ≤ 2dm + d`, i.e. `f⁺(v) ∈ [d(d+1)/2, d(2m−d+1)/2]`. -/
theorem wt_bounds (f : Labelling G) (v : V) :
    G.degree v * (G.degree v + 1) ≤ 2 * wt f v ∧
      2 * wt f v + G.degree v * G.degree v ≤
        2 * G.degree v * Fintype.card G.edgeSet + G.degree v := by
  set S := (G.incidenceFinset v).image (lab f)
  have hinj : Set.InjOn (lab f) (G.incidenceFinset v : Set (Sym2 V)) := fun e he e' he' h =>
    lab_injOn f (G.incidenceSet_subset v (by simpa using he))
      (G.incidenceSet_subset v (by simpa using he')) h
  have hw : wt f v = ∑ x ∈ S, x := (sum_image (f := fun x => x) hinj).symm
  have hcard : S.card = G.degree v := by
    rw [card_image_of_injOn hinj, card_incidenceFinset_eq_degree]
  have hmem : ∀ x ∈ S, 1 ≤ x ∧ x ≤ Fintype.card G.edgeSet := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := mem_image.1 hx
    exact lab_mem f (G.incidenceSet_subset v (by simpa using he))
  rw [hw, ← hcard]
  exact ⟨sum_lower S fun x hx => (hmem x hx).1,
    sum_upper S _ fun x hx => (hmem x hx).2⟩

/-- A leaf's weight is the label of its edge. -/
theorem exists_wt_leaf (f : Labelling G) (v : V) (hv : G.degree v = 1) :
    ∃ e ∈ G.edgeSet, v ∈ e ∧ wt f v = lab f e := by
  rw [← card_incidenceFinset_eq_degree] at hv
  obtain ⟨e, he⟩ := card_eq_one.1 hv
  have hmem : e ∈ G.incidenceSet v := by
    rw [← mem_incidenceFinset, he]; exact mem_singleton_self e
  exact ⟨e, hmem.1, hmem.2, by rw [wt, he, sum_singleton]⟩

theorem wt_leaf_le (f : Labelling G) (v : V) (hv : G.degree v = 1) :
    wt f v ≤ Fintype.card G.edgeSet := by
  obtain ⟨e, he, -, h⟩ := exists_wt_leaf f v hv
  rw [h]; exact (lab_mem f he).2

/-- Two distinct non-adjacent leaves get different weights. -/
theorem wt_leaf_ne (f : Labelling G) {u v : V} (hu : G.degree u = 1) (hv : G.degree v = 1)
    (huv : u ≠ v) (hn : ¬ G.Adj u v) : wt f u ≠ wt f v := by
  obtain ⟨e, he, hue, h⟩ := exists_wt_leaf f u hu
  obtain ⟨e', he', hve', h'⟩ := exists_wt_leaf f v hv
  intro hw
  rw [h, h'] at hw
  have hee : e = e' := lab_injOn f he he' hw
  subst hee
  have : e = s(u, v) := (Sym2.mem_and_mem_iff huv).1 ⟨hue, hve'⟩
  rw [this, mem_edgeSet] at he
  exact hn he

end OpenProblemsLab.LocalAntimagic
