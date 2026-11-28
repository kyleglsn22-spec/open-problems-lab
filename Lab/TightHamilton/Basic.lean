import Mathlib

/-!
# The all-`n` exact codegree conjecture for tight Hamiltonian cycles is false

Definitions and the general argument. See `Lab/TightHamilton/Main.lean`.
-/

namespace OpenProblemsLab.TightHamilton

open Finset

section General

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The codegree of a vertex set `S` in a hypergraph with edge set `E`. -/
def codegree (E : Finset (Finset V)) (S : Finset V) : ℕ := (E.filter (S ⊆ ·)).card

/-- The positions of the window of `k` cyclically consecutive positions starting at `i`. -/
def idx {n : ℕ} (k : ℕ) (i : Fin n) : Finset (Fin n) :=
  (Finset.range k).image fun t => ⟨(i.val + t) % n, Nat.mod_lt _ i.pos⟩

/-- The window of `k` cyclically consecutive vertices starting at position `i` of a cyclic
order `f : Fin n → V`. -/
def window {n : ℕ} (f : Fin n → V) (k : ℕ) (i : Fin n) : Finset V :=
  (Finset.range k).image fun t => f ⟨(i.val + t) % n, Nat.mod_lt _ i.pos⟩

omit [Fintype V] in
theorem window_eq {n : ℕ} (f : Fin n → V) (k : ℕ) (i : Fin n) :
    window f k i = (idx k i).image f := by
  simp [window, idx, Finset.image_image, Function.comp_def]

/-- `E` has a tight Hamiltonian cycle (for uniformity `k`): a cyclic order of all vertices in
which every `k` cyclically consecutive vertices form an edge. -/
def HasTightHamiltonCycle (E : Finset (Finset V)) (k : ℕ) : Prop :=
  ∃ f : Fin (Fintype.card V) → V, Function.Bijective f ∧ ∀ i, window f k i ∈ E

end General

/-- **Conjecture** (Rödl–Ruciński–Szemerédi 2011, Conjecture 1.1, attributed to Katona and
Kierstead): every `k`-uniform hypergraph on `n ≥ k + 1 ≥ 4` vertices in which every
`(k - 1)`-set has codegree at least `⌊(n - k + 3)/2⌋` has a tight Hamiltonian cycle. -/
def CodegreeConjecture : Prop :=
  ∀ (k : ℕ) (V : Type) [Fintype V] [DecidableEq V] (E : Finset (Finset V)),
    3 ≤ k → k + 1 ≤ Fintype.card V → (∀ e ∈ E, e.card = k) →
    (∀ S : Finset V, S.card = k - 1 → (Fintype.card V - k + 3) / 2 ≤ codegree E S) →
    HasTightHamiltonCycle E k

/-- The ten faces of the hemi-icosahedron on `{0,…,5}` (Ferudun's `D′`, shifted down by one). -/
def Dface : Finset (Finset ℕ) :=
  {{0,1,2}, {0,1,3}, {0,2,4}, {0,3,5}, {0,4,5}, {1,2,5}, {1,3,4}, {1,4,5}, {2,3,4}, {2,3,5}}

/-- Two faces of the hemi-icosahedron always meet. -/
theorem Dface_meet : ∀ A ∈ Dface, ∀ B ∈ Dface, ¬ Disjoint A B := by decide +kernel

/-- The points of `W = {0,…,5}` in a vertex set (the other vertices are the apexes). -/
def wpart {n : ℕ} (e : Finset (Fin n)) : Finset (Fin n) := e.filter fun x => x.val < 6

/-- The edge condition of `H_k`: the set meets `W` in other than three points, or in a face. -/
def good {n : ℕ} (e : Finset (Fin n)) : Prop :=
  (wpart e).card ≠ 3 ∨ (wpart e).image Fin.val ∈ Dface

instance {n : ℕ} (e : Finset (Fin n)) : Decidable (good e) := by unfold good; infer_instance

/-- Ferudun's `k`-graph `H_k` on `Fin (k + 4)`: all `k`-sets meeting `W = {0,…,5}` in other than
three points, and the `k`-sets meeting `W` in a face of the hemi-icosahedron. -/
def E (k : ℕ) : Finset (Finset (Fin (k + 4))) :=
  (Finset.univ : Finset (Finset (Fin (k + 4)))).filter fun e => e.card = k ∧ good e

theorem uniform_E (k : ℕ) : ∀ e ∈ E k, e.card = k := fun _ he => (Finset.mem_filter.1 he).2.1

/-- The codegree of a `(k - 1)`-set `S` in `H_k` counts the vertices `x ∉ S` such that
`S ∪ {x}` is good. (Used to keep the kernel computations small.) -/
theorem codegree_E_eq (k : ℕ) (S : Finset (Fin (k + 4))) (hS : S.card + 1 = k) :
    codegree (E k) S = ((Finset.univ \ S).filter fun x => good (insert x S)).card := by
  symm
  unfold codegree
  apply Finset.card_bij (fun x _ => insert x S)
  · intro x hx
    obtain ⟨hx, hg⟩ := Finset.mem_filter.1 hx
    have hxS : x ∉ S := (Finset.mem_sdiff.1 hx).2
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, hg⟩,
      Finset.subset_insert _ _⟩
    rw [Finset.card_insert_of_notMem hxS, hS]
  · intro x hx y hy h
    have hxS : x ∉ S := (Finset.mem_sdiff.1 (Finset.mem_filter.1 hx).1).2
    have : x ∈ insert y S := h ▸ Finset.mem_insert_self x S
    rcases Finset.mem_insert.1 this with h' | h'
    · exact h'
    · exact absurd h' hxS
  · intro e he
    obtain ⟨he, hSe⟩ := Finset.mem_filter.1 he
    obtain ⟨-, hc, hg⟩ := Finset.mem_filter.1 he
    have h1 : (e \ S).card = 1 := by rw [Finset.card_sdiff_of_subset hSe]; omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h1
    have hxe : x ∈ e \ S := hx ▸ Finset.mem_singleton_self x
    have heq : insert x S = e := by
      rw [Finset.insert_eq, ← hx, Finset.sdiff_union_of_subset hSe]
    refine ⟨x, Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ _,
      (Finset.mem_sdiff.1 hxe).2⟩, heq ▸ hg⟩, heq⟩

/-- The combinatorial core (Ferudun's Lemma 2.4): wherever the `k - 2` apexes sit in the cyclic
order, two `k`-windows contain exactly three points of `W` each, and these triples are disjoint. -/
def ForcedPair (k : ℕ) : Prop :=
  ∀ P ∈ (Finset.univ : Finset (Fin (k + 4))).powersetCard (k - 2),
    ∃ i j : Fin (k + 4), (idx k i \ P).card = 3 ∧ (idx k j \ P).card = 3 ∧
      Disjoint (idx k i \ P) (idx k j \ P)

theorem no_tight_cycle (k : ℕ)
    (hA : ((Finset.univ : Finset (Fin (k + 4))).filter fun x => ¬ x.val < 6).card = k - 2)
    (hF : ForcedPair k) :
    ¬ ∃ f : Fin (k + 4) → Fin (k + 4), Function.Bijective f ∧ ∀ i, window f k i ∈ E k := by
  rintro ⟨f, hf, hw⟩
  set P := (Finset.univ : Finset (Fin (k + 4))).filter fun x => ¬ (f x).val < 6 with hPdef
  have hP : P.image f = (Finset.univ : Finset (Fin (k + 4))).filter fun x => ¬ x.val < 6 := by
    ext y
    simp only [hPdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy; obtain ⟨x, rfl⟩ := hf.2 y; exact ⟨x, hy, rfl⟩
  have hPc : P.card = k - 2 := by
    rw [← hA, ← hP, Finset.card_image_of_injective _ hf.1]
  obtain ⟨i, j, hi, hj, hd⟩ := hF P (Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hPc⟩)
  have hwp : ∀ i, wpart (window f k i) = (idx k i \ P).image f := by
    intro i
    ext y
    simp only [window_eq, wpart, hPdef, Finset.mem_filter, Finset.mem_image, Finset.mem_sdiff,
      Finset.mem_univ, true_and, not_not]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩; exact ⟨x, ⟨hx, hy⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hy⟩, rfl⟩; exact ⟨⟨x, hx, rfl⟩, hy⟩
  have key : ∀ i, (idx k i \ P).card = 3 → ((idx k i \ P).image f).image Fin.val ∈ Dface := by
    intro i hc
    have h : good (window f k i) := (Finset.mem_filter.1 (hw i)).2.2
    unfold good at h
    rw [hwp, Finset.card_image_of_injective _ hf.1] at h
    rcases h with h | h
    · exact absurd hc h
    · exact h
  refine Dface_meet _ (key i hi) _ (key j hj) ?_
  rw [Finset.disjoint_image Fin.val_injective, Finset.disjoint_image hf.1]
  exact hd

/-- Turn the abstract statement into the conjecture's form (with `Fintype.card`). -/
theorem not_hasTightHamiltonCycle (k : ℕ)
    (hA : ((Finset.univ : Finset (Fin (k + 4))).filter fun x => ¬ x.val < 6).card = k - 2)
    (hF : ForcedPair k) : ¬ HasTightHamiltonCycle (E k) k := by
  unfold HasTightHamiltonCycle
  rw [Fintype.card_fin]
  exact no_tight_cycle k hA hF

end OpenProblemsLab.TightHamilton
