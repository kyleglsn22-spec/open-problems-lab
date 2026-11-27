import os
HERE = os.path.dirname(os.path.abspath(__file__))
import json, itertools
import networkx as nx

d = json.load(open(os.path.join(HERE, '..', 'paper_graphs.json')))
G = nx.Graph([tuple(e) for e in d['G29']['edges']])
G = nx.convert_node_labels_to_integers(G, ordering='sorted')
E = sorted(tuple(sorted(e)) for e in G.edges())
coords = json.load(open(os.path.join(HERE, '..', 'g29_coords.json')))
C = [tuple(coords[str(i)]) for i in range(29)]
cyc = json.load(open(os.path.join(HERE, '..', 'g29_cycles.json')))
QI = [1, 2, 3, 4, 7, 8, 9, 10, 16, 17, 18, 19]
RI = [0, 5, 6, 11, 12, 13, 14, 15, 20, 21, 22, 23, 24, 25, 26]


def lst(xs):
    return '[' + ', '.join(map(str, xs)) + ']'


def fin(xs):
    return '{' + ', '.join(map(str, xs)) + '}'


def cyclist(key):
    k, cs = cyc[key]
    return k, '[' + ',\n    '.join(lst(c) for c in cs) + ']'


out = []
w = out.append
w('''import Mathlib

/-!
# The Albertson–Berman conjecture is false (claim AB-1)

Albertson and Berman (1979) conjectured that every planar graph on `n` vertices has an induced forest
on at least `n / 2` vertices. It was disproved in August 2026 (Jung, arXiv 2608.17350; Makarov,
arXiv 2608.13964). Cames van Batenburg, Goedgebeur and Jooken (arXiv 2608.23260) showed that the
smallest counterexample has 29 vertices; their graph `G₂₉` glues a 14-vertex gadget `Q` and a
17-vertex gadget `R` along an edge.

We check `G₂₉` here:
* `G` has a straight-line drawing in the plane (rational, in fact integer, coordinates) in which two
  distinct edges meet only at a common endpoint (`straightLinePlanar_G`). Any reasonable notion of
  planarity follows from this.
* every induced forest of `G` has at most `14 < 29 / 2` vertices (`card_le_of_isAcyclic`).

The forest bound follows the paper's gadget argument: `{27, 28}` (the distinguished edge) separates
the `Q` side (12 vertices) from the `R` side (15 vertices). For each choice of which of `27, 28` lie in
the forest, every large enough vertex set on one side contains the vertex set of a cycle from an
explicit list. These hitting facts and the drawing are checked with `decide +kernel`.
-/

namespace OpenProblemsLab.AlbertsonBerman

open SimpleGraph

/-! ## Statement -/

/-- A straight-line planar drawing: vertices go to distinct points of `ℝ²`, edges are drawn as
segments, and the segments of two distinct edges meet only in the image of a common endpoint. -/
def StraightLinePlanar {V : Type*} (H : SimpleGraph V) : Prop :=
  ∃ p : V → ℝ × ℝ, Function.Injective p ∧
    ∀ a b c d, H.Adj a b → H.Adj c d → s(a, b) ≠ s(c, d) →
      segment ℝ (p a) (p b) ∩ segment ℝ (p c) (p d) ⊆ p '' ({a, b} ∩ {c, d} : Set V)

/-! ## The graph -/

/-- The 80 edges of `G₂₉` (vertex labels as in `explorer/albertson-berman/paper_graphs.json`,
renumbered in sorted order). -/
def edges : List (Fin 29 × Fin 29) :=
''')
w('  [' + ', '.join(f'({a}, {b})' for a, b in E) + ']\n')
w('''
/-- Boolean adjacency. -/
def adjB (a b : Fin 29) : Bool :=
  edges.any fun e => (e.1 == a && e.2 == b) || (e.1 == b && e.2 == a)

lemma adjB_symm : ∀ a b : Fin 29, adjB a b = adjB b a := by decide +kernel

lemma adjB_irrefl : ∀ a : Fin 29, adjB a a = false := by decide +kernel

/-- The 29-vertex graph `G₂₉` of Cames van Batenburg–Goedgebeur–Jooken. -/
def G : SimpleGraph (Fin 29) where
  Adj a b := adjB a b = true
  symm := ⟨fun a b h => by rw [adjB_symm]; exact h⟩
  loopless := ⟨fun a h => by rw [adjB_irrefl] at h; exact Bool.false_ne_true h⟩

lemma G_adj (a b : Fin 29) : G.Adj a b ↔ adjB a b = true := Iff.rfl

lemma adj_iff (a b : Fin 29) : G.Adj a b ↔ (a, b) ∈ edges ∨ (b, a) ∈ edges := by
  rw [G_adj]
  unfold adjB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨e, he, h⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [← h1, ← h2]; exact he
    · right; rw [← h1, ← h2]; exact he
  · rintro (h | h)
    · exact ⟨_, h, by simp⟩
    · exact ⟨_, h, by simp⟩

/-! ## Cycles -/

theorem not_isAcyclic_of_cycleFn {V : Type*} (H : SimpleGraph V) (S : Set V) (k : ℕ)
    (f : Fin (k + 3) → V) (hinj : Function.Injective f) (hadj : ∀ i, H.Adj (f i) (f (i + 1)))
    (hS : ∀ i, f i ∈ S) : ¬ (H.induce S).IsAcyclic := by
  rw [isAcyclic_iff_free_cycleGraph]
  intro h
  refine h (k + 3) (by omega) ?_
  refine ⟨⟨⟨fun i => ⟨f i, hS i⟩, ?_⟩, ?_⟩⟩
  · intro u v huv
    have huv' : (cycleGraph ((k + 1) + 2)).Adj u v := huv
    rw [cycleGraph_adj] at huv'
    show H.Adj (f u) (f v)
    rcases huv' with h1 | h1
    · have : u = v + 1 := by rw [← h1, add_sub_cancel]
      subst this; exact (hadj v).symm
    · have : v = u + 1 := by rw [← h1, add_sub_cancel]
      subst this; exact hadj u
  · intro u v huv
    exact hinj (congrArg Subtype.val huv)

/-- A list `[v₀, …, v_{m-1}]` (`m ≥ 3`, distinct) with `vᵢ ~ vᵢ₊₁` and `v_{m-1} ~ v₀`. -/
def validCycle (l : List (Fin 29)) : Bool :=
  decide (3 ≤ l.length) && l.Nodup &&
    (List.range l.length).all fun i => adjB (l.getD i 0) (l.getD ((i + 1) % l.length) 0)

theorem not_isAcyclic_of_validCycle (S : Set (Fin 29)) (l : List (Fin 29))
    (hl : validCycle l = true) (hS : ∀ v ∈ l, v ∈ S) : ¬ (G.induce S).IsAcyclic := by
  simp only [validCycle, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hl
  obtain ⟨⟨hlen, hnd⟩, hadj⟩ := hl
  obtain ⟨k, hk⟩ : ∃ k, l.length = k + 3 := ⟨l.length - 3, by omega⟩
  have hget : ∀ i : Fin (k + 3), l.getD i.val 0 = l.get (Fin.cast hk.symm i) := by
    intro i
    rw [List.getD_eq_getElem _ _ (by rw [hk]; exact i.isLt)]
    rfl
  refine not_isAcyclic_of_cycleFn G S k (fun i => l.getD i.val 0) ?_ ?_ ?_
  · intro i j hij
    simp only [hget] at hij
    have := (List.nodup_iff_injective_get.mp hnd) hij
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · intro i
    have h := hadj i.val (by rw [hk]; exact i.isLt)
    have hv : ((i + 1 : Fin (k + 3)) : ℕ) = (i.val + 1) % l.length := by
      have h1 : ((1 : Fin (k + 3)) : ℕ) = 1 := by
        rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < k + 3)]
      rw [Fin.val_add, h1, hk]
    rw [G_adj]
    rw [hv]; exact h
  · intro i
    rw [hget]
    exact hS _ (List.get_mem _ _)

/-! ## Bitmask enumeration of `k`-subsets -/

/-- The bitmask of a list of vertices. -/
def maskL (l : List (Fin 29)) : ℕ := l.foldr (fun v m => m ||| 2 ^ (v : ℕ)) 0

lemma testBit_maskL (l : List (Fin 29)) (v : Fin 29) : (maskL l).testBit v = true ↔ v ∈ l := by
  induction l with
  | nil => simp [maskL]
  | cons a l ih =>
    show (maskL l ||| 2 ^ (a : ℕ)).testBit v = true ↔ v ∈ a :: l
    rw [Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true, ih, decide_eq_true_eq,
      List.mem_cons, Fin.val_inj]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h.symm
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h

/-- `allSub Q L k acc`: for every `k`-element sublist `T` of `L`, `Q (acc ||| mask T)` holds. -/
def allSub (Q : ℕ → Bool) : List (Fin 29) → ℕ → ℕ → Bool
  | _, 0, acc => Q acc
  | [], _ + 1, _ => true
  | a :: L, k + 1, acc => allSub Q L (k + 1) acc && allSub Q L k (acc ||| 2 ^ (a : ℕ))

lemma allSub_sound (Q : ℕ → Bool) (L : List (Fin 29)) : ∀ (k acc : ℕ), allSub Q L k acc = true →
    ∀ B : Finset (Fin 29), B ⊆ L.toFinset → B.card = k →
      ∃ m, Q m = true ∧ ∀ v : Fin 29, m.testBit v = true → acc.testBit v = true ∨ v ∈ B := by
  induction L with
  | nil =>
    intro k acc h B hB hc
    have hB0 : B = ∅ := by simpa using hB
    subst hB0
    rw [Finset.card_empty] at hc
    subst hc
    exact ⟨acc, by simpa [allSub] using h, fun v hv => Or.inl hv⟩
  | cons a L ih =>
    intro k acc h B hB hc
    cases k with
    | zero =>
      have : B = ∅ := Finset.card_eq_zero.1 hc
      subst this
      exact ⟨acc, by simpa [allSub] using h, fun v hv => Or.inl hv⟩
    | succ k =>
      simp only [allSub, Bool.and_eq_true] at h
      by_cases ha : a ∈ B
      · have hsub : B.erase a ⊆ L.toFinset := by
          intro x hx
          have hx' := hB (Finset.mem_of_mem_erase hx)
          rw [List.toFinset_cons, Finset.mem_insert] at hx'
          rcases hx' with rfl | hx'
          · exact absurd hx (Finset.notMem_erase _ _)
          · exact hx'
        have hcard : (B.erase a).card = k := by
          rw [Finset.card_erase_of_mem ha, hc]
          rfl
        obtain ⟨m, hm, hmv⟩ := ih k _ h.2 (B.erase a) hsub hcard
        refine ⟨m, hm, fun v hv => ?_⟩
        rcases hmv v hv with h1 | h1
        · rw [Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at h1
          rcases h1 with h1 | h1
          · exact Or.inl h1
          · right
            rw [show v = a from Fin.ext h1.symm]
            exact ha
        · exact Or.inr (Finset.mem_of_mem_erase h1)
      · refine ih (k + 1) acc h.1 B (fun x hx => ?_) hc
        have hx' := hB hx
        rw [List.toFinset_cons, Finset.mem_insert] at hx'
        rcases hx' with rfl | hx'
        · exact absurd hx ha
        · exact hx'

/-- The cycle test on a bitmask `m`: some cycle mask `c` has all its bits in `m`. -/
def cycTest (cm : List ℕ) (m : ℕ) : Bool := cm.any fun c => c &&& m == c

lemma hits_of_allSub (cyc : List (List (Fin 29))) (cm : List ℕ) (hcm : cm = cyc.map maskL)
    (L : List (Fin 29)) (k : ℕ) (Xl : List (Fin 29))
    (h : allSub (cycTest cm) L k (maskL Xl) = true) :
    ∀ B : Finset (Fin 29), B ⊆ L.toFinset → B.card = k →
      ∃ l ∈ cyc, ∀ v ∈ l, v ∈ Xl ∨ v ∈ B := by
  intro B hB hc
  obtain ⟨m, hm, hmv⟩ := allSub_sound _ L k _ h B hB hc
  rw [cycTest, hcm, List.any_map, List.any_eq_true] at hm
  obtain ⟨l, hl, hlm⟩ := hm
  refine ⟨l, hl, fun v hv => ?_⟩
  have h1 : (maskL l).testBit v = true := (testBit_maskL l v).2 hv
  have hlm' : maskL l &&& m = maskL l := by
    simpa only [Function.comp_apply, beq_iff_eq] using hlm
  have h2 : (maskL l &&& m).testBit v = true := by rw [hlm']; exact h1
  rw [Nat.testBit_land, Bool.and_eq_true] at h2
  rcases hmv v h2.2 with h3 | h3
  · exact Or.inl ((testBit_maskL Xl v).1 h3)
  · exact Or.inr h3

theorem card_inter_lt (S I : Finset (Fin 29)) (L Xl : List (Fin 29)) (cs : List (List (Fin 29)))
    (k : ℕ) (hcs : ∀ l ∈ cs, validCycle l = true) (hI : L.toFinset = I) (hX : ∀ v ∈ Xl, v ∈ S)
    (hh : ∀ B : Finset (Fin 29), B ⊆ L.toFinset → B.card = k → ∃ l ∈ cs, ∀ v ∈ l, v ∈ Xl ∨ v ∈ B)
    (hS : (G.induce (S : Set (Fin 29))).IsAcyclic) : (S ∩ I).card < k := by
  by_contra hlt
  rw [not_lt] at hlt
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hlt
  obtain ⟨l, hl, hlB⟩ := hh B (hI ▸ hBsub.trans Finset.inter_subset_right) hBcard
  refine not_isAcyclic_of_validCycle (S : Set (Fin 29)) l (hcs l hl) ?_ hS
  intro v hv
  rcases hlB v hv with h | h
  · exact Finset.mem_coe.2 (hX v h)
  · exact Finset.mem_coe.2 (Finset.mem_of_mem_inter_left (hBsub h))

/-! ## The two sides of the separating edge `{27, 28}` -/

''')
w(f'/-- The `Q` side (12 vertices). -/\ndef QI : Finset (Fin 29) := {fin(QI)}\n\n')
w(f'/-- The `R` side (15 vertices). -/\ndef RI : Finset (Fin 29) := {fin(RI)}\n\n')
w(f'def QL : List (Fin 29) := {lst(QI)}\n\nlemma QL_eq : QL.toFinset = QI := by decide +kernel\n\n')
w(f'def RL : List (Fin 29) := {lst(RI)}\n\nlemma RL_eq : RL.toFinset = RI := by decide +kernel\n\n')

keys = [('Q', '', '∅'), ('Q', '27', '{27}'), ('Q', '28', '{28}'), ('Q', '27,28', '{27, 28}'),
        ('R', '', '∅'), ('R', '27', '{27}'), ('R', '28', '{28}'), ('R', '27,28', '{27, 28}')]
names = {'': '0', '27': 'x', '28': 'y', '27,28': 'xy'}
for side, X, Xs in keys:
    k, cl = cyclist(f'{side}|{X}')
    nm = f'cyc{side}{names[X]}'
    w(f'/-- Cycles hitting every `{k}`-subset of the `{side}` side together with `{Xs}`. -/\n')
    w(f'def {nm} : List (List (Fin 29)) :=\n  {cl}\n\n')
    w(f'lemma {nm}_valid : ∀ l ∈ {nm}, validCycle l = true := by decide +kernel\n\n')
    masks = [sum(1 << v for v in c) for c in cyc[f'{side}|{X}'][1]]
    w(f'/-- Bitmasks of `{nm}`. -/\ndef m{nm} : List ℕ := {lst(masks)}\n\n')
    w(f'lemma m{nm}_eq : m{nm} = {nm}.map maskL := by decide +kernel\n\n')
open(os.path.join(HERE, 'AB_part1.lean'), 'w').write(''.join(out))
json.dump({'E': E, 'C': C}, open(os.path.join(HERE, 'g29_lean_data.json'), 'w'))
print('ok', len(E))
