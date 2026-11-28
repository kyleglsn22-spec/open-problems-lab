import Mathlib

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
  [(0, 5), (0, 6), (0, 11), (0, 12), (0, 13), (1, 2), (1, 3), (1, 4), (1, 7), (1, 9), (2, 3), (2, 4), (2, 8), (2, 10), (3, 7), (3, 8), (3, 19), (4, 9), (4, 10), (4, 18), (5, 6), (5, 11), (5, 14), (5, 22), (6, 12), (6, 14), (6, 23), (7, 9), (7, 16), (7, 19), (8, 10), (8, 17), (8, 19), (9, 16), (9, 18), (10, 17), (10, 18), (11, 13), (11, 22), (11, 24), (12, 13), (12, 23), (12, 25), (13, 24), (13, 25), (14, 22), (14, 23), (14, 26), (15, 20), (15, 21), (15, 24), (15, 25), (15, 27), (16, 18), (16, 19), (16, 27), (16, 28), (17, 18), (17, 19), (17, 27), (17, 28), (18, 28), (19, 27), (20, 22), (20, 24), (20, 26), (20, 27), (20, 28), (21, 23), (21, 25), (21, 26), (21, 27), (21, 28), (22, 24), (22, 26), (23, 25), (23, 26), (24, 25), (26, 28), (27, 28)]

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

/-- The `Q` side (12 vertices). -/
def QI : Finset (Fin 29) := {1, 2, 3, 4, 7, 8, 9, 10, 16, 17, 18, 19}

/-- The `R` side (15 vertices). -/
def RI : Finset (Fin 29) := {0, 5, 6, 11, 12, 13, 14, 15, 20, 21, 22, 23, 24, 25, 26}

def QL : List (Fin 29) := [1, 2, 3, 4, 7, 8, 9, 10, 16, 17, 18, 19]

lemma QL_eq : QL.toFinset = QI := by decide +kernel

def RL : List (Fin 29) := [0, 5, 6, 11, 12, 13, 14, 15, 20, 21, 22, 23, 24, 25, 26]

lemma RL_eq : RL.toFinset = RI := by decide +kernel

/-- Cycles hitting every `7`-subset of the `Q` side together with `∅`. -/
def cycQ0 : List (List (Fin 29)) :=
  [[2, 8, 3],
    [4, 18, 9],
    [7, 19, 16],
    [10, 18, 17],
    [1, 4, 2],
    [1, 9, 7],
    [8, 19, 17],
    [9, 18, 16],
    [1, 7, 3],
    [2, 10, 4],
    [3, 19, 8],
    [8, 17, 10],
    [1, 3, 2],
    [1, 9, 4],
    [2, 10, 8],
    [3, 19, 7],
    [4, 18, 10],
    [7, 16, 9],
    [16, 18, 17, 19],
    [1, 4, 18, 17, 8, 3],
    [1, 7, 16, 18, 17, 8, 2],
    [4, 10, 17, 19, 16, 9],
    [2, 10, 17, 19, 3],
    [3, 8, 17, 18, 16, 7],
    [2, 8, 17, 18, 4],
    [2, 4, 18, 16, 7, 3],
    [1, 9, 16, 19, 17, 10, 2],
    [1, 7, 16, 18, 4],
    [1, 4, 10, 17, 19, 3],
    [2, 4, 9, 16, 19, 3],
    [1, 9, 16, 19, 3]]

lemma cycQ0_valid : ∀ l ∈ cycQ0, validCycle l = true := by decide +kernel

/-- Bitmasks of `cycQ0`. -/
def mcycQ0 : List ℕ := [268, 262672, 589952, 394240, 22, 642, 655616, 328192, 138, 1044, 524552, 132352, 14, 530, 1284, 524424, 263184, 66176, 983040, 393498, 459142, 722448, 656396, 459144, 393492, 327836, 722438, 327826, 656410, 590364, 590346]

lemma mcycQ0_eq : mcycQ0 = cycQ0.map maskL := by decide +kernel

/-- Cycles hitting every `7`-subset of the `Q` side together with `{27}`. -/
def cycQx : List (List (Fin 29)) :=
  [[16, 27, 19],
    [2, 8, 3],
    [4, 18, 9],
    [10, 18, 17],
    [1, 9, 7],
    [1, 4, 2],
    [8, 17, 10],
    [3, 19, 7],
    [16, 27, 17, 18],
    [2, 10, 4],
    [1, 7, 3],
    [8, 19, 17],
    [7, 16, 9],
    [1, 9, 4],
    [2, 10, 8],
    [1, 3, 2],
    [4, 18, 10],
    [3, 19, 8],
    [9, 18, 16]]

lemma cycQx_valid : ∀ l ∈ cycQx, validCycle l = true := by decide +kernel

/-- Bitmasks of `cycQx`. -/
def mcycQx : List ℕ := [134807552, 268, 262672, 394240, 642, 22, 132352, 524424, 134676480, 1044, 138, 655616, 66176, 530, 1284, 14, 263184, 524552, 328192]

lemma mcycQx_eq : mcycQx = cycQx.map maskL := by decide +kernel

/-- Cycles hitting every `7`-subset of the `Q` side together with `{28}`. -/
def cycQy : List (List (Fin 29)) :=
  [[16, 28, 18],
    [2, 8, 3],
    [1, 9, 4],
    [3, 19, 7],
    [8, 17, 10],
    [2, 10, 4],
    [1, 9, 7],
    [16, 28, 17, 19],
    [4, 18, 9],
    [10, 18, 17],
    [1, 4, 2],
    [7, 16, 9],
    [8, 19, 17],
    [1, 7, 3],
    [3, 19, 8],
    [2, 10, 8],
    [1, 3, 2],
    [7, 19, 16],
    [4, 18, 10]]

lemma cycQy_valid : ∀ l ∈ cycQy, validCycle l = true := by decide +kernel

/-- Bitmasks of `cycQy`. -/
def mcycQy : List ℕ := [268763136, 268, 530, 524424, 132352, 1044, 642, 269156352, 262672, 394240, 22, 66176, 655616, 138, 524552, 1284, 14, 589952, 263184]

lemma mcycQy_eq : mcycQy = cycQy.map maskL := by decide +kernel

/-- Cycles hitting every `6`-subset of the `Q` side together with `{27, 28}`. -/
def cycQxy : List (List (Fin 29)) :=
  [[17, 28, 27],
    [16, 28, 27],
    [2, 8, 3],
    [4, 18, 9],
    [1, 9, 7],
    [3, 19, 7],
    [2, 10, 4],
    [8, 19, 27, 28, 18, 10],
    [1, 4, 2],
    [3, 19, 8],
    [2, 10, 8],
    [4, 18, 10],
    [1, 3, 2],
    [1, 9, 4],
    [1, 7, 3],
    [7, 19, 27, 28, 18, 9],
    [1, 7, 19, 8, 2],
    [1, 9, 18, 10, 2],
    [1, 9, 18, 28, 27, 19, 8, 2],
    [2, 8, 19, 27, 28, 18, 4],
    [2, 10, 18, 9, 7, 3],
    [2, 8, 19, 7, 9, 4],
    [4, 10, 8, 19, 7, 9],
    [3, 8, 10, 4, 9, 7],
    [1, 9, 18, 28, 27, 19, 3],
    [1, 7, 19, 27, 28, 18, 10, 2],
    [3, 8, 10, 18, 9, 7],
    [1, 7, 19, 8, 10, 4],
    [1, 7, 19, 27, 28, 18, 4],
    [2, 10, 18, 28, 27, 19, 3],
    [1, 9, 18, 10, 8, 3]]

lemma cycQxy_valid : ∀ l ∈ cycQxy, validCycle l = true := by decide +kernel

/-- Bitmasks of `cycQxy`. -/
def mcycQxy : List ℕ := [402784256, 402718720, 268, 262672, 642, 524424, 1044, 403440896, 22, 524552, 1284, 263184, 14, 530, 138, 403440256, 524678, 263686, 403440390, 403439892, 263820, 525204, 526224, 1944, 403440138, 403440774, 264072, 525714, 403439762, 403440652, 263946]

lemma mcycQxy_eq : mcycQxy = cycQxy.map maskL := by decide +kernel

/-- Cycles hitting every `9`-subset of the `R` side together with `∅`. -/
def cycR0 : List (List (Fin 29)) :=
  [[0, 13, 11],
    [6, 23, 14],
    [15, 25, 24],
    [20, 26, 22],
    [0, 6, 5],
    [21, 26, 23],
    [12, 25, 13],
    [5, 22, 11],
    [15, 20, 24],
    [15, 21, 25],
    [5, 22, 14],
    [0, 12, 6],
    [11, 24, 13],
    [12, 25, 23],
    [5, 14, 6],
    [0, 13, 12],
    [0, 11, 5],
    [11, 24, 22],
    [13, 25, 24],
    [6, 23, 12],
    [20, 26, 21, 25, 24],
    [15, 20, 26, 23, 25],
    [15, 21, 26, 22, 24],
    [15, 21, 26, 20],
    [5, 14, 23, 12, 13, 11],
    [6, 14, 22, 11, 13, 12],
    [11, 22, 14, 23, 12, 13],
    [0, 12, 23, 14, 22, 11]]

lemma cycR0_valid : ∀ l ∈ cycR0, validCycle l = true := by decide +kernel

/-- Bitmasks of `cycR0`. -/
def mcycR0 : List ℕ := [10241, 8405056, 50364416, 72351744, 97, 77594624, 33566720, 4196384, 17858560, 35684352, 4210720, 4161, 16787456, 41947136, 16480, 12289, 2081, 20973568, 50339840, 8392768, 120586240, 110133248, 90210304, 70287360, 8419360, 4225088, 12613632, 12605441]

lemma mcycR0_eq : mcycR0 = cycR0.map maskL := by decide +kernel

/-- Cycles hitting every `8`-subset of the `R` side together with `{27}`. -/
def cycRx : List (List (Fin 29)) :=
  [[15, 27, 21],
    [15, 27, 20],
    [0, 13, 11],
    [6, 23, 14],
    [13, 25, 24],
    [5, 22, 11],
    [20, 27, 21, 26],
    [0, 12, 6],
    [12, 25, 23],
    [14, 26, 22],
    [20, 24, 22],
    [5, 14, 6],
    [21, 26, 23],
    [0, 11, 5],
    [0, 13, 12],
    [11, 24, 13],
    [0, 6, 5],
    [15, 25, 24],
    [12, 25, 13],
    [21, 25, 23],
    [6, 23, 12],
    [14, 26, 23],
    [5, 22, 14],
    [11, 24, 22],
    [20, 27, 21, 25, 24],
    [20, 26, 22],
    [20, 26, 23, 25, 24],
    [5, 11, 24, 25, 12, 6],
    [5, 22, 26, 23, 6],
    [21, 26, 22, 24, 25],
    [0, 12, 25, 24, 11],
    [5, 11, 13, 25, 23, 6],
    [5, 22, 24, 13, 12, 6],
    [0, 13, 25, 23, 26, 22, 5],
    [5, 14, 23, 12, 13, 11],
    [5, 14, 26, 21, 25, 24, 11],
    [0, 13, 25, 23, 6],
    [0, 11, 22, 26, 23, 6],
    [11, 22, 14, 23, 12, 13],
    [0, 12, 25, 21, 26, 14, 5],
    [0, 12, 23, 14, 5],
    [12, 23, 21, 27, 20, 24, 13],
    [6, 14, 22, 11, 13, 12],
    [11, 22, 20, 27, 21, 25, 13],
    [0, 13, 24, 22, 5],
    [11, 22, 26, 23, 25, 13],
    [12, 23, 26, 22, 24, 13],
    [0, 12, 25, 24, 20, 26, 14, 5],
    [5, 14, 23, 21, 27, 20, 24, 11],
    [5, 14, 26, 20, 24, 11],
    [6, 14, 22, 20, 27, 21, 25, 12],
    [0, 12, 25, 21, 27, 20, 22, 11],
    [0, 13, 24, 20, 27, 21, 23, 14, 5],
    [6, 14, 26, 21, 25, 12],
    [6, 14, 26, 20, 24, 25, 12],
    [0, 12, 23, 26, 22, 5],
    [0, 11, 22, 14, 6],
    [0, 12, 23, 21, 27, 20, 24, 11],
    [0, 12, 23, 14, 22, 11],
    [0, 11, 24, 25, 21, 26, 14, 6],
    [0, 13, 25, 21, 27, 20, 22, 14, 6],
    [0, 11, 24, 20, 26, 14, 6],
    [0, 13, 24, 22, 26, 23, 6]]

lemma cycRx_valid : ∀ l ∈ cycRx, validCycle l = true := by decide +kernel

/-- Bitmasks of `cycRx`. -/
def mcycRx : List ℕ := [136347648, 135299072, 10241, 8405056, 50339840, 4196384, 204472320, 4161, 41947136, 71319552, 22020096, 16480, 77594624, 2081, 12289, 16787456, 97, 50364416, 33566720, 44040192, 8392768, 75513856, 4210720, 20973568, 187695104, 72351744, 126877696, 50337888, 79691872, 123731968, 50337793, 41953376, 20983904, 113254433, 8419360, 119556128, 41951297, 79693889, 12613632, 102780961, 8409121, 162541568, 4225088, 175122432, 20979745, 113256448, 96481280, 118509601, 162547744, 84953120, 175132736, 175118337, 162553889, 102780992, 118509632, 79695905, 4212801, 162535425, 12605441, 119556161, 175136833, 84953153, 96477249]

lemma mcycRx_eq : mcycRx = cycRx.map maskL := by decide +kernel

/-- Cycles hitting every `8`-subset of the `R` side together with `{28}`. -/
def cycRy : List (List (Fin 29)) :=
  [[20, 28, 26],
    [21, 28, 26],
    [0, 13, 11],
    [6, 23, 14],
    [15, 25, 24],
    [5, 22, 14],
    [0, 12, 6],
    [15, 21, 28, 20],
    [12, 25, 23],
    [11, 24, 22],
    [13, 25, 24],
    [0, 6, 5],
    [0, 13, 12],
    [5, 22, 11],
    [11, 24, 13],
    [12, 25, 13],
    [0, 11, 5],
    [20, 24, 22],
    [6, 23, 12],
    [21, 25, 23],
    [5, 14, 6],
    [14, 26, 23],
    [14, 26, 22],
    [20, 28, 21, 25, 24],
    [15, 20, 24],
    [15, 21, 25],
    [5, 14, 23, 12, 13, 11],
    [11, 22, 14, 23, 12, 13],
    [6, 14, 22, 11, 13, 12],
    [11, 22, 20, 15, 25, 13],
    [14, 23, 21, 15, 24, 22],
    [0, 12, 23, 14, 22, 11],
    [0, 13, 25, 23, 6],
    [0, 12, 23, 14, 5],
    [0, 13, 24, 22, 5],
    [12, 23, 21, 15, 24, 13],
    [14, 23, 25, 15, 20, 22],
    [0, 11, 22, 14, 6],
    [5, 22, 26, 23, 6],
    [5, 11, 13, 25, 23, 6],
    [5, 22, 24, 13, 12, 6],
    [0, 13, 25, 23, 26, 22, 5],
    [0, 13, 25, 21, 28, 20, 22, 14, 6],
    [12, 23, 21, 28, 20, 24, 13],
    [0, 11, 22, 26, 23, 6],
    [6, 14, 22, 20, 28, 21, 25, 12],
    [0, 12, 25, 15, 20, 22, 11],
    [6, 14, 22, 24, 13, 12],
    [0, 13, 24, 22, 14, 6],
    [0, 13, 25, 15, 20, 22, 5],
    [0, 13, 24, 15, 21, 23, 14, 5],
    [0, 12, 23, 21, 28, 20, 24, 11],
    [11, 22, 26, 23, 25, 13],
    [5, 14, 23, 21, 15, 24, 11],
    [12, 23, 26, 22, 24, 13],
    [0, 13, 25, 15, 20, 22, 14, 6],
    [0, 13, 24, 20, 28, 21, 23, 14, 5],
    [0, 12, 23, 26, 22, 5],
    [0, 12, 23, 21, 15, 24, 11],
    [0, 12, 23, 21, 15, 24, 22, 5],
    [11, 22, 20, 28, 21, 25, 13],
    [5, 14, 23, 21, 28, 20, 24, 11],
    [6, 14, 22, 20, 15, 25, 12],
    [0, 11, 22, 20, 15, 25, 23, 6],
    [0, 13, 24, 22, 26, 23, 6],
    [0, 13, 24, 15, 21, 23, 6],
    [5, 22, 24, 15, 21, 23, 6],
    [0, 12, 25, 21, 28, 20, 22, 11],
    [5, 22, 20, 15, 25, 23, 6],
    [5, 14, 23, 25, 13, 11],
    [0, 13, 25, 23, 14, 5]]

lemma cycRy_valid : ∀ l ∈ cycRy, validCycle l = true := by decide +kernel

/-- Bitmasks of `cycRy`. -/
def mcycRy : List ℕ := [336592896, 337641472, 10241, 8405056, 50364416, 4210720, 4161, 271613952, 41947136, 20973568, 50339840, 97, 12289, 4196384, 16787456, 33566720, 2081, 22020096, 8392768, 44040192, 16480, 75513856, 71319552, 321912832, 17858560, 35684352, 8419360, 12613632, 4225088, 38840320, 31506432, 12605441, 41951297, 8409121, 20979745, 27308032, 47235072, 4212801, 79691872, 41953376, 20983904, 113254433, 309354561, 296759296, 79693889, 309350464, 38836225, 21000256, 20996161, 38838305, 27320353, 296753153, 113256448, 27314208, 96481280, 38854721, 296771617, 79695905, 27301889, 31494177, 309340160, 296765472, 38850624, 47220801, 96477249, 27304001, 31490144, 309336065, 47218784, 41969696, 41967649]

lemma mcycRy_eq : mcycRy = cycRy.map maskL := by decide +kernel

/-- Cycles hitting every `8`-subset of the `R` side together with `{27, 28}`. -/
def cycRxy : List (List (Fin 29)) :=
  [[20, 28, 27],
    [15, 27, 21],
    [21, 28, 26],
    [0, 13, 11],
    [6, 23, 14],
    [13, 25, 24],
    [5, 22, 11],
    [0, 12, 6],
    [12, 25, 23],
    [14, 26, 22],
    [15, 25, 24],
    [5, 14, 6],
    [0, 13, 12],
    [11, 24, 13],
    [0, 6, 5],
    [14, 26, 23],
    [15, 27, 28, 26, 22, 24],
    [5, 22, 14],
    [11, 24, 22],
    [0, 11, 5],
    [6, 23, 12],
    [12, 25, 13],
    [15, 27, 28, 26, 23, 25]]

lemma cycRxy_valid : ∀ l ∈ cycRxy, validCycle l = true := by decide +kernel

/-- Bitmasks of `cycRxy`. -/
def mcycRxy : List ℕ := [403701760, 136347648, 337641472, 10241, 8405056, 50339840, 4196384, 4161, 41947136, 71319552, 50364416, 16480, 12289, 16787456, 97, 75513856, 490766336, 4210720, 20973568, 2081, 8392768, 33566720, 511737856]

lemma mcycRxy_eq : mcycRxy = cycRxy.map maskL := by decide +kernel

end OpenProblemsLab.AlbertsonBerman
