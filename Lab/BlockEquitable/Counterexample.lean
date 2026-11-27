import Mathlib

/-!
# The gap-one conjecture for the equitable chromatic number of block graphs is false

An **equitable `q`-colouring** of a finite graph `G` on `n` vertices is a proper colouring with
`q` colours in which every colour class has `⌊n/q⌋` or `⌈n/q⌉` vertices; the **equitable chromatic
number** `χ_=(G)` is the least such `q`. For a vertex `v` let `α(G,v)` be the largest size of an
independent set containing `v`, let `α_min(G) = min_v α(G,v)`, and let
`L(G) = max {ω(G), ⌈(n+1)/(α_min(G)+1)⌉}` (a lower bound for `χ_=(G)`).

Dybizbański, Furmańczyk and Mkrtchyan (Discrete Appl. Math. 354 (2024)) conjectured that every
block graph (every block is a clique) satisfies `χ_=(G) ≤ L(G) + 1`.
Lauri (arXiv:2608.14517, Aug 2026) disproves this with connected block graphs `G_{d,k}` having
`L = k` and `χ_= = k + d`. We formalize the smallest member, `d = 2`, `k = 7`, a connected block
graph on 32 vertices with `L = 7` and `χ_= = 9`:

* `G_isBlockGraph`, `G_connected`;
* `cliqueNum_G : G.cliqueNum = 7`, `αmin_G : αmin G = 4`, `L_G : L G = 7`;
* `equitableChromaticNumber_G : equitableChromaticNumber G = 9`;
* `not_gapOneConjecture`: the conjecture is false (even restricted to connected block graphs).

## The graph (vertices are `Fin 32`)

* `Q = {0,…,6}` is a `K_7`; `v = 0`, `w = 1`, `c = 2`;
* `u = 7` is a pendant vertex at `c`;
* `B₁ = {8,…,13}` and `B₂ = {14,…,19}` are `K_6`'s whose vertices are all joined to `v`
  (so `B₁ ∪ {v}`, `B₂ ∪ {v}` are `K_7` blocks), and `B₃ = {20,…,25}`, `B₄ = {26,…,31}` likewise
  at `w`.

`blk a` names the part of `a` (`0` for `Q`, `1…4` for `Bᵢ`, `5` for `u`) and `anchor i` is the
cut vertex part `i` hangs from.

## Block graphs

We say `G` is a block graph if every set `S` of vertices that induces a connected subgraph which
stays connected after deleting any one vertex of `S` is a clique. Such an `S` is 2-connected (or
has at most two vertices), so it lies in one block; conversely every block induces such a
subgraph. Hence this says exactly that every block is a clique.

## Proof (following the paper)

* Independent sets meet each part in at most one vertex. The non-neighbours of `v` lie in
  `u, B₃, B₄`, so `α(G,v) ≤ 4`, and `α(G - u, v) ≤ 3`; similarly for `w` with `u, B₁, B₂`.
  Every vertex lies in an independent 4-set, so `α_min = 4` and `L = max(7, ⌈33/5⌉) = 7`.
* In an equitable `q`-colouring with `q ≤ 8` every class has at least `⌊32/q⌋ ≥ 4` vertices. But
  `v` and `w` get different colours, and one of their two classes misses `u`, so has at most 3
  vertices. Hence `χ_= ≥ 9`, and an explicit equitable 9-colouring gives `χ_= = 9 > L + 1 = 8`.
-/

namespace OpenProblemsLab.BlockEquitable

open Finset SimpleGraph

/-! ### Definitions -/

/-- `G` is a block graph: every vertex set inducing a connected subgraph that remains connected
after deleting any single vertex is a clique (equivalently, every block of `G` is complete). -/
def IsBlockGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, (G.induce S).Connected → (∀ x ∈ S, (G.induce (S \ {x})).Connected) → G.IsClique S

/-- `α(G,v)`: the largest size of an independent set containing `v`. -/
noncomputable def αAt {V : Type*} (G : SimpleGraph V) (v : V) : ℕ :=
  sSup {n | ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧ v ∈ s ∧ s.card = n}

/-- `α_min(G) = min_v α(G,v)`. -/
noncomputable def αmin {V : Type*} (G : SimpleGraph V) : ℕ := ⨅ v, αAt G v

/-- `L(G) = max {ω(G), ⌈(|V|+1)/(α_min(G)+1)⌉}` (ceiling written as a natural-number division). -/
noncomputable def L {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  max G.cliqueNum ((Fintype.card V + 1 + αmin G) / (αmin G + 1))

/-- `c` is an equitable colouring with `q` colours: proper, and every colour class has between
`⌊|V|/q⌋` and `⌈|V|/q⌉` vertices. -/
def IsEquitableColoring {V : Type*} [Fintype V] (G : SimpleGraph V) {q : ℕ} (c : V → Fin q) :
    Prop :=
  (∀ x y, G.Adj x y → c x ≠ c y) ∧
    ∀ i, Fintype.card V / q ≤ (univ.filter fun x => c x = i).card ∧
      (univ.filter fun x => c x = i).card ≤ (Fintype.card V + q - 1) / q

/-- The equitable chromatic number: the least `q` admitting an equitable `q`-colouring. -/
noncomputable def equitableChromaticNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {q | ∃ c : V → Fin q, IsEquitableColoring G c}

/-- **Gap-one conjecture** (Dybizbański–Furmańczyk–Mkrtchyan 2024): every finite block graph
satisfies `χ_=(G) ≤ L(G) + 1`. We state it for connected block graphs only, which makes its
negation stronger. -/
def GapOneConjecture : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → IsBlockGraph G →
    equitableChromaticNumber G ≤ L G + 1

/-! ### The graph `G_{2,7}` -/

/-- The part of a vertex: `0` for `Q`, `1…4` for `B₁…B₄`, `5` for `u`. -/
def blk (a : Fin 32) : ℕ := if a.1 < 7 then 0 else if a.1 = 7 then 5 else (a.1 - 8) / 6 + 1

/-- The cut vertex that part `i ≠ 0` hangs from. -/
def anchor (i : ℕ) : Fin 32 := if i ≤ 2 then 0 else if i ≤ 4 then 1 else 2

/-- Adjacency: same part, or one vertex is the anchor of the other's part. -/
def adjR (a b : Fin 32) : Prop :=
  a ≠ b ∧ (blk a = blk b ∨ (blk a ≠ 0 ∧ b = anchor (blk a)) ∨ (blk b ≠ 0 ∧ a = anchor (blk b)))

instance : DecidableRel adjR := fun a b => by unfold adjR; infer_instance

/-- `G_{2,7}`. -/
def G : SimpleGraph (Fin 32) where
  Adj := adjR
  symm := ⟨fun a b h => by unfold adjR at *; tauto⟩
  loopless := ⟨fun a h => h.1 rfl⟩

instance : DecidableRel G.Adj := inferInstanceAs (DecidableRel adjR)

/-! ### Finite facts -/

theorem same_blk_adj : ∀ a b : Fin 32, a ≠ b → blk a = blk b → G.Adj a b := by decide

/-- A vertex outside `Q` has neighbours only in its own part and its anchor. -/
theorem nbr_closed : ∀ a b : Fin 32, blk a ≠ 0 → G.Adj a b → b ≠ anchor (blk a) →
    blk b = blk a := by decide

theorem adj_anchor : ∀ a : Fin 32, blk a ≠ 0 → G.Adj a (anchor (blk a)) := by decide

theorem clique_bound : ∀ a b : Fin 32, G.Adj a b →
    (insert a (insert b (univ.filter fun z => G.Adj a z ∧ G.Adj b z))).card ≤ 7 := by
  decide +kernel

theorem reach_facts : ∀ x : Fin 32, x = 0 ∨ G.Adj 0 x ∨ ∃ y, G.Adj 0 y ∧ G.Adj y x := by decide

/-- Parts met by `v = 0` and its non-neighbours (all / avoiding `u = 7`), and likewise for `w`. -/
theorem parts_v : ((insert 0 (univ.filter fun y => ¬ G.Adj 0 y)).image blk).card = 4 := by
  decide
theorem parts_v' :
    ((insert 0 (univ.filter fun y => ¬ G.Adj 0 y ∧ y ≠ 7)).image blk).card = 3 := by decide
theorem parts_w' :
    ((insert 1 (univ.filter fun y => ¬ G.Adj 1 y ∧ y ≠ 7)).image blk).card = 3 := by decide

/-- Every vertex lies in an independent set of size 4. -/
def wit : List (List (Fin 32)) :=
  [[0,7,20,26],[1,7,8,14],[2,8,14,20],[3,7,8,14],[4,7,8,14],[5,7,8,14],[6,7,8,14],[0,7,20,26],
   [1,7,8,14],[1,7,9,14],[1,7,10,14],[1,7,11,14],[1,7,12,14],[1,7,13,14],[1,7,8,14],[1,7,8,15],
   [1,7,8,16],[1,7,8,17],[1,7,8,18],[1,7,8,19],[0,7,20,26],[0,7,21,26],[0,7,22,26],[0,7,23,26],
   [0,7,24,26],[0,7,25,26],[0,7,20,26],[0,7,20,27],[0,7,20,28],[0,7,20,29],[0,7,20,30],
   [0,7,20,31]]

theorem wit_ok : ∀ x : Fin 32,
    (∀ a ∈ (wit.getD x.1 []).toFinset, ∀ b ∈ (wit.getD x.1 []).toFinset, ¬ G.Adj a b) ∧
    x ∈ (wit.getD x.1 []).toFinset ∧ (wit.getD x.1 []).toFinset.card = 4 := by
  decide +kernel

/-- An explicit equitable 9-colouring (the paper's colouring, colours shifted to `0…8`). -/
def c9 : Fin 32 → Fin 9 :=
  ![0, 1, 2, 3, 4, 5, 6, 0, 1, 3, 4, 5, 7, 8, 1, 2, 4, 5, 7, 8, 0, 2, 3, 6, 7, 8, 0, 2, 3, 4, 5, 6]

theorem c9_equitable : IsEquitableColoring G c9 := by
  unfold IsEquitableColoring; simp only [Fintype.card_fin]; decide +kernel

/-! ### Block graph and connectivity -/

/-- In an induced subgraph, a walk starting in a set closed under adjacency stays in it. -/
theorem walk_closed {T : Set (Fin 32)} (P : Fin 32 → Prop)
    (h : ∀ x y : T, G.Adj x.1 y.1 → P x.1 → P y.1) {x y : T}
    (p : (G.induce T).Walk x y) (hx : P x.1) : P y.1 := by
  induction p with
  | nil => exact hx
  | cons hadj _ ih => exact ih (h _ _ hadj hx)

theorem G_isBlockGraph : IsBlockGraph G := by
  intro S hS hS' a ha b hb hab
  by_contra hna
  -- `a` and `b` lie in different parts, so one of them is outside `Q`; call it `a'`.
  have hdiff : blk a ≠ blk b := fun h => hna (same_blk_adj a b hab h)
  obtain ⟨a', b', ha', hb', hna', hblk⟩ : ∃ a' b', a' ∈ S ∧ b' ∈ S ∧ ¬ G.Adj a' b' ∧
      blk a' ≠ 0 ∧ blk b' ≠ blk a' := by
    by_cases h0 : blk a = 0
    · exact ⟨b, a, hb, ha, fun h => hna h.symm, by omega, by omega⟩
    · exact ⟨a, b, ha, hb, hna, h0, Ne.symm hdiff⟩
  set z := anchor (blk a')
  have hbz : b' ≠ z := fun h => hna' (h ▸ adj_anchor a' hblk.1)
  have haz : a' ≠ z := (adj_anchor a' hblk.1).ne
  -- `T` is `S` minus `z`; it induces a connected subgraph containing `a'` and `b'`.
  obtain ⟨T, hT, hzT, haT, hbT⟩ : ∃ T : Set (Fin 32), (G.induce T).Connected ∧ z ∉ T ∧
      a' ∈ T ∧ b' ∈ T := by
    by_cases hz : z ∈ S
    · exact ⟨S \ {z}, hS' z hz, by simp, ⟨ha', haz⟩, ⟨hb', hbz⟩⟩
    · exact ⟨S, hS, hz, ha', hb'⟩
  obtain ⟨p⟩ := hT.preconnected ⟨a', haT⟩ ⟨b', hbT⟩
  have := walk_closed (T := T) (fun y => blk y = blk a')
    (fun x y hxy hx => by
      have hyz : y.1 ≠ z := fun h => hzT (h ▸ y.2)
      have h0 : blk x.1 ≠ 0 := hx ▸ hblk.1
      have hyz' : y.1 ≠ anchor (blk x.1) := by rw [hx]; exact hyz
      exact (nbr_closed _ _ h0 hxy hyz').trans hx) p rfl
  exact hblk.2 this

theorem G_connected : G.Connected := by
  have h0 : ∀ x, G.Reachable 0 x := by
    intro x
    rcases reach_facts x with rfl | h | ⟨y, h1, h2⟩
    · rfl
    · exact h.reachable
    · exact h1.reachable.trans h2.reachable
  exact ⟨fun x y => (h0 x).symm.trans (h0 y)⟩

/-! ### Clique number, `α_min` and `L` -/

theorem clique_card_le (s : Finset (Fin 32)) (hs : G.IsClique (s : Set (Fin 32))) :
    s.card ≤ 7 := by
  by_cases h2 : s.card ≤ 1
  · omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (show 1 < s.card by omega)
  refine le_trans (card_le_card ?_) (clique_bound a b (hs ha hb hab))
  intro z hz
  by_cases hza : z = a
  · simp [hza]
  by_cases hzb : z = b
  · simp [hzb]
  simp only [mem_insert, mem_filter, mem_univ, true_and]
  exact Or.inr (Or.inr ⟨hs ha hz (Ne.symm hza), hs hb hz (Ne.symm hzb)⟩)

theorem cliqueNum_G : G.cliqueNum = 7 := by
  apply le_antisymm
  · obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
    rw [← hs.card_eq]; exact clique_card_le s hs.isClique
  · have hQ : G.IsClique ((univ.filter fun a : Fin 32 => a.1 < 7 : Finset (Fin 32)) :
        Set (Fin 32)) := by
      intro a ha b hb hab
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      exact same_blk_adj a b hab (by simp [blk, ha, hb])
    have : (univ.filter fun a : Fin 32 => a.1 < 7).card = 7 := by decide
    rw [← this]; exact hQ.card_le_cliqueNum

/-- Independent sets meet each part at most once, so their size is bounded by the number of
parts met by any superset. -/
theorem indep_card_le (s R : Finset (Fin 32)) (hs : G.IsIndepSet (s : Set (Fin 32)))
    (hR : s ⊆ R) : s.card ≤ (R.image blk).card := by
  rw [← card_image_of_injOn (f := blk) (fun x hx y hy hxy => by
    by_contra hne; exact hs hx hy hne (same_blk_adj x y hne hxy))]
  exact card_le_card (image_subset_image hR)

theorem indep_sub (s : Finset (Fin 32)) (hs : G.IsIndepSet (s : Set (Fin 32))) (x : Fin 32)
    (hx : x ∈ s) (h7 : (7 : Fin 32) ∉ s) :
    s ⊆ insert x (univ.filter fun y => ¬ G.Adj x y ∧ y ≠ 7) := by
  intro y hy
  by_cases hyx : y = x
  · simp [hyx]
  simp only [mem_insert, mem_filter, mem_univ, true_and]
  exact Or.inr ⟨hs hx hy (Ne.symm hyx), fun h => h7 (h ▸ hy)⟩

theorem αAt_zero_le : αAt G 0 ≤ 4 := by
  refine csSup_le ⟨1, {0}, by simp, by simp, by simp⟩ ?_
  rintro n ⟨s, hs, h0, rfl⟩
  rw [← parts_v]
  refine indep_card_le s _ hs fun y hy => ?_
  by_cases hy0 : y = 0
  · simp [hy0]
  simp only [mem_insert, mem_filter, mem_univ, true_and]
  exact Or.inr (hs h0 hy (Ne.symm hy0))

theorem four_le_αAt (x : Fin 32) : 4 ≤ αAt G x := by
  obtain ⟨h1, h2, h3⟩ := wit_ok x
  refine le_csSup ⟨32, ?_⟩ ⟨_, fun a ha b hb _ => h1 a ha b hb, h2, h3⟩
  rintro n ⟨s, -, -, rfl⟩
  simpa using card_le_univ s

theorem αmin_G : αmin G = 4 :=
  le_antisymm ((ciInf_le (OrderBot.bddBelow _) 0).trans αAt_zero_le) (le_ciInf four_le_αAt)

theorem L_G : L G = 7 := by
  rw [L, cliqueNum_G, αmin_G, Fintype.card_fin]
  norm_num

/-! ### The equitable chromatic number is 9 -/

/-- No equitable colouring with at most 8 colours: the class of `v` or of `w` misses `u` and
so has at most 3 vertices, while every class needs at least `⌊32/q⌋ ≥ 4`. -/
theorem no_equitable_le_eight (q : ℕ) (hq : q ≤ 8) (c : Fin 32 → Fin q) :
    ¬ IsEquitableColoring G c := by
  rintro ⟨hp, hcl⟩
  have hq1 : 0 < q := (c 0).pos
  have small : ∀ x : Fin 32,
      ((insert x (univ.filter fun y => ¬ G.Adj x y ∧ y ≠ 7)).image blk).card = 3 →
      c 7 ≠ c x → False := by
    intro x hpart h7
    set s := univ.filter fun y => c y = c x
    have hs : G.IsIndepSet (s : Set (Fin 32)) := by
      intro a ha b hb _ hab
      simp only [s, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      exact hp a b hab (ha.trans hb.symm)
    have hcard : s.card ≤ 3 :=
      hpart ▸ indep_card_le s _ hs (indep_sub s hs x (by simp [s]) (by simpa [s] using h7))
    have hlow : 32 / q ≤ s.card := by
      have := (hcl (c x)).1
      rwa [Fintype.card_fin] at this
    have : 4 ≤ 32 / q := (Nat.le_div_iff_mul_le hq1).2 (by omega)
    omega
  by_cases h : c 7 = c 0
  · exact small 1 parts_w' (fun h' => hp 0 1 (by decide) (h.symm.trans h'))
  · exact small 0 parts_v' h

theorem equitableChromaticNumber_G : equitableChromaticNumber G = 9 := by
  apply le_antisymm (Nat.sInf_le (show 9 ∈ {q | ∃ c : Fin 32 → Fin q, IsEquitableColoring G c}
    from ⟨c9, c9_equitable⟩))
  refine le_csInf ⟨9, c9, c9_equitable⟩ fun q ⟨c, hc⟩ => ?_
  by_contra h
  exact no_equitable_le_eight q (by omega) c hc

/-! ### The conjecture is false -/

/-- `G_{2,7}` is a connected block graph with `χ_=(G) = 9 > 8 = L(G) + 1`. -/
theorem not_gapOneConjecture : ¬ GapOneConjecture := by
  intro h
  have := h (Fin 32) G G_connected G_isBlockGraph
  rw [equitableChromaticNumber_G, L_G] at this
  omega

theorem exists_counterexample : ∃ G : SimpleGraph (Fin 32), G.Connected ∧ IsBlockGraph G ∧
    L G = 7 ∧ equitableChromaticNumber G = 9 :=
  ⟨G, G_connected, G_isBlockGraph, L_G, equitableChromaticNumber_G⟩

end OpenProblemsLab.BlockEquitable
