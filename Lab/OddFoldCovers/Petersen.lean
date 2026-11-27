import Mathlib

/-!
# Edge-colouring odd-fold covers: the Chen–van der Holst–Luo–Ma conjecture is false

For a loopless multigraph `G` and odd `ℓ ≥ 3`, let `s_ℓ(G)` be the least chromatic index of a
cyclic `ℓ`-fold cover of `G` (vertex set `V × ℤ/ℓ`, voltages `α : E → ℤ/ℓ`), and let
`L_ℓ(G) = max(Δ(G), max_{S odd, |S| ≥ 3} ⌈2ℓ|E(G[S])| / (ℓ|S| − 1)⌉)`, a lower bound for
`s_ℓ(G)`. Chen, van der Holst, Luo and Ma (Conjecture 1 of their paper on edge-colouring spectra
of cyclic covers) conjectured `s_ℓ(G) = L_ℓ(G)`.

R. Wang (arXiv:2611.13394, Corollary 1.4) disproved it: replace each vertex of the Petersen graph
by a triangle with `(3ℓ − 1)/2` parallel edges per side and each Petersen edge by an edge between
corners. The resulting `3ℓ`-regular multigraph `F_ℓ` on `30` vertices has `L_ℓ = 3ℓ` but
`s_ℓ = 3ℓ + 1`. We formalize the case `ℓ = 3` (a `9`-regular multigraph with `135` edges):

* `F_L`: `L_3(F) = 9` (every odd vertex set has at least `3` edges leaving it).
* `no_nine_colouring`: no cyclic `3`-fold cover of `F` has a proper `9`-edge-colouring. Each
  colour class would induce a perfect matching of the Petersen graph, with every edge used `3`
  times by the `9` classes, but a perfect matching of the Petersen graph has `1` or `5` spokes,
  and `9` numbers that are `1 mod 4` cannot add up to `15` (Wang's spoke count).
* `F_sCyc`: `s_3(F) ≥ 10`, and `not_conjecture`.

(Wang also shows `s_3(F) = 10` and gives a simple-graph counterexample; neither is formalized here.)
-/

namespace OpenProblemsLab.OddFoldCovers

open Finset

/-- A loopless multigraph with vertex type `V` and edge type `E`; each edge has a reference
orientation `src e → tgt e`. Parallel edges are allowed. -/
structure Multigraph (V E : Type*) where
  src : E → V
  tgt : E → V
  loopless : ∀ e, src e ≠ tgt e

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E)

/-- `v` is an end of `e`. -/
def Inc (v : V) (e : E) : Prop := G.src e = v ∨ G.tgt e = v

instance [DecidableEq V] (v : V) : DecidablePred (G.Inc v) :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Proper `k`-edge-colouring: distinct edges sharing an end get distinct colours. -/
def IsProper {k : ℕ} (c : E → Fin k) : Prop :=
  ∀ e e', e ≠ e' → ∀ v, G.Inc v e → G.Inc v e' → c e ≠ c e'

/-- Chromatic index. -/
noncomputable def chromaticIndex : ℕ := sInf {k | ∃ c : E → Fin k, G.IsProper c}

/-- The cyclic `ℓ`-fold cover with voltage assignment `α`: edge `(e, i)` joins
`(src e, i)` to `(tgt e, i + α e)`. -/
def cover (ℓ : ℕ) (α : E → ZMod ℓ) : Multigraph (V × ZMod ℓ) (E × ZMod ℓ) where
  src f := (G.src f.1, f.2)
  tgt f := (G.tgt f.1, f.2 + α f.1)
  loopless f h := G.loopless f.1 (congrArg Prod.fst h)

/-- `s_ℓ(G)`: least chromatic index of a cyclic `ℓ`-fold cover. -/
noncomputable def sCyc (ℓ : ℕ) : ℕ :=
  sInf {k | ∃ α : E → ZMod ℓ, (G.cover ℓ α).chromaticIndex = k}

variable [Fintype E] [DecidableEq V]

def degree (v : V) : ℕ := (univ.filter (G.Inc v)).card

/-- Number of edges with both ends in `S`. -/
def edgesIn (S : Finset V) : ℕ := (univ.filter fun e => G.src e ∈ S ∧ G.tgt e ∈ S).card

/-- `L_ℓ(G) = max(Δ(G), max over odd S, |S| ≥ 3, of ⌈2ℓ|E(G[S])| / (ℓ|S| − 1)⌉)`. -/
noncomputable def L [Fintype V] (ℓ : ℕ) : ℕ :=
  max (univ.sup G.degree)
    ((univ.powerset.filter fun S : Finset V => Odd S.card ∧ 3 ≤ S.card).sup fun S =>
      ⌈(2 * ℓ * G.edgesIn S : ℚ) / (ℓ * S.card - 1)⌉₊)

/-- Handshake for a set `S` and an edge class `Q`. -/
lemma handshake (S : Finset V) (Q : E → Prop) [DecidablePred Q] :
    ∑ v ∈ S, (univ.filter fun e => Q e ∧ G.Inc v e).card =
      2 * (univ.filter fun e => Q e ∧ G.src e ∈ S ∧ G.tgt e ∈ S).card +
        (univ.filter fun e => Q e ∧ (G.src e ∈ S ↔ G.tgt e ∉ S)).card := by
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun e _ => ?_
  have hne := G.loopless e
  have : ∀ v, (if Q e ∧ G.Inc v e then (1 : ℕ) else 0) =
      (if Q e then 1 else 0) * ((if v = G.src e then 1 else 0) + (if v = G.tgt e then 1 else 0)) := by
    intro v
    by_cases hq : Q e <;> by_cases h1 : v = G.src e <;> by_cases h2 : v = G.tgt e <;>
      simp_all [Inc, eq_comm]
  simp only [this, ← mul_sum, sum_add_distrib, sum_ite_eq']
  by_cases hq : Q e <;> by_cases h1 : G.src e ∈ S <;> by_cases h2 : G.tgt e ∈ S <;> simp [hq, h1, h2]

omit [Fintype E] in
lemma cover_inc_iff {ℓ : ℕ} (α : E → ZMod ℓ) (x : V) (i : ZMod ℓ) (f : E × ZMod ℓ) :
    (G.cover ℓ α).Inc (x, i) f ↔
      G.Inc x f.1 ∧ f.2 = if G.src f.1 = x then i else i - α f.1 := by
  obtain ⟨e, j⟩ := f
  simp only [Inc, cover, Prod.mk.injEq]
  by_cases h : G.src e = x
  · have : G.tgt e ≠ x := fun h' => G.loopless e (h.trans h'.symm)
    simp [h, this]
  · simp [h, eq_sub_iff_add_eq]

lemma cover_degree {ℓ : ℕ} [NeZero ℓ] (α : E → ZMod ℓ) (x : V) (i : ZMod ℓ) :
    (G.cover ℓ α).degree (x, i) = G.degree x := by
  unfold degree
  rw [← card_map ⟨fun e => (e, if G.src e = x then i else i - α e), fun a b h => congrArg Prod.fst h⟩]
  congr 1
  ext ⟨e, j⟩
  simp only [mem_filter, mem_univ, true_and, mem_map, cover_inc_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨e, h1, by rw [h2]; rfl⟩
  · rintro ⟨e', h1, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨h1, rfl⟩

/-- In a `k`-regular multigraph a proper `k`-edge-colouring uses every colour exactly once at
every vertex. -/
lemma colour_once {k : ℕ} (hdeg : ∀ w, G.degree w = k) {c : E → Fin k} (hc : G.IsProper c)
    (w : V) (col : Fin k) : (univ.filter fun f => c f = col ∧ G.Inc w f).card = 1 := by
  have hinj : Set.InjOn c (univ.filter (G.Inc w) : Finset E) := by
    intro f hf f' hf' h
    by_contra hne
    exact hc f f' hne w (mem_filter.1 (mem_coe.1 hf)).2 (mem_filter.1 (mem_coe.1 hf')).2 h
  have himg : (univ.filter (G.Inc w)).image c = univ :=
    eq_univ_of_card _ (by rw [card_image_of_injOn hinj]; exact (hdeg w).trans (Fintype.card_fin k).symm)
  obtain ⟨f0, hf0, hc0⟩ := mem_image.1 (himg ▸ mem_univ col)
  refine card_eq_one.2 ⟨f0, ?_⟩
  ext f
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    exact hinj (mem_coe.2 (mem_filter.2 ⟨mem_univ _, h2⟩)) (mem_coe.2 hf0) (h1.trans hc0.symm)
  · rintro rfl
    exact ⟨hc0, (mem_filter.1 hf0).2⟩

/-- Parity: then every colour leaves an odd vertex set an odd number of times. -/
lemma colour_cut_odd {k : ℕ} {c : E → Fin k}
    (hone : ∀ w col, (univ.filter fun f => c f = col ∧ G.Inc w f).card = 1) (D : Finset V)
    (hD : Odd D.card) (col : Fin k) :
    Odd (univ.filter fun f => c f = col ∧ (G.src f ∈ D ↔ G.tgt f ∉ D)).card := by
  have h := G.handshake D (fun f => c f = col)
  rw [sum_congr rfl fun w _ => hone w col, sum_const, smul_eq_mul, mul_one] at h
  obtain ⟨r, hr⟩ := hD
  exact Nat.odd_iff.2 (by omega)

end Multigraph

/-- If `|X|` equals the number of colours and every colour occurs an odd number of times on `X`,
then every colour occurs exactly once. -/
lemma colour_all_once {ι κ : Type*} [Fintype κ] [DecidableEq κ] (X : Finset ι) (c : ι → κ)
    (hX : X.card = Fintype.card κ) (hodd : ∀ col, Odd (X.filter fun f => c f = col).card)
    (col : κ) : (X.filter fun f => c f = col).card = 1 := by
  have htot : ∑ col, (X.filter fun f => c f = col).card = ∑ _col : κ, 1 := by
    rw [← card_eq_sum_card_fiberwise (fun _ _ => mem_univ _), hX]
    simp
  exact ((sum_eq_sum_iff_of_le (fun col _ => (hodd col).pos)).1 htot.symm col (mem_univ _)).symm

open Multigraph

/-! ## The Petersen graph

Vertices `a_i = i` and `b_i = 5 + i` (`i ∈ ℤ/5`). Edges: `i` is `a_i a_{i+1}`, `5 + i` is the spoke
`a_i b_i`, `10 + i` is `b_i b_{i+2}`. Edge `e` runs from `pu e` to `pw e`. The *corner* of `e` at
each end (`ku e`, `kw e`) numbers the three edges at every vertex `0, 1, 2`. -/

def pu : Fin 15 → Fin 10 := ![0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
def pw : Fin 15 → Fin 10 := ![1, 2, 3, 4, 0, 5, 6, 7, 8, 9, 7, 8, 9, 5, 6]
def ku : Fin 15 → Fin 3 := ![0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0]
def kw : Fin 15 → Fin 3 := ![1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1]

/-- The Petersen graph as a multigraph. -/
def petersen : Multigraph (Fin 10) (Fin 15) where
  src := pu
  tgt := pw
  loopless := by decide

/-- Every odd vertex set of the Petersen graph has at least `3` edges leaving it. -/
lemma petersen_odd_cut : ∀ U : Finset (Fin 10), Odd U.card →
    3 ≤ (univ.filter fun e => pu e ∈ U ↔ pw e ∉ U).card := by
  decide +kernel

/-- The finite search behind "a perfect matching of the Petersen graph has `1` or `5` spokes":
the variables are the outer edges `o_i`, spokes `s_i` and inner edges `n_i`, and each hypothesis
says one vertex is covered exactly once. -/
lemma matching_search : ∀ o0 o4 s0 : Bool, o0.toNat + o4.toNat + s0.toNat = 1 →
    ∀ o1 s1 : Bool, o1.toNat + o0.toNat + s1.toNat = 1 →
    ∀ o2 s2 : Bool, o2.toNat + o1.toNat + s2.toNat = 1 →
    ∀ o3 s3 : Bool, o3.toNat + o2.toNat + s3.toNat = 1 →
    ∀ s4 : Bool, o4.toNat + o3.toNat + s4.toNat = 1 →
    ∀ n0 n3 : Bool, s0.toNat + n0.toNat + n3.toNat = 1 →
    ∀ n1 n4 : Bool, s1.toNat + n1.toNat + n4.toNat = 1 →
    ∀ n2 : Bool, s2.toNat + n2.toNat + n0.toNat = 1 →
    s3.toNat + n3.toNat + n1.toNat = 1 → s4.toNat + n4.toNat + n2.toNat = 1 →
    (s0.toNat + s1.toNat + s2.toNat + s3.toNat + s4.toNat) % 4 = 1 := by
  decide

lemma card_triple {α : Type*} [DecidableEq α] (m : α → Bool) {a b c : α} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    (({a, b, c} : Finset α).filter fun e => m e = true).card =
      (m a).toNat + (m b).toNat + (m c).toNat := by
  rw [card_filter, sum_insert (by simp [hab, hac]), sum_insert (by simp [hbc]), sum_singleton]
  cases m a <;> cases m b <;> cases m c <;> rfl

/-- **A perfect matching of the Petersen graph has `1` or `5` spokes**, so their number is
`1 mod 4`. -/
lemma matching_spokes (m : Fin 15 → Bool)
    (h : ∀ v, (univ.filter fun e => (pu e = v ∨ pw e = v) ∧ m e = true).card = 1) :
    ((m 5).toNat + (m 6).toNat + (m 7).toNat + (m 8).toNat + (m 9).toNat) % 4 = 1 := by
  have h0 : (m 0).toNat + (m 4).toNat + (m 5).toNat = 1 := by
    rw [← h 0, ← filter_filter,
      (by decide : (univ.filter fun e : Fin 15 => pu e = 0 ∨ pw e = 0) = {0, 4, 5}),
      card_triple m (by decide) (by decide) (by decide)]
  have h1 : (m 1).toNat + (m 0).toNat + (m 6).toNat = 1 := by
    rw [← h 1, ← filter_filter,
      (by decide : (univ.filter fun e : Fin 15 => pu e = 1 ∨ pw e = 1) = {1, 0, 6}),
      card_triple m (by decide) (by decide) (by decide)]
  have h2 : (m 2).toNat + (m 1).toNat + (m 7).toNat = 1 := by
    rw [← h 2, ← filter_filter,
      (by decide : (univ.filter fun e : Fin 15 => pu e = 2 ∨ pw e = 2) = {2, 1, 7}),
      card_triple m (by decide) (by decide) (by decide)]
  have h3 : (m 3).toNat + (m 2).toNat + (m 8).toNat = 1 := by
    rw [← h 3, ← filter_filter,
      (by decide : (univ.filter fun e : Fin 15 => pu e = 3 ∨ pw e = 3) = {3, 2, 8}),
      card_triple m (by decide) (by decide) (by decide)]
  have h4 : (m 4).toNat + (m 3).toNat + (m 9).toNat = 1 := by
    rw [← h 4, ← filter_filter,
      (by decide : (univ.filter fun e : Fin 15 => pu e = 4 ∨ pw e = 4) = {4, 3, 9}),
      card_triple m (by decide) (by decide) (by decide)]
  have h5 : (m 5).toNat + (m 10).toNat + (m 13).toNat = 1 := by
    rw [← h 5, ← filter_filter,
      (by decide : (univ.filter fun e : Fin 15 => pu e = 5 ∨ pw e = 5) = {5, 10, 13}),
      card_triple m (by decide) (by decide) (by decide)]
  have h6 : (m 6).toNat + (m 11).toNat + (m 14).toNat = 1 := by
    rw [← h 6, ← filter_filter,
      (by decide : (univ.filter fun e : Fin 15 => pu e = 6 ∨ pw e = 6) = {6, 11, 14}),
      card_triple m (by decide) (by decide) (by decide)]
  have h7 : (m 7).toNat + (m 12).toNat + (m 10).toNat = 1 := by
    rw [← h 7, ← filter_filter,
      (by decide : (univ.filter fun e : Fin 15 => pu e = 7 ∨ pw e = 7) = {7, 12, 10}),
      card_triple m (by decide) (by decide) (by decide)]
  have h8 : (m 8).toNat + (m 13).toNat + (m 11).toNat = 1 := by
    rw [← h 8, ← filter_filter,
      (by decide : (univ.filter fun e : Fin 15 => pu e = 8 ∨ pw e = 8) = {8, 13, 11}),
      card_triple m (by decide) (by decide) (by decide)]
  have h9 : (m 9).toNat + (m 14).toNat + (m 12).toNat = 1 := by
    rw [← h 9, ← filter_filter,
      (by decide : (univ.filter fun e : Fin 15 => pu e = 9 ∨ pw e = 9) = {9, 14, 12}),
      card_triple m (by decide) (by decide) (by decide)]
  exact matching_search _ _ _ h0 _ _ h1 _ _ h2 _ _ h3 _ h4 _ _ h5 _ _ h6 _ h7 h8 h9

/-! ## Wang's multigraph `F_3(P)`

Each Petersen vertex `v` becomes a triangle on the corners `(v, 0), (v, 1), (v, 2)` with `p = 4`
parallel edges on each side (`inl (v, s, j)` joins corner `s` to corner `s + 1`); each Petersen
edge `e` becomes the connecting edge `inr e` between the corresponding corners. -/

abbrev FV := Fin 10 × Fin 3
abbrev FE := (Fin 10 × Fin 3 × Fin 4) ⊕ Fin 15

def F : Multigraph FV FE where
  src | .inl (v, s, _) => (v, s) | .inr e => (pu e, ku e)
  tgt | .inl (v, s, _) => (v, s + 1) | .inr e => (pw e, kw e)
  loopless := by decide +kernel

lemma F_degree : ∀ x, F.degree x = 9 := by decide +kernel

/-- Whether an edge of `F` leaves the block of `v` (exactly one end in the block). -/
def Leaves (v : Fin 10) (x : FE) : Prop := ((F.src x).1 = v ↔ (F.tgt x).1 ≠ v)

instance (v : Fin 10) : DecidablePred (Leaves v) := fun _ => inferInstanceAs (Decidable (_ ↔ _))

lemma leaves_inl : ∀ v y, ¬ Leaves v (.inl y) := by decide +kernel
lemma leaves_inr : ∀ v e, Leaves v (.inr e) ↔ (pu e = v ∨ pw e = v) := by decide +kernel
lemma card_leaves : ∀ v, (univ.filter (Leaves v)).card = 3 := by decide +kernel
lemma card_block : ∀ v, (univ.filter fun w : FV × ZMod 3 => w.1.1 = v).card = 9 := by decide +kernel

lemma sum_toNat {ι : Type*} (s : Finset ι) (p : ι → Bool) :
    ∑ i ∈ s, (p i).toNat = (s.filter fun i => p i = true).card := by
  rw [card_filter]
  refine sum_congr rfl fun i _ => ?_
  cases p i <;> rfl

/-- Each colour occurs exactly once among the `9` edges leaving the lifted block of `v`. -/
lemma leaves_once (α : FE → ZMod 3) (c : FE × ZMod 3 → Fin 9) (hc : (F.cover 3 α).IsProper c)
    (v : Fin 10) (col : Fin 9) :
    ((univ.filter fun f : FE × ZMod 3 => Leaves v f.1).filter fun f => c f = col).card = 1 := by
  have hone := (F.cover 3 α).colour_once
    (fun w => (F.cover_degree α w.1 w.2).trans (F_degree w.1)) hc
  revert col
  refine colour_all_once _ c ?_ fun col => ?_
  · have : (univ.filter fun f : FE × ZMod 3 => Leaves v f.1) =
        (univ.filter (Leaves v)) ×ˢ (univ : Finset (ZMod 3)) := by
      ext f; simp
    rw [this, card_product, card_leaves, card_univ, ZMod.card, Fintype.card_fin]
  · have h := (F.cover 3 α).colour_cut_odd hone
      (univ.filter fun w : FV × ZMod 3 => w.1.1 = v) (by rw [card_block]; decide) col
    convert h using 2
    ext f
    simp only [mem_filter, mem_univ, true_and, cover]
    exact and_comm.trans (and_congr_right fun _ => Iff.rfl)

/-- The same, as existence and uniqueness. -/
lemma leaves_exists_unique (α : FE → ZMod 3) (c : FE × ZMod 3 → Fin 9)
    (hc : (F.cover 3 α).IsProper c) (v : Fin 10) (col : Fin 9) :
    (∃ f : FE × ZMod 3, Leaves v f.1 ∧ c f = col) ∧
      ∀ f f' : FE × ZMod 3, Leaves v f.1 → c f = col → Leaves v f'.1 → c f' = col → f = f' := by
  have h := leaves_once α c hc v col
  refine ⟨?_, fun f f' h1 h2 h3 h4 => card_le_one.1 h.le f ?_ f' ?_⟩
  · rw [card_eq_one] at h
    obtain ⟨f0, hf0⟩ := h
    have := congrArg (f0 ∈ ·) hf0
    simp only [mem_filter, mem_univ, true_and, mem_singleton, eq_iff_iff, iff_true] at this
    exact ⟨f0, this⟩
  · simp only [mem_filter, mem_univ, true_and]; exact ⟨h1, h2⟩
  · simp only [mem_filter, mem_univ, true_and]; exact ⟨h3, h4⟩

/-- The colour class of `col` on connecting edges is a perfect matching of the Petersen graph. -/
lemma class_matching (c : FE × ZMod 3 → Fin 9)
    (hX : ∀ v col, (∃ f : FE × ZMod 3, Leaves v f.1 ∧ c f = col) ∧
      ∀ f f' : FE × ZMod 3, Leaves v f.1 → c f = col → Leaves v f'.1 → c f' = col → f = f')
    (m : Fin 9 → Fin 15 → Bool) (hm : ∀ col e, m col e = true ↔ ∃ j, c (.inr e, j) = col) :
    ∀ col v, (univ.filter fun e => (pu e = v ∨ pw e = v) ∧ m col e = true).card = 1 := by
  intro col v
  obtain ⟨⟨⟨x | e0, j0⟩, hl, hc0⟩, huniq⟩ := hX v col
  · exact absurd hl (leaves_inl v x)
  refine card_eq_one.2 ⟨e0, ?_⟩
  ext e
  simp only [mem_filter, mem_univ, true_and, mem_singleton, hm]
  constructor
  · rintro ⟨hv, j, hj⟩
    have := huniq (.inr e, j) (.inr e0, j0) ((leaves_inr v e).2 hv) hj hl hc0
    simpa using congrArg Prod.fst this
  · rintro rfl
    exact ⟨(leaves_inr v e).1 hl, j0, hc0⟩

/-- Every Petersen edge lies in exactly `3` colour classes. -/
lemma class_three (c : FE × ZMod 3 → Fin 9)
    (hX : ∀ v col, (∃ f : FE × ZMod 3, Leaves v f.1 ∧ c f = col) ∧
      ∀ f f' : FE × ZMod 3, Leaves v f.1 → c f = col → Leaves v f'.1 → c f' = col → f = f')
    (m : Fin 9 → Fin 15 → Bool) (hm : ∀ col e, m col e = true ↔ ∃ j, c (.inr e, j) = col) :
    ∀ e, (univ.filter fun col => m col e = true).card = 3 := by
  intro e
  have : (univ.filter fun col => m col e = true) = univ.image fun j => c (.inr e, j) := by
    ext col; simp only [mem_filter, mem_univ, true_and, mem_image, hm]
  rw [this, card_image_of_injective _ ?_, card_univ, ZMod.card]
  intro j j' h
  have hl : Leaves (pu e) (.inr e : FE) := (leaves_inr _ e).2 (Or.inl rfl)
  have := (hX (pu e) (c (.inr e, j))).2 (.inr e, j) (.inr e, j') hl rfl hl h.symm
  simpa using congrArg Prod.snd this

/-- **No cyclic `3`-fold cover of `F` has a proper `9`-edge-colouring** (Wang, Lemma 3.1 and
Corollary 1.4 for `ℓ = 3`). -/
theorem no_nine_colouring (α : FE → ZMod 3) (c : FE × ZMod 3 → Fin 9)
    (hc : (F.cover 3 α).IsProper c) : False := by
  have hX := leaves_exists_unique α c hc
  -- The colour classes give `9` perfect matchings of the Petersen graph covering each edge `3` times.
  obtain ⟨m, hm⟩ : ∃ m : Fin 9 → Fin 15 → Bool, ∀ col e, m col e = true ↔ ∃ j, c (.inr e, j) = col :=
    ⟨fun col e => decide (∃ j, c (.inr e, j) = col), fun _ _ => decide_eq_true_iff⟩
  have hpm := class_matching c hX m hm
  have hthree := class_three c hX m hm
  -- Count spokes: each matching has `1` or `5`, the total is `5 · 3 = 15`; impossible mod `4`.
  have htot : ∑ col, ((m col 5).toNat + (m col 6).toNat + (m col 7).toNat + (m col 8).toNat +
      (m col 9).toNat) = 15 := by
    simp only [sum_add_distrib, sum_toNat, hthree]
  have h4 := Finset.sum_nat_mod univ 4 fun col => (m col 5).toNat + (m col 6).toNat +
    (m col 7).toNat + (m col 8).toNat + (m col 9).toNat
  rw [htot, sum_congr rfl fun col _ => matching_spokes (m col) (hpm col)] at h4
  simp at h4

/-- Every odd vertex set of `F` has at least `3` edges leaving it. -/
lemma F_cut (S : Finset FV) (hS : Odd S.card) :
    3 ≤ (univ.filter fun x => F.src x ∈ S ↔ F.tgt x ∉ S).card := by
  by_cases hsplit : ∃ v s, ((v, s) ∈ S ↔ (v, s + 1) ∉ S)
  · obtain ⟨v, s, hvs⟩ := hsplit
    calc 3 ≤ (univ.map ⟨fun j : Fin 4 => (Sum.inl (v, s, j) : FE),
          fun a b h => by simpa using h⟩).card := by simp
      _ ≤ _ := card_le_card fun x hx => by
          obtain ⟨j, -, rfl⟩ := mem_map.1 hx
          simp only [mem_filter, mem_univ, true_and]
          exact hvs
  · have hb : ∀ v s, ((v, s) ∈ S ↔ (v, s + 1) ∈ S) := fun v s => by
      by_contra h
      exact hsplit ⟨v, s, by tauto⟩
    have hall : ∀ v k, (v, k) ∈ S ↔ (v, 0) ∈ S := by
      intro v k
      have h0 := hb v 0
      have h1 := hb v 1
      fin_cases k
      · rfl
      · exact h0.symm
      · exact h1.symm.trans h0.symm
    set U := univ.filter fun v : Fin 10 => (v, 0) ∈ S
    have hSU : S = U ×ˢ univ := by
      ext ⟨v, k⟩
      simp [U, hall v k]
    have hU : Odd U.card := by
      rw [hSU, card_product, card_univ, Fintype.card_fin] at hS
      exact (Nat.odd_mul.1 hS).1
    calc 3 ≤ _ := petersen_odd_cut U hU
      _ = ((univ.filter fun e => pu e ∈ U ↔ pw e ∉ U).map ⟨Sum.inr, Sum.inr_injective⟩).card :=
          (card_map _).symm
      _ ≤ _ := card_le_card fun x hx => by
          obtain ⟨e, he, rfl⟩ := mem_map.1 hx
          simp only [mem_filter, mem_univ, true_and] at he ⊢
          rw [hSU]
          simpa [F] using he

/-- `L_3(F) = 9`. -/
lemma F_L : F.L 3 = 9 := by
  apply le_antisymm
  · apply max_le
    · exact Finset.sup_le fun x _ => (F_degree x).le
    · refine Finset.sup_le fun S hS => ?_
      obtain ⟨hodd, h3⟩ := (mem_filter.1 hS).2
      have hcut := F_cut S hodd
      have h := F.handshake S (fun _ => True)
      have hd : ∀ v, (univ.filter fun e => True ∧ F.Inc v e).card = 9 := fun v => by
        simpa [degree] using F_degree v
      rw [sum_congr rfl fun v _ => hd v, sum_const, smul_eq_mul] at h
      simp only [true_and] at h
      have hnat : 2 * 3 * F.edgesIn S + 9 ≤ 9 * (3 * S.card) := by
        unfold edgesIn
        omega
      have h3' : (3 : ℚ) ≤ S.card := by exact_mod_cast h3
      rw [Nat.ceil_le, div_le_iff₀ (by push_cast; linarith)]
      have : ((2 * 3 * F.edgesIn S + 9 : ℕ) : ℚ) ≤ ((9 * (3 * S.card) : ℕ) : ℚ) := by
        exact_mod_cast hnat
      push_cast at this ⊢
      linarith
  · have := Finset.le_sup (f := F.degree) (mem_univ ((0 : Fin 10), (0 : Fin 3)))
    rw [F_degree] at this
    exact le_max_of_le_left this

lemma chromaticIndex_ge (α : FE → ZMod 3) : 10 ≤ (F.cover 3 α).chromaticIndex := by
  apply le_csInf
  · exact ⟨_, fun f => Fintype.equivFin _ f,
      fun e e' hne _ _ _ h => hne ((Fintype.equivFin _).injective h)⟩
  · rintro k ⟨c, hc⟩
    by_contra hk
    exact no_nine_colouring α (fun f => Fin.castLE (by omega) (c f))
      (fun e e' hne v h1 h2 h => hc e e' hne v h1 h2 (Fin.castLE_injective _ h))

/-- `s_3(F) ≥ 10`: every cyclic `3`-fold cover of `F` needs at least `10` colours. -/
lemma F_sCyc : 10 ≤ F.sCyc 3 :=
  le_csInf ⟨_, 0, rfl⟩ (by rintro k ⟨α, rfl⟩; exact chromaticIndex_ge α)

/-- **Conjecture (Chen, van der Holst, Luo, Ma)**: for every loopless multigraph `G` and odd
`ℓ ≥ 3`, `s_ℓ(G) = L_ℓ(G)`. -/
def Conjecture : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] (G : Multigraph V E) (ℓ : ℕ),
    Odd ℓ → 3 ≤ ℓ → G.sCyc ℓ = G.L ℓ

/-- **The conjecture is false** (Wang, arXiv:2611.13394): `F_3(P)` has `L_3 = 9` but
`s_3 ≥ 10`. -/
theorem not_conjecture : ¬ Conjecture := fun h => by
  have h1 := h FV FE F 3 ⟨1, rfl⟩ le_rfl
  have h2 := F_sCyc
  have h3 := F_L
  omega

end OpenProblemsLab.OddFoldCovers
