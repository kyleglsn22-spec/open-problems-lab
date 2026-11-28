import Mathlib

/-!
# Unstable graphs: the first version of Mizzi's cycle conjecture is false

The canonical double cover `CDC(G) = G × K₂` has vertex set `V × Bool`, with `(u, a) ~ (v, b)` when
`a ≠ b` and `u ~ v`. Every automorphism `φ` of `G` gives automorphisms `(v, a) ↦ (φ v, a)` and
`(v, a) ↦ (φ v, !a)` of `CDC(G)`, forming `Aut(G) × ℤ₂`. A graph is **unstable** if `CDC(G)` has any
other automorphism. Two kinds of graph are unstable for trivial reasons: bipartite graphs and graphs
with two vertices of equal neighbourhood (not vertex-determining).

R. Mizzi (arXiv:2603.27559, versions 1 and 2, abstract and Section 7, working with connected graphs and
excluding the trivial cases) conjectured that every unstable graph contains cycles `C_k` and `C_{2k}`
for some odd `k`. Versions 3 and 4 of that paper restrict the conjecture to *asymmetric* unstable
graphs. The graph below has an automorphism group of order 2, so it does **not** refute the current
version, and Mizzi's version 4 acknowledges it as a counterexample to the earlier statement. We
formalize the version 1/2 statement as `MizziConjectureV1`.

P. R. Srivastava (arXiv:2608.15281) gave a 10-vertex counterexample. Its vertices are `1, …, 10`,
and here `0, …, 9`. Its 11 edges are `12, 1 10, 24, 34, 36, 45, 57, 5 10, 6 10, 79, 8 10`.
The pair `α = (1 6)`, `β = (2 3)` satisfies `β(N(v)) = N(α(v))`, so
`(v, false) ↦ (α v, false)`, `(v, true) ↦ (β v, true)` is an automorphism of the double cover that
does not come from `Aut(G) × ℤ₂`. The only cycles have lengths 5, 5 and 6.

"Contains" is read in the weakest sense: as a (not necessarily induced) subgraph, that is, a cycle
walk of that length. Our counterexample has no such pair, so it refutes every stronger reading too.

Main result: `not_mizziConjectureV1`. (Mizzi's version 4 also gives a smaller, 7-vertex
counterexample to the version 1/2 statement; we do not formalize it.)
-/

namespace OpenProblemsLab.Unstable

open SimpleGraph

/-- The canonical double cover `G × K₂`. -/
def cdc {V : Type} (G : SimpleGraph V) : SimpleGraph (V × Bool) where
  Adj x y := x.2 ≠ y.2 ∧ G.Adj x.1 y.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- `G` is unstable: the double cover has an automorphism not of the form
`(v, a) ↦ (φ v, a xor c)` with `φ` an automorphism of `G`. -/
def IsUnstable {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ σ : cdc G ≃g cdc G, ¬ ∃ (φ : G ≃g G) (c : Bool), ∀ x, σ x = (φ x.1, xor x.2 c)

/-- `G` is vertex-determining: distinct vertices have distinct neighbourhoods. -/
def IsVertexDetermining {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v, G.neighborSet u = G.neighborSet v → u = v

/-- `G` contains a cycle of length `n` (as a subgraph). -/
def HasCycleOfLength {V : Type} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n

/-- **Mizzi's conjecture, as stated in versions 1–2 of arXiv:2603.27559** (for unstable graphs): every connected, non-bipartite, vertex-determining,
unstable finite graph contains cycles `C_k` and `C_{2k}` for some odd `k`. -/
def MizziConjectureV1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → ¬ G.Colorable 2 →
    IsVertexDetermining G → IsUnstable G →
    ∃ k, Odd k ∧ HasCycleOfLength G k ∧ HasCycleOfLength G (2 * k)

/-! ## Srivastava's graph -/

/-- The edges (paper labels minus one). -/
def edgeList : List (Fin 10 × Fin 10) :=
  [(0, 1), (0, 9), (1, 3), (2, 3), (2, 5), (3, 4), (4, 6), (4, 9), (5, 9), (6, 8), (7, 9)]

/-- Adjacency as a Boolean test. -/
def adjB (a b : Fin 10) : Bool := (a, b) ∈ edgeList || (b, a) ∈ edgeList

/-- The 10-vertex graph. -/
def G : SimpleGraph (Fin 10) where
  Adj a b := adjB a b = true
  symm := ⟨fun a b h => by simpa [adjB, Bool.or_comm] using h⟩
  loopless := ⟨fun a h => by revert a h; decide⟩

instance : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable (adjB a b = true))

theorem G_connected : G.Connected := by
  have h : ∀ v : Fin 10, G.Reachable 0 v := by
    have e : ∀ a b : Fin 10, adjB a b = true → G.Adj a b := fun _ _ h => h
    have r1 : G.Reachable 0 1 := (e 0 1 (by decide)).reachable
    have r9 : G.Reachable 0 9 := (e 0 9 (by decide)).reachable
    have r3 : G.Reachable 0 3 := r1.trans (e 1 3 (by decide)).reachable
    have r2 : G.Reachable 0 2 := r3.trans (e 3 2 (by decide)).reachable
    have r5 : G.Reachable 0 5 := r2.trans (e 2 5 (by decide)).reachable
    have r4 : G.Reachable 0 4 := r3.trans (e 3 4 (by decide)).reachable
    have r6 : G.Reachable 0 6 := r4.trans (e 4 6 (by decide)).reachable
    have r8 : G.Reachable 0 8 := r6.trans (e 6 8 (by decide)).reachable
    have r7 : G.Reachable 0 7 := r9.trans (e 9 7 (by decide)).reachable
    intro v
    fin_cases v
    exacts [Reachable.refl _, r1, r2, r3, r4, r5, r6, r7, r8, r9]
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

/-- The 5-cycle `1 2 4 5 10` (paper labels) rules out a 2-colouring. -/
theorem G_not_bipartite : ¬ G.Colorable 2 := by
  rintro ⟨C⟩
  have h01 := C.valid (show G.Adj 0 1 by decide)
  have h13 := C.valid (show G.Adj 1 3 by decide)
  have h34 := C.valid (show G.Adj 3 4 by decide)
  have h49 := C.valid (show G.Adj 4 9 by decide)
  have h90 := C.valid (show G.Adj 9 0 by decide)
  revert h01 h13 h34 h49 h90
  generalize C 0 = a, C 1 = b, C 3 = c, C 4 = d, C 9 = e
  intro h01 h13 h34 h49 h90
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> simp_all

theorem G_vertexDetermining : IsVertexDetermining G := by
  have key : ∀ u v : Fin 10, G.neighborFinset u = G.neighborFinset v → u = v := by decide
  intro u v h
  apply key
  ext w; simp only [mem_neighborFinset]; exact Set.ext_iff.mp h w

/-- `α = (1 6)` in paper labels. -/
def α : Equiv.Perm (Fin 10) := Equiv.swap 0 5
/-- `β = (2 3)` in paper labels. -/
def β : Equiv.Perm (Fin 10) := Equiv.swap 1 2

/-- The two-fold automorphism acting as `α` on one side and `β` on the other. -/
def σperm : Equiv.Perm (Fin 10 × Bool) where
  toFun x := (if x.2 then β x.1 else α x.1, x.2)
  invFun x := (if x.2 then β x.1 else α x.1, x.2)
  left_inv x := by rcases x with ⟨v, _ | _⟩ <;> simp [α, β]
  right_inv x := by rcases x with ⟨v, _ | _⟩ <;> simp [α, β]

theorem σ_adj : ∀ x y : Fin 10 × Bool, (cdc G).Adj (σperm x) (σperm y) ↔ (cdc G).Adj x y := by
  simp only [cdc, σperm, Equiv.coe_fn_mk, G]
  decide

/-- The unexpected automorphism of the double cover. -/
def σ : cdc G ≃g cdc G := ⟨σperm, σ_adj _ _⟩

theorem G_unstable : IsUnstable G := by
  refine ⟨σ, ?_⟩
  rintro ⟨φ, c, h⟩
  cases c
  · have h0 := h (0, false)
    have h1 := h (0, true)
    have e0 : α 0 = φ 0 := by simpa [σ, σperm] using congrArg Prod.fst h0
    have e1 : β 0 = φ 0 := by simpa [σ, σperm] using congrArg Prod.fst h1
    have : α 0 = β 0 := e0.trans e1.symm
    revert this; decide
  · have h0 := h (0, false)
    simp [σ, σperm] at h0

/-! ## Cycles -/

theorem cycle_length_le {v : Fin 10} {p : G.Walk v v} (hp : p.IsCycle) : p.length ≤ 10 := by
  have h := hp.isPath_tail.length_lt
  have e := Walk.length_tail_add_one hp.not_nil
  simp only [Fintype.card_fin] at h
  omega

theorem triangle_free : ∀ a b c : Fin 10, G.Adj a b → G.Adj b c → G.Adj c a → False := by
  decide

theorem no_triangle {v : Fin 10} {p : G.Walk v v} (hp : p.IsCycle) : p.length ≠ 3 := by
  intro hl
  match p, hp, hl with
  | .cons h1 (.cons h2 (.cons h3 .nil)), _, _ => exact triangle_free _ _ _ h1 h2 h3

/-- A cycle of length 10 would pass through the leaf `8` (paper label), impossible. -/
theorem no_ten {v : Fin 10} {p : G.Walk v v} (hp : p.IsCycle) : p.length ≠ 10 := by
  intro hl
  have hnd := hp.nodup_dropLast_support
  have hlen : p.support.dropLast.length = 10 := by
    rw [List.length_dropLast, Walk.length_support, hl]
  have hall : p.support.dropLast.toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup hnd, hlen]; rfl)
  have h7 : (7 : Fin 10) ∈ p.support := by
    have : (7 : Fin 10) ∈ p.support.dropLast.toFinset := hall ▸ Finset.mem_univ _
    exact List.dropLast_subset _ (List.mem_toFinset.mp this)
  have h2 := hp.ncard_neighborSet_toSubgraph_eq_two h7
  have hsub : p.toSubgraph.neighborSet 7 ⊆ ({9} : Set (Fin 10)) := by
    have key : ∀ w : Fin 10, G.Adj 7 w → w = 9 := by decide
    intro w hw
    exact key w (p.toSubgraph.adj_sub hw)
  have := Set.ncard_le_ncard hsub (Set.finite_singleton 9)
  rw [h2, Set.ncard_singleton] at this
  omega

theorem not_cycle_pair : ¬ ∃ k, Odd k ∧ HasCycleOfLength G k ∧ HasCycleOfLength G (2 * k) := by
  rintro ⟨k, hk, ⟨v, p, hp, hl⟩, ⟨w, q, hq, hl2⟩⟩
  have h3 := hp.three_le_length
  have hq10 := cycle_length_le hq
  obtain ⟨j, rfl⟩ := hk
  have : j = 1 ∨ j = 2 := by omega
  rcases this with rfl | rfl
  · exact no_triangle hp hl
  · exact no_ten hq hl2

/-- **Mizzi's conjecture (versions 1–2) is false**: Srivastava's 10-vertex graph is connected, non-bipartite,
vertex-determining and unstable, but has no cycles `C_k`, `C_{2k}` with `k` odd. -/
theorem not_mizziConjectureV1 : ¬ MizziConjectureV1 := fun h =>
  not_cycle_pair (h (Fin 10) G G_connected G_not_bipartite G_vertexDetermining G_unstable)

end OpenProblemsLab.Unstable
