import Mathlib

/-!
# The Bougard–Joret conjecture on sparse `k`-connected graphs is false

Let `f(n, α, k)` be the least number of edges of a `k`-connected graph on `n` vertices with
independence number `α`. Bougard and Joret (*Turán's theorem and k-connected graphs*, J. Graph Theory
58 (2008), Conjecture 1 in Section 6) conjectured that, for `n ≥ 2α`, `n ≥ α + k`, `α ≥ 2`, `k ≥ 3`:

* `f(n, α, k) = ⌈nk/2⌉` if `n ≤ kα` (first regime),
* `f(n, α, k) = t(n, α) + ⌈kα/2⌉` if `n > kα`.

Das and Gupta (arXiv:2608.18828) showed that the first regime fails, the smallest case being
`(n, α, k) = (7, 3, 4)`, where `f = 15 > 14 = ⌈7·4/2⌉`. Their argument:

* a `4`-connected graph on `7` vertices has minimum degree `≥ 4`, so `14` edges force it to be
  `4`-regular;
* the three vertices of an independent triple `T` are then joined to all four other vertices, so
  each of those four has exactly one neighbour outside `T`;
* deleting `T` leaves a perfect matching on four vertices, which is disconnected.

We formalize this lower bound (`fifteen_le_card_edges`) and the failure of the first regime
(`not_bougardJoretFirstRegime`). We do not formalize the matching upper bound `f(7,3,4) ≤ 15`
(attained by the join of three isolated vertices with a path on four vertices).
-/

namespace OpenProblemsLab.BougardJoret

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `G` is `k`-connected: it has more than `k` vertices and stays connected after deleting any
fewer than `k` vertices. -/
def KConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Connected

/-- **First regime of the Bougard–Joret conjecture**: for admissible `n, α, k` with `n ≤ kα`, the
least number of edges of a `k`-connected graph on `n` vertices with independence number `α` is
`⌈nk/2⌉`. That is, such a graph with `⌈nk/2⌉` edges exists, and every such graph has at least that
many edges. -/
def BougardJoretFirstRegime : Prop :=
  ∀ n α k : ℕ, 2 * α ≤ n → α + k ≤ n → 2 ≤ α → 3 ≤ k → n ≤ k * α →
    (∃ G : SimpleGraph (Fin n), KConnected G k ∧ G.indepNum = α ∧
        G.edgeSet.ncard = (n * k + 1) / 2) ∧
    ∀ G : SimpleGraph (Fin n), KConnected G k → G.indepNum = α →
      (n * k + 1) / 2 ≤ G.edgeSet.ncard

/-- In a `k`-connected graph every vertex has degree at least `k`. -/
theorem le_degree {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} (hk : KConnected G k) (v : V) :
    k ≤ G.degree v := by
  by_contra hlt
  push Not at hlt
  set S := G.neighborFinset v
  have hconn := hk.2 S (by rw [card_neighborFinset_eq_degree]; exact hlt)
  have hv : v ∈ ((S : Set V)ᶜ) := by simp [S]
  have hcard : 1 < (univ \ S).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_neighborFinset_eq_degree]
    have := hk.1
    omega
  obtain ⟨w, hw, hwv⟩ := exists_mem_ne hcard v
  have hw' : w ∈ ((S : Set V)ᶜ) := by simpa using hw
  obtain ⟨p⟩ := hconn.preconnected ⟨v, hv⟩ ⟨w, hw'⟩
  cases p with
  | nil => exact hwv rfl
  | @cons _ u _ h _ =>
    have hu := u.2
    have : u.1 ∈ S := by
      rw [mem_neighborFinset]; exact h
    exact hu this

/-- **Lower bound `f(7, 3, 4) ≥ 15`.** A `4`-connected graph on `7` vertices with an independent set
of size `3` has at least `15` edges. -/
theorem fifteen_le_card_edges (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = 7)
    (hk : KConnected G 4) (T : Finset V) (hT : G.IsNIndepSet 3 T) : 15 ≤ G.edgeFinset.card := by
  by_contra hlt
  push Not at hlt
  have hmin := le_degree hk
  -- 4-regular
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v, G.degree v = 4 := by
    intro v
    refine le_antisymm ?_ (hmin v)
    by_contra h5
    push Not at h5
    have h1 : ∑ u ∈ univ.erase v, 4 ≤ ∑ u ∈ univ.erase v, G.degree u :=
      sum_le_sum fun u _ => hmin u
    have h2 := add_sum_erase univ (fun u => G.degree u) (mem_univ v)
    rw [sum_const, card_erase_of_mem (mem_univ v), card_univ, hV, smul_eq_mul] at h1
    omega
  -- vertices of `T` are adjacent to everything outside `T`
  have hTc : (univ \ T).card = 4 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hV, hT.card_eq]
  have hindep : ∀ a ∈ T, ∀ b ∈ T, ¬ G.Adj a b := by
    intro a ha b hb hab
    exact hT.isIndepSet (mem_coe.mpr ha) (mem_coe.mpr hb) hab.ne hab
  have hTadj : ∀ a ∈ T, ∀ r ∉ T, G.Adj a r := by
    intro a ha r hr
    have hsub : G.neighborFinset a ⊆ univ \ T := by
      intro b hb
      rw [mem_neighborFinset] at hb
      simp only [mem_sdiff, mem_univ, true_and]
      exact fun hbT => hindep a ha b hbT hb
    have heq : G.neighborFinset a = univ \ T :=
      eq_of_subset_of_card_le hsub (by rw [hTc, card_neighborFinset_eq_degree, hdeg])
    have : r ∈ G.neighborFinset a := by rw [heq]; simpa using hr
    rwa [mem_neighborFinset] at this
  -- every vertex outside `T` has exactly one neighbour outside `T`
  have huniq : ∀ r ∉ T, ∀ x y, x ∉ T → y ∉ T → G.Adj r x → G.Adj r y → x = y := by
    intro r hr x y hx hy hrx hry
    have hsub : T ⊆ G.neighborFinset r := fun a ha => by
      rw [mem_neighborFinset]; exact (hTadj a ha r hr).symm
    have hc : (G.neighborFinset r \ T).card = 1 := by
      rw [card_sdiff_of_subset hsub, card_neighborFinset_eq_degree, hdeg, hT.card_eq]
    exact card_le_one.mp hc.le x (by simp [hx, hrx]) y (by simp [hy, hry])
  have hex : ∀ r ∉ T, ∃ x, x ∉ T ∧ G.Adj r x := by
    intro r hr
    have hsub : T ⊆ G.neighborFinset r := fun a ha => by
      rw [mem_neighborFinset]; exact (hTadj a ha r hr).symm
    have hc : (G.neighborFinset r \ T).card = 1 := by
      rw [card_sdiff_of_subset hsub, card_neighborFinset_eq_degree, hdeg, hT.card_eq]
    obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < (G.neighborFinset r \ T).card)
    simp only [mem_sdiff, mem_neighborFinset] at hx
    exact ⟨x, hx.2, hx.1⟩
  -- deleting `T` disconnects the graph
  have hconn := hk.2 T (by rw [hT.card_eq]; norm_num)
  obtain ⟨r, hr⟩ := card_pos.mp (by omega : 0 < (univ \ T).card)
  have hrT : r ∉ T := by simpa using hr
  obtain ⟨r', hr'T, hrr'⟩ := hex r hrT
  have hcard2 : 0 < ((univ \ T) \ {r, r'}).card := by
    have := card_le_card_sdiff_add_card (s := univ \ T) (t := {r, r'})
    have h2 : ({r, r'} : Finset V).card ≤ 2 := card_le_two
    omega
  obtain ⟨s, hs⟩ := card_pos.mp hcard2
  simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton, not_or] at hs
  obtain ⟨hsT, hsr, hsr'⟩ := hs
  have hmemr : r ∈ ((T : Set V)ᶜ) := by simpa using hrT
  have hmems : s ∈ ((T : Set V)ᶜ) := by simpa using hsT
  obtain ⟨p⟩ := hconn.preconnected ⟨r, hmemr⟩ ⟨s, hmems⟩
  -- every vertex reachable from `r` avoiding `T` is `r` or `r'`
  have key : ∀ x y : ↥((T : Set V)ᶜ), (G.induce ((T : Set V)ᶜ)).Walk x y →
      (x.1 = r ∨ x.1 = r') → (y.1 = r ∨ y.1 = r') := by
    intro x y q
    induction q with
    | nil => exact id
    | @cons a b c h q ih =>
      intro ha
      apply ih
      have hadj : G.Adj a.1 b.1 := h
      have hbT : b.1 ∉ T := by
        have := b.2; rwa [Set.mem_compl_iff, Finset.mem_coe] at this
      rcases ha with ha | ha
      · right
        rw [ha] at hadj
        exact huniq r hrT b.1 r' hbT hr'T hadj hrr'
      · left
        rw [ha] at hadj
        exact huniq r' hr'T b.1 r hbT hrT hadj hrr'.symm
  rcases key _ _ p (Or.inl rfl) with h | h
  · exact hsr h
  · exact hsr' h

/-- **The first regime of the Bougard–Joret conjecture is false**, at `(n, α, k) = (7, 3, 4)`:
no `4`-connected graph on `7` vertices with independence number `3` has `14` edges. -/
theorem not_bougardJoretFirstRegime : ¬ BougardJoretFirstRegime := by
  intro h
  obtain ⟨⟨G, hk, hα, hE⟩, -⟩ := h 7 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  classical
  obtain ⟨T, hT⟩ := G.exists_isNIndepSet_indepNum
  rw [hα] at hT
  have h15 := fifteen_le_card_edges G (Fintype.card_fin 7) hk T hT
  rw [← coe_edgeFinset, Set.ncard_coe_finset] at hE
  norm_num at hE
  omega

end OpenProblemsLab.BougardJoret
