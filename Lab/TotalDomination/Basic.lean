import Lab.AlbertsonBerman.Drawing

/-!
# Goddard–Henning Conjecture 32 is false (claim GHT-1)

A set `A` of vertices is a **total dominating set** if every vertex has a neighbour in `A`.
Goddard and Henning (2018, Conjecture 32) conjectured that every planar triangulation on at least
four vertices has a proper 4-colouring with colour classes `C₁, C₂, C₃, C₄` such that `C₁ ∪ C₂` and
`C₃ ∪ C₄` are total dominating sets. Equivalently, the vertex set splits into two total dominating
sets that both induce bipartite subgraphs.

H. Kwon, B. Park and Y. Sano (arXiv:2611.00572, Theorem 1.2) disproved this with a 36-vertex
triangulation `B`, glued from three copies of a 14-vertex triangulation `G₁₄`.

Formal statement (`GoddardHenningConjecture`): planar triangulations are the graphs on `n ≥ 4`
vertices with a straight-line planar drawing (`AlbertsonBerman.StraightLinePlanar`, by Fáry's
theorem the same as planar) and `3n - 6` edges (the maximal planar graphs).

Files:
* `Basic`: definitions, the graph `B`, and the reduction from the partition to a "partner
  colouring" (Proposition 2.3 (a) ⇒ (b) of the paper);
* `Lemma`: Lemma 3.1 of the paper on `G₁₄`, checked by the kernel;
* `NoPartner`: `B` has no partner colouring (the paper's gluing argument);
* `DrawData`, `Good0`–`Good5`, `Drawing`: a straight-line planar drawing of `B`;
* `Main`: `not_goddardHenningConjecture`.
-/

namespace OpenProblemsLab.TotalDomination

open SimpleGraph

/-! ## Statement -/

/-- `A` is a total dominating set of `H`: every vertex has a neighbour in `A`. -/
def IsTotalDominating {V : Type*} (H : SimpleGraph V) (A : Set V) : Prop :=
  ∀ v, ∃ u ∈ A, H.Adj v u

/-- **Goddard–Henning Conjecture 32** (2018), in its equivalent partition form: every planar
triangulation on `n ≥ 4` vertices (a graph with a straight-line planar drawing and `3n - 6` edges)
has a vertex partition into two total dominating sets that both induce bipartite subgraphs. -/
def GoddardHenningConjecture : Prop :=
  ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], 4 ≤ n →
    AlbertsonBerman.StraightLinePlanar H → H.edgeFinset.card = 3 * n - 6 →
    ∃ A : Set (Fin n), IsTotalDominating H A ∧ IsTotalDominating H Aᶜ ∧
      (H.induce A).Colorable 2 ∧ (H.induce Aᶜ).Colorable 2

/-! ## Partner colourings -/

/-- The partner of a colour: colours `0, 1` are partners, and so are `2, 3`. -/
def partner : Fin 4 → Fin 4 := ![1, 0, 3, 2]

/-- Colour `b` of side `s`. -/
def col (s : Bool) (b : Fin 2) : Fin 4 := if s then (if b = 0 then 0 else 1) else (if b = 0 then 2 else 3)

lemma col_ne_side : ∀ (s t : Bool) (b b' : Fin 2), s ≠ t → col s b ≠ col t b' := by decide
lemma col_ne : ∀ (s : Bool) (b b' : Fin 2), b ≠ b' → col s b ≠ col s b' := by decide
lemma col_partner : ∀ (s : Bool) (b b' : Fin 2), b ≠ b' → col s b' = partner (col s b) := by decide

/-- Proposition 2.3 (a) ⇒ (b): a partition into two total dominating sets inducing bipartite graphs
gives a proper 4-colouring in which every vertex has a neighbour of its partner colour. -/
theorem partnerColoring_of_partition {n : ℕ} (H : SimpleGraph (Fin n)) (A : Set (Fin n))
    (h1 : IsTotalDominating H A) (h2 : IsTotalDominating H Aᶜ) (c1 : (H.induce A).Colorable 2)
    (c2 : (H.induce Aᶜ).Colorable 2) :
    ∃ c : Fin n → Fin 4, (∀ u v, H.Adj u v → c u ≠ c v) ∧
      ∀ v, ∃ u, H.Adj v u ∧ c u = partner (c v) := by
  classical
  obtain ⟨C1⟩ := c1
  obtain ⟨C2⟩ := c2
  let c : Fin n → Fin 4 := fun v =>
    if h : v ∈ A then col true (C1 ⟨v, h⟩) else col false (C2 ⟨v, h⟩)
  refine ⟨c, ?_, ?_⟩
  · intro u v huv
    by_cases hu : u ∈ A <;> by_cases hv : v ∈ A
    · simp only [c, dif_pos hu, dif_pos hv]
      exact col_ne _ _ _ (C1.valid (show (H.induce A).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv))
    · simp only [c, dif_pos hu, dif_neg hv]; exact col_ne_side _ _ _ _ (by decide)
    · simp only [c, dif_neg hu, dif_pos hv]; exact col_ne_side _ _ _ _ (by decide)
    · simp only [c, dif_neg hu, dif_neg hv]
      exact col_ne _ _ _ (C2.valid (show (H.induce Aᶜ).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv))
  · intro v
    by_cases hv : v ∈ A
    · obtain ⟨u, hu, huv⟩ := h1 v
      refine ⟨u, huv, ?_⟩
      simp only [c, dif_pos hu, dif_pos hv]
      exact col_partner _ _ _ (C1.valid (show (H.induce A).Adj ⟨v, hv⟩ ⟨u, hu⟩ from huv))
    · obtain ⟨u, hu, huv⟩ := h2 v
      refine ⟨u, huv, ?_⟩
      simp only [c, dif_neg (show u ∉ A from hu), dif_neg hv]
      exact col_partner _ _ _ (C2.valid (show (H.induce Aᶜ).Adj ⟨v, hv⟩ ⟨u, hu⟩ from huv))

/-- Three distinct colours always contain a partner pair. -/
lemma triangle : ∀ p q r : Fin 4, p ≠ q → p ≠ r → q ≠ r → r ≠ partner p → r ≠ partner q →
    q ≠ partner p → False := by decide

/-! ## The graph `B` -/

/-- The 102 edges of the 36-vertex triangulation `B` (Kwon–Park–Sano, Section 3). Vertex `0` is
`a`, `1` is `b`, `2` is `z₂`, `7` is `z₁`; the full labelling is produced by
`explorer/total-domination/build.py` from the paper's edge list of `G₁₄`. -/
def edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 18), (0, 19), (0, 20), (0, 25), (0, 26), (0, 27), (0, 28), (0, 29), (1, 2), (1, 7), (1, 8), (1, 9), (1, 14), (1, 15), (1, 16), (1, 17), (1, 18), (1, 25), (1, 30), (1, 32), (1, 33), (2, 3), (2, 8), (2, 10), (2, 11), (2, 14), (2, 19), (2, 21), (2, 22), (3, 4), (3, 11), (4, 5), (4, 11), (4, 12), (5, 6), (5, 12), (6, 7), (6, 10), (6, 12), (6, 13), (7, 9), (7, 13), (8, 9), (8, 10), (8, 13), (9, 13), (10, 11), (10, 12), (10, 13), (11, 12), (14, 15), (14, 22), (15, 16), (15, 22), (15, 23), (16, 17), (16, 23), (17, 18), (17, 21), (17, 23), (17, 24), (18, 20), (18, 24), (18, 29), (18, 30), (18, 31), (19, 20), (19, 21), (19, 24), (20, 24), (21, 22), (21, 23), (21, 24), (22, 23), (25, 26), (25, 33), (26, 27), (26, 33), (26, 34), (27, 28), (27, 34), (28, 29), (28, 32), (28, 34), (28, 35), (29, 31), (29, 35), (30, 31), (30, 32), (30, 35), (31, 35), (32, 33), (32, 34), (32, 35), (33, 34)]

/-- Boolean adjacency. -/
def adjB (a b : Fin 36) : Bool :=
  edges.any fun e => (e.1 == a.val && e.2 == b.val) || (e.1 == b.val && e.2 == a.val)

lemma adjB_symm (a b : Fin 36) : adjB a b = adjB b a := by
  unfold adjB
  congr 1
  funext e
  exact Bool.or_comm _ _

lemma edges_ne : ∀ e ∈ edges, e.1 ≠ e.2 := by decide +kernel

lemma adjB_irrefl (a : Fin 36) : adjB a a = false := by
  unfold adjB
  rw [List.any_eq_false]
  intro e he h
  simp only [Bool.or_self, Bool.and_eq_true, beq_iff_eq] at h
  exact edges_ne e he (h.1.trans h.2.symm)

/-- The triangulation `B`. -/
def B : SimpleGraph (Fin 36) where
  Adj a b := adjB a b = true
  symm := ⟨fun a b h => by rw [adjB_symm]; exact h⟩
  loopless := ⟨fun a h => by rw [adjB_irrefl] at h; exact Bool.false_ne_true h⟩

instance : DecidableRel B.Adj := fun a b => inferInstanceAs (Decidable (adjB a b = true))

lemma B_adj (a b : Fin 36) : B.Adj a b ↔ adjB a b = true := Iff.rfl

lemma adj_iff (a b : Fin 36) : B.Adj a b ↔ (a.val, b.val) ∈ edges ∨ (b.val, a.val) ∈ edges := by
  rw [B_adj]
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

end OpenProblemsLab.TotalDomination
