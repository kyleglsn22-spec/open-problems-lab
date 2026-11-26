import Mathlib

/-!
# Henning–Yeo: basic hypergraph infrastructure

We formalize the Henning–Yeo transversal theorem (Graphs Combin. 37 (2021) 867–890,
Theorems 6 and 7) for finite 3-uniform linear hypergraphs.

A hypergraph is given by its edge set `E : Finset (Finset α)`; its vertex set is the union of
its edges (`verts E`), so it has no isolated vertices. This matches the paper's operation
`H - X`, which deletes isolated vertices, and loses nothing: isolated vertices only make the
bounds easier.
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-- The vertex set of a hypergraph: the union of its edges. -/
def verts (E : Finset (Finset α)) : Finset α := E.biUnion id

/-- 3-uniform linear hypergraphs (the class `L₃` of the paper). -/
structure IsL3 (E : Finset (Finset α)) : Prop where
  card3 : ∀ e ∈ E, e.card = 3
  linear : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e ∩ f).card ≤ 1

/-- `T` meets every edge. -/
def IsTransversal (E : Finset (Finset α)) (T : Finset α) : Prop := ∀ e ∈ E, (e ∩ T).Nonempty

/-- Degree of a vertex. -/
def deg (E : Finset (Finset α)) (x : α) : ℕ := (E.filter (x ∈ ·)).card

/-- Isolated edges (the `E₃`-components). -/
def isoEdges (E : Finset (Finset α)) : Finset (Finset α) :=
  E.filter (fun e => ∀ f ∈ E, f ≠ e → Disjoint e f)

/-- `h(H)`: the number of `E₃`-components. -/
def hE (E : Finset (Finset α)) : ℕ := (isoEdges E).card

/-- The weight `w(H) = 4n + 4m + h`. -/
def wt (E : Finset (Finset α)) : ℕ := 4 * (verts E).card + 4 * E.card + hE E

/-- `H - X`: delete `X` and every edge meeting it (isolated vertices disappear automatically,
since vertices are the union of the remaining edges). -/
def del (E : Finset (Finset α)) (X : Finset α) : Finset (Finset α) :=
  E.filter (fun e => Disjoint e X)

/-- No (not necessarily induced) copy of `F₇`, the affine plane `AG(2,3)` with two points
removed. Same definition as `OpenProblemsLab.E757.LowerBound.F7Free`. -/
def F7Free (E : Finset (Finset α)) : Prop :=
  ∀ g : Fin 7 → α, Function.Injective g →
    ¬ (({g 0, g 1, g 2} : Finset α) ∈ E ∧ ({g 0, g 3, g 4} : Finset α) ∈ E ∧
      ({g 0, g 5, g 6} : Finset α) ∈ E ∧ ({g 1, g 3, g 5} : Finset α) ∈ E ∧
      ({g 2, g 4, g 6} : Finset α) ∈ E)

/-! ### Basic lemmas -/

lemma mem_verts {E : Finset (Finset α)} {x : α} : x ∈ verts E ↔ ∃ e ∈ E, x ∈ e := by
  simp [verts]

lemma subset_verts {E : Finset (Finset α)} {e : Finset α} (he : e ∈ E) : e ⊆ verts E :=
  fun x hx => mem_verts.2 ⟨e, he, hx⟩

lemma verts_mono {E F : Finset (Finset α)} (h : E ⊆ F) : verts E ⊆ verts F := by
  intro x hx
  obtain ⟨e, he, hxe⟩ := mem_verts.1 hx
  exact mem_verts.2 ⟨e, h he, hxe⟩

lemma verts_union (E F : Finset (Finset α)) : verts (E ∪ F) = verts E ∪ verts F := by
  ext x; simp only [mem_verts, Finset.mem_union]
  constructor
  · rintro ⟨e, he | he, hx⟩
    · exact Or.inl ⟨e, he, hx⟩
    · exact Or.inr ⟨e, he, hx⟩
  · rintro (⟨e, he, hx⟩ | ⟨e, he, hx⟩)
    · exact ⟨e, Or.inl he, hx⟩
    · exact ⟨e, Or.inr he, hx⟩

lemma IsL3.mono {E F : Finset (Finset α)} (hF : IsL3 F) (h : E ⊆ F) : IsL3 E :=
  ⟨fun e he => hF.card3 e (h he), fun e he f hf hne => hF.linear e (h he) f (h hf) hne⟩

lemma F7Free.mono {E F : Finset (Finset α)} (hF : F7Free F) (h : E ⊆ F) : F7Free E :=
  fun g hg ⟨h1, h2, h3, h4, h5⟩ => hF g hg ⟨h h1, h h2, h h3, h h4, h h5⟩

lemma del_subset (E : Finset (Finset α)) (X : Finset α) : del E X ⊆ E :=
  Finset.filter_subset _ _

lemma mem_del {E : Finset (Finset α)} {X : Finset α} {e : Finset α} :
    e ∈ del E X ↔ e ∈ E ∧ Disjoint e X := Finset.mem_filter

lemma verts_del_disjoint (E : Finset (Finset α)) (X : Finset α) : Disjoint (verts (del E X)) X := by
  rw [Finset.disjoint_left]
  intro x hx hxX
  obtain ⟨e, he, hxe⟩ := mem_verts.1 hx
  exact Finset.disjoint_left.1 (mem_del.1 he).2 hxe hxX

/-- Extending a transversal of `H - X` by `X` gives a transversal of `H`. -/
lemma IsTransversal.of_del {E : Finset (Finset α)} {X T : Finset α}
    (hT : IsTransversal (del E X) T) : IsTransversal E (T ∪ X) := by
  intro e he
  by_cases hd : Disjoint e X
  · obtain ⟨y, hy⟩ := hT e (mem_del.2 ⟨he, hd⟩)
    exact ⟨y, Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hy).1,
      Finset.mem_union_left _ (Finset.mem_inter.1 hy).2⟩⟩
  · obtain ⟨y, hye, hyX⟩ := Finset.not_disjoint_iff.1 hd
    exact ⟨y, Finset.mem_inter.2 ⟨hye, Finset.mem_union_right _ hyX⟩⟩

lemma IsTransversal.mono {E F : Finset (Finset α)} {T : Finset α} (hT : IsTransversal F T)
    (h : E ⊆ F) : IsTransversal E T := fun e he => hT e (h he)

lemma IsTransversal.union {E F : Finset (Finset α)} {T U : Finset α} (hT : IsTransversal E T)
    (hU : IsTransversal F U) : IsTransversal (E ∪ F) (T ∪ U) := by
  intro e he
  rcases Finset.mem_union.1 he with he | he
  · obtain ⟨y, hy⟩ := hT e he
    exact ⟨y, by simp only [Finset.mem_inter, Finset.mem_union] at hy ⊢; tauto⟩
  · obtain ⟨y, hy⟩ := hU e he
    exact ⟨y, by simp only [Finset.mem_inter, Finset.mem_union] at hy ⊢; tauto⟩

/-- A transversal can always be taken inside the vertex set. -/
lemma IsTransversal.inter_verts {E : Finset (Finset α)} {T : Finset α} (hT : IsTransversal E T) :
    IsTransversal E (T ∩ verts E) := by
  intro e he
  obtain ⟨y, hy⟩ := hT e he
  refine ⟨y, Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hy).1, Finset.mem_inter.2
    ⟨(Finset.mem_inter.1 hy).2, subset_verts he (Finset.mem_inter.1 hy).1⟩⟩⟩

end OpenProblemsLab.HY
