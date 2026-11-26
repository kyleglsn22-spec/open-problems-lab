import Lab.HenningYeo.Basic

/-!
# Henning–Yeo Theorem 7 from Theorem 6

Henning–Yeo (Graphs Combin. 37 (2021), Thm. 7): every linear 3-uniform `F₇`-free hypergraph
satisfies `17 τ ≤ 5n + 3m`. Their proof deduces it from Theorem 6 (`17 τ ≤ 4n + 4m + h`):
a vertex of degree `≥ 4` can be put into the transversal, and when all degrees are `≤ 3` one
has `m + h ≤ n`.

Here we prove that deduction. `Theorem6Bound` is the (first half of the) statement of
Theorem 6; it is proved in `Lab.HenningYeo.Theorem6`.
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-- The first half of Henning–Yeo Theorem 6: `17 τ ≤ 4n + 4m + h`. -/
def Theorem6Bound (α : Type*) [DecidableEq α] : Prop :=
  ∀ E : Finset (Finset α), IsL3 E → F7Free E →
    ∃ T : Finset α, IsTransversal E T ∧ 17 * T.card ≤ wt E

/-- Double counting: in a 3-uniform hypergraph, `3m = ∑ deg`. -/
lemma sum_deg {E : Finset (Finset α)} (h3 : ∀ e ∈ E, e.card = 3) :
    ∑ x ∈ verts E, deg E x = 3 * E.card := by
  unfold deg
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  rw [Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [← Finset.card_filter, mul_one, ← h3 e he]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨subset_verts he h, h⟩⟩

/-- If all degrees are at most `3`, then `m ≤ n`. -/
lemma card_le_of_deg_le {E : Finset (Finset α)} (h3 : ∀ e ∈ E, e.card = 3)
    (hd : ∀ x, deg E x ≤ 3) : E.card ≤ (verts E).card := by
  have h := sum_deg h3
  have : ∑ x ∈ verts E, deg E x ≤ ∑ _x ∈ verts E, 3 := Finset.sum_le_sum fun x _ => hd x
  simp at this
  omega

lemma deg_mono {E F : Finset (Finset α)} (h : E ⊆ F) (x : α) : deg E x ≤ deg F x :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

lemma isoEdges_subset (E : Finset (Finset α)) : isoEdges E ⊆ E := Finset.filter_subset _ _

/-- An isolated edge is disjoint from the union of the other edges. -/
lemma disjoint_verts_sdiff_isoEdges {E : Finset (Finset α)} :
    Disjoint (verts (isoEdges E)) (verts (E \ isoEdges E)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨e, he, hxe⟩ := mem_verts.1 hx
  obtain ⟨f, hf, hxf⟩ := mem_verts.1 hx'
  have hf' := Finset.mem_sdiff.1 hf
  have hne : f ≠ e := fun h => hf'.2 (h ▸ he)
  exact Finset.disjoint_left.1 ((Finset.mem_filter.1 he).2 f hf'.1 hne) hxe hxf

lemma card_verts_isoEdges {E : Finset (Finset α)} (h3 : ∀ e ∈ E, e.card = 3) :
    (verts (isoEdges E)).card = 3 * hE E := by
  unfold verts hE
  rw [Finset.card_biUnion]
  · rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e he => by simp [h3 e (isoEdges_subset E he)]
  · intro e he f hf hne
    exact (Finset.mem_filter.1 he).2 f (isoEdges_subset E hf) (Ne.symm hne)

/-- With all degrees `≤ 3`: `m + h ≤ n`. -/
lemma card_add_hE_le {E : Finset (Finset α)} (h3 : ∀ e ∈ E, e.card = 3)
    (hd : ∀ x, deg E x ≤ 3) : E.card + hE E ≤ (verts E).card := by
  set I := isoEdges E
  set E0 := E \ I
  have hEI : E = E0 ∪ I := (Finset.sdiff_union_of_subset (isoEdges_subset E)).symm
  have hcard : E.card = E0.card + I.card := by
    rw [hEI, Finset.card_union_of_disjoint Finset.sdiff_disjoint]
  have hv : (verts E).card = (verts E0).card + (verts I).card := by
    rw [hEI, verts_union, Finset.card_union_of_disjoint disjoint_verts_sdiff_isoEdges.symm]
  have h0 : E0.card ≤ (verts E0).card :=
    card_le_of_deg_le (fun e he => h3 e (Finset.sdiff_subset he))
      (fun x => (deg_mono Finset.sdiff_subset x).trans (hd x))
  have hI : (verts I).card = 3 * hE E := card_verts_isoEdges h3
  have : hE E = I.card := rfl
  omega

/-- Deleting a vertex of degree `d` removes exactly `d` edges. -/
lemma card_del_singleton (E : Finset (Finset α)) (v : α) :
    (del E {v}).card + deg E v = E.card := by
  unfold del deg
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext e; simp only [Finset.mem_union, Finset.mem_filter, Finset.disjoint_singleton_right]
    tauto
  · rw [Finset.disjoint_filter]; intro e _ h1 h2; exact (Finset.disjoint_singleton_right.1 h1) h2

lemma card_verts_del_singleton_lt {E : Finset (Finset α)} {v : α} (hv : v ∈ verts E) :
    (verts (del E {v})).card < (verts E).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset (verts_mono (del_subset E _)) |>.2 ⟨v, hv, ?_⟩
  exact fun h => Finset.disjoint_left.1 (verts_del_disjoint E {v}) h (Finset.mem_singleton_self v)

/-- **Henning–Yeo, Theorem 7**, from Theorem 6. -/
theorem theorem7_of_theorem6 (h6 : Theorem6Bound α) (E : Finset (Finset α)) (hL : IsL3 E)
    (hF : F7Free E) :
    ∃ T : Finset α, T ⊆ verts E ∧ IsTransversal E T ∧
      17 * T.card ≤ 5 * (verts E).card + 3 * E.card := by
  induction hn : E.card using Nat.strong_induction_on generalizing E with
  | _ k ih =>
  by_cases hd : ∀ x, deg E x ≤ 3
  · obtain ⟨T, hT, hTw⟩ := h6 E hL hF
    refine ⟨T ∩ verts E, Finset.inter_subset_right, hT.inter_verts, ?_⟩
    have h1 : (T ∩ verts E).card ≤ T.card := Finset.card_le_card Finset.inter_subset_left
    have h2 := card_add_hE_le hL.card3 hd
    unfold wt at hTw
    omega
  · push Not at hd
    obtain ⟨v, hv⟩ := hd
    have hvE : v ∈ verts E := by
      obtain ⟨e, he⟩ : (E.filter (v ∈ ·)).Nonempty := Finset.card_pos.1 (by unfold deg at hv; omega)
      exact mem_verts.2 ⟨e, (Finset.mem_filter.1 he).1, (Finset.mem_filter.1 he).2⟩
    have hc := card_del_singleton E v
    obtain ⟨T, hTs, hT, hTw⟩ := ih (del E {v}).card (by omega) (del E {v}) (hL.mono (del_subset E _))
      (hF.mono (del_subset E _)) rfl
    have hn' := card_verts_del_singleton_lt hvE
    refine ⟨T ∪ {v}, Finset.union_subset (hTs.trans (verts_mono (del_subset E _)))
      (Finset.singleton_subset_iff.2 hvE), hT.of_del, ?_⟩
    have := Finset.card_union_le T {v}
    simp only [Finset.card_singleton] at this
    omega

end OpenProblemsLab.HY
