import Mathlib

/-!
# The TxGraffiti conjecture `μ*(G) ≤ H(G)` is false

The **saturation number** `μ*(G)` of a graph is the minimum size of a maximal matching. The
**harmonic index** is `H(G) = ∑_{uv ∈ E(G)} 2 / (d(u) + d(v))`.

TxGraffiti (2023; Davila, Brimkov and Pepper, Conjecture 4) conjectured that every nontrivial
connected graph satisfies `μ*(G) ≤ H(G)`. Bıyıkoğlu (2026) disproved it. C. Gupta
(arXiv:2606.15761, Theorem 1) showed that the friendship graph `F_k` (`k` triangles sharing one hub
vertex) has `μ*(F_k) = k` and `H(F_k) = 2k/(k + 1) + k/2`, so `F_k` is a counterexample for every
`k ≥ 4` (`F_4` has 9 vertices, the smallest order of any counterexample by Gupta's search).

Main results:
* `not_txGraffitiConjecture`: the conjecture is false;
* `saturationNumber_F`, `harmonicIndex_F`: Gupta's Theorem 1;
* `F_counterexample`: `F_k` is a connected counterexample for every `k ≥ 4`.
-/

namespace OpenProblemsLab.Saturation

open SimpleGraph Finset

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `M` is a matching of `G`: a set of edges of `G`, no two of which share a vertex. -/
def IsMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v, ¬ (v ∈ e ∧ v ∈ f)

/-- `M` is a maximal matching: a matching such that every edge of `G` shares a vertex with an edge
of `M` (so no edge can be added). -/
def IsMaximalMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  IsMatching G M ∧ ∀ e ∈ G.edgeSet, ∃ f ∈ M, ∃ v, v ∈ e ∧ v ∈ f

/-- The saturation number `μ*(G)`: the minimum size of a maximal matching. -/
noncomputable def saturationNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ M : Finset (Sym2 V), IsMaximalMatching G M ∧ M.card = k}

/-- The harmonic index `H(G) = ∑_{uv ∈ E(G)} 2 / (d(u) + d(v))`. -/
def harmonicIndex (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  ∑ e ∈ G.edgeFinset,
    Sym2.lift ⟨fun u v => (2 : ℚ) / (G.degree u + G.degree v), fun u v => by dsimp only; rw [add_comm]⟩ e

/-- Twice a sum over edges is the sum over ordered adjacent pairs. -/
theorem two_mul_sum_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] (g : Sym2 V → ℚ) :
    2 * ∑ e ∈ G.edgeFinset, g e = ∑ x, ∑ y, if G.Adj x y then g s(x, y) else 0 := by
  have h1 : ∑ d : G.Dart, g d.edge = 2 * ∑ e ∈ G.edgeFinset, g e := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Dart.edge) (s := Finset.univ) (t := G.edgeFinset)
      (fun d _ => by simp [d.edge_mem]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.sum_congr rfl (fun d hd => by rw [(Finset.mem_filter.1 hd).2]), Finset.sum_const,
      G.dart_edge_fiber_card e (by simpa using he)]
    simp [nsmul_eq_mul]
  have h2 : ∑ d : G.Dart, g d.edge =
      ∑ xy ∈ Finset.univ.filter (fun xy : V × V => G.Adj xy.1 xy.2), g s(xy.1, xy.2) := by
    refine Finset.sum_bij' (fun d _ => (d.fst, d.snd)) (fun xy h => ⟨xy, (Finset.mem_filter.1 h).2⟩)
      ?_ ?_ ?_ ?_ ?_ <;> first | (intros; rfl) | simp
  rw [← h1, h2, Finset.sum_filter, Fintype.sum_prod_type]

end General

/-- **TxGraffiti conjecture** (Davila–Brimkov–Pepper, Conjecture 4): every connected graph with at
least two vertices satisfies `μ*(G) ≤ H(G)`. -/
def TxGraffitiConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → 2 ≤ Fintype.card V → (saturationNumber G : ℚ) ≤ harmonicIndex G

/-! ## Friendship graphs -/

/-- Vertices of `F_k`: `none` is the hub, `some (i, b)` the two rim vertices of triangle `i`. -/
abbrev FV (k : ℕ) := Option (Fin k × Bool)

/-- Adjacency of `F_k`. -/
def adjB {k : ℕ} : FV k → FV k → Bool
  | none, some _ => true
  | some _, none => true
  | some (i, a), some (j, b) => decide (i = j ∧ a ≠ b)
  | none, none => false

/-- The friendship graph `F_k`. -/
def F (k : ℕ) : SimpleGraph (FV k) where
  Adj u v := adjB u v = true
  symm := ⟨fun u v h => by
    rcases u with _ | ⟨i, a⟩ <;> rcases v with _ | ⟨j, b⟩ <;>
      simp only [adjB, decide_eq_true_eq] at h ⊢ <;>
      first | trivial | exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun u h => by rcases u with _ | ⟨i, a⟩ <;> simp_all [adjB]⟩

instance (k : ℕ) : DecidableRel (F k).Adj :=
  fun u v => inferInstanceAs (Decidable (adjB u v = true))

@[simp] theorem adj_hub_rim {k : ℕ} (p : Fin k × Bool) : (F k).Adj none (some p) := rfl
@[simp] theorem adj_rim_hub {k : ℕ} (p : Fin k × Bool) : (F k).Adj (some p) none := rfl
@[simp] theorem not_adj_hub_hub (k : ℕ) : ¬ (F k).Adj none none := by simp [F, adjB]
@[simp] theorem adj_rim_rim {k : ℕ} (i j : Fin k) (a b : Bool) :
    (F k).Adj (some (i, a)) (some (j, b)) ↔ i = j ∧ a ≠ b := by simp [F, adjB]

theorem degree_eq_sum {k : ℕ} (v : FV k) :
    (F k).degree v = ∑ w, if (F k).Adj v w then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter]

theorem degree_hub (k : ℕ) : (F k).degree none = 2 * k := by
  rw [degree_eq_sum]
  simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool, F]
  simp [adjB]; ring

theorem degree_rim {k : ℕ} (i : Fin k) (a : Bool) : (F k).degree (some (i, a)) = 2 := by
  rw [degree_eq_sum]
  simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool, F]
  cases a <;> simp [adjB]

theorem harmonicIndex_F (k : ℕ) : harmonicIndex (F k) = 2 * k / (k + 1) + k / 2 := by
  have h : 2 * harmonicIndex (F k) = _ := two_mul_sum_edgeFinset (F k)
    (Sym2.lift ⟨fun u v => (2 : ℚ) / ((F k).degree u + (F k).degree v),
      fun u v => by dsimp only; rw [add_comm]⟩)
  simp only [Sym2.lift_mk] at h
  simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool, degree_hub,
    degree_rim] at h
  simp at h
  have hk : (k : ℚ) + 1 ≠ 0 := by positivity
  have e : (k : ℚ) * (2 / (2 * k + 2)) + k * (2 / (2 * k + 2)) +
      (k * (2 / (2 + 2 * k)) + k * (2 / (2 + 2)) + (k * (2 / (2 + 2 * k)) + k * (2 / (2 + 2)))) =
      2 * (2 * k / (k + 1) + k / 2) := by
    rw [show (2 : ℚ) + 2 * k = 2 * (k + 1) by ring, show (2 : ℚ) * k + 2 = 2 * (k + 1) by ring]
    field_simp
    ring
  linarith

/-- The rim edge of triangle `i`. -/
def rimEdge {k : ℕ} (i : Fin k) : Sym2 (FV k) := s(some (i, false), some (i, true))

theorem rimEdge_mem {k : ℕ} (i : Fin k) : rimEdge i ∈ (F k).edgeSet := by
  simp [rimEdge]

theorem mem_rimEdge {k : ℕ} {i : Fin k} {v : FV k} (h : v ∈ rimEdge i) : ∃ a, v = some (i, a) := by
  rcases Sym2.mem_iff.1 h with rfl | rfl
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

/-- An edge of `F_k` meets the rim of at most one triangle. -/
theorem same_triangle {k : ℕ} {f : Sym2 (FV k)} (hf : f ∈ (F k).edgeSet) {i j : Fin k} {a b : Bool}
    (hi : some (i, a) ∈ f) (hj : some (j, b) ∈ f) : i = j := by
  induction f using Sym2.ind with
  | _ x y =>
    rw [mem_edgeSet] at hf
    rw [Sym2.mem_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with h | h <;> simp_all [eq_comm]

/-- The rim edges form a maximal matching of size `k`. -/
theorem isMaximalMatching_rim (k : ℕ) :
    IsMaximalMatching (F k) (Finset.univ.image rimEdge) := by
  refine ⟨⟨fun e he => ?_, fun e he f hf hef v hv => ?_⟩, fun e he => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 he
    exact rimEdge_mem i
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hf
    obtain ⟨a, rfl⟩ := mem_rimEdge hv.1
    obtain ⟨b, hb⟩ := mem_rimEdge hv.2
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    exact hef (hb.1 ▸ rfl)
  · induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgeSet] at he
      rcases x with _ | ⟨i, a⟩ <;> rcases y with _ | ⟨j, b⟩
      · exact absurd he (not_adj_hub_hub k)
      · refine ⟨rimEdge j, Finset.mem_image_of_mem _ (Finset.mem_univ _), some (j, b),
          Sym2.mem_mk_right _ _, ?_⟩
        cases b <;> simp [rimEdge]
      · refine ⟨rimEdge i, Finset.mem_image_of_mem _ (Finset.mem_univ _), some (i, a),
          Sym2.mem_mk_left _ _, ?_⟩
        cases a <;> simp [rimEdge]
      · refine ⟨rimEdge i, Finset.mem_image_of_mem _ (Finset.mem_univ _), some (i, a),
          Sym2.mem_mk_left _ _, ?_⟩
        cases a <;> simp [rimEdge]

theorem card_rim (k : ℕ) : (Finset.univ.image (rimEdge (k := k))).card = k := by
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro i j h
  have := Sym2.mem_mk_left (some (i, false)) (some (i, true))
  rw [show s(some (i, false), some (i, true)) = rimEdge j from h] at this
  obtain ⟨a, ha⟩ := mem_rimEdge this
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  exact ha.1

/-- **Gupta, Theorem 1 (first half).** `μ*(F_k) = k`. -/
theorem saturationNumber_F (k : ℕ) : saturationNumber (F k) = k := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨_, isMaximalMatching_rim k, card_rim k⟩
  · have hne : ({c | ∃ M : Finset (Sym2 (FV k)), IsMaximalMatching (F k) M ∧ M.card = c} :
        Set ℕ).Nonempty := ⟨_, _, isMaximalMatching_rim k, card_rim k⟩
    apply le_csInf hne
    rintro c ⟨M, hM, rfl⟩
    choose f hfM v hv using fun i => hM.2 (rimEdge i) (rimEdge_mem i)
    have h := Finset.card_le_card_of_injOn f (s := Finset.univ) (t := M)
      (fun i _ => hfM i) (fun i _ j _ hij => by
        obtain ⟨a, ha⟩ := mem_rimEdge (hv i).1
        obtain ⟨b, hb⟩ := mem_rimEdge (hv j).1
        have h1 := (hv i).2
        have h2 := (hv j).2
        rw [ha] at h1
        rw [hb, ← hij] at h2
        exact same_triangle (hM.1.1 _ (hfM i)) h1 h2)
    simpa using h

theorem connected_F (k : ℕ) : (F k).Connected := by
  have h : ∀ v, (F k).Reachable none v := by
    rintro (_ | p)
    · rfl
    · exact (adj_hub_rim p).reachable
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

theorem card_FV (k : ℕ) : Fintype.card (FV k) = 2 * k + 1 := by
  simp [Fintype.card_option, Fintype.card_prod]; ring

/-- For every `k ≥ 4`, the friendship graph `F_k` is a connected counterexample. -/
theorem F_counterexample {k : ℕ} (hk : 4 ≤ k) :
    (F k).Connected ∧ 2 ≤ Fintype.card (FV k) ∧
      harmonicIndex (F k) < saturationNumber (F k) := by
  refine ⟨connected_F k, by rw [card_FV]; omega, ?_⟩
  rw [harmonicIndex_F, saturationNumber_F]
  have hk' : (4 : ℚ) ≤ k := by exact_mod_cast hk
  have h1 : (2 * k / (k + 1) : ℚ) < k / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- The TxGraffiti conjecture `μ*(G) ≤ H(G)` is false. -/
theorem not_txGraffitiConjecture : ¬ TxGraffitiConjecture := fun h => by
  obtain ⟨h1, h2, h3⟩ := F_counterexample (le_refl 4)
  exact absurd (h _ (F 4) h1 h2) (not_le.2 h3)

end OpenProblemsLab.Saturation
