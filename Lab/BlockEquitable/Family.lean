import Lab.BlockEquitable.Counterexample

/-!
# The whole family `G_{d,k}`: the gap `χ_= − L` is unbounded on connected block graphs

Lauri (arXiv:2608.14517, Theorem 1.1): for all `d ≥ 2` and `k ≥ 4d − 1` there is a connected
block graph `G_{d,k}` with `L(G_{d,k}) = k` and `χ_=(G_{d,k}) = k + d`. Hence no bound
`χ_=(G) ≤ L(G) + C` holds for connected block graphs. Definitions (`IsBlockGraph`, `αAt`, `αmin`,
`L`, `IsEquitableColoring`, `equitableChromaticNumber`) are those of
`Lab/BlockEquitable/Counterexample.lean`.

* `lauri_family`: for `d ≥ 2`, `k ≥ 4d − 1`, `G_{d,k}` is a connected block graph with
  `L = k` and `χ_= = k + d`;
* `gap_unbounded`: for every `C` there is a connected block graph with `χ_= > L + C`.

## The graph

With `m = 4d − 1`, the vertices are `Fin m ⊕ (Unit ⊕ (Fin 4 × Fin (k − 1)))`:

* `inl i`: the central clique `Q ≅ K_m`, with `v = 0`, `w = 1`, `c = 2`;
* `inr (inl ())`: the pendant vertex `u`, adjacent to `c` only;
* `inr (inr (j, t))`: private vertex `t` of block `j`; each block is a `K_{k−1}` joined to `v`
  (`j = 0, 1`) or to `w` (`j = 2, 3`), so it forms a `K_k` block with its anchor.

There are `m + 1 + 4(k − 1) = 4(k + d − 1)` vertices.

## Proof (following the paper)

* Independent sets meet each part (`Q`, `{u}`, each private block) at most once; the
  non-neighbours of `v` lie in `u` and the blocks at `w`, so `α(G,v) ≤ 4`, and `≤ 3` without `u`
  (similarly for `w`). Every vertex lies in an independent 4-set, so `α_min = 4`.
* `ω = k` (the blocks at `v`, `w` are `K_k` and `m ≤ k`), and `⌈(4(k+d−1)+1)/5⌉ ≤ k`, so `L = k`.
* For `q < k + d` every class of an equitable `q`-colouring has at least
  `⌊4(k+d−1)/q⌋ ≥ 4` vertices, but the class of `v` or `w` that misses `u` has at most 3.
* The paper's equitable `(k+d)`-colouring (colours shifted to start at `0`): `Q` gets `0,…,m−1`
  injectively (`v ↦ 0`, `w ↦ 1`, `c ↦ 2`), `u ↦ 0`, and block `j` uses, in increasing order,
  every colour outside an omitted set `O_j` of size `d + 1`:
  `O₀ = {0} ∪ [2,d] ∪ {m−1}`, `O₁ = {0} ∪ [d+1,2d−1] ∪ {m−1}`, `O₂ = {1} ∪ [2d,3d−1]`,
  `O₃ = {1} ∪ [3d,4d−3] ∪ {m, m+1}`. Every colour class has 3 or 4 vertices.
-/

namespace OpenProblemsLab.BlockEquitable.Family

open Finset SimpleGraph OpenProblemsLab.BlockEquitable

variable {d k : ℕ}

/-- Vertex type of `G_{d,k}`. -/
abbrev V (d k : ℕ) := Fin (4 * d - 1) ⊕ (Unit ⊕ (Fin 4 × Fin (k - 1)))

/-- The index in `Q` of the anchor of private block `j` (`v = 0` or `w = 1`). -/
def anc (j : Fin 4) : ℕ := if j.1 < 2 then 0 else 1

/-- Adjacency of `G_{d,k}`. -/
def adjR : V d k → V d k → Prop
  | .inl i, .inl i' => i ≠ i'
  | .inl i, .inr (.inl _) => i.1 = 2
  | .inr (.inl _), .inl i => i.1 = 2
  | .inl i, .inr (.inr (j, _)) => i.1 = anc j
  | .inr (.inr (j, _)), .inl i => i.1 = anc j
  | .inr (.inr (j, t)), .inr (.inr (j', t')) => j = j' ∧ t ≠ t'
  | _, _ => False

/-- The graph `G_{d,k}`. -/
def G (d k : ℕ) : SimpleGraph (V d k) where
  Adj := adjR
  symm := ⟨by
    rintro (a | ⟨⟩ | ⟨j, t⟩) (b | ⟨⟩ | ⟨j', t'⟩) h <;> simp only [adjR] at h ⊢ <;>
      first | exact h | exact Ne.symm h | exact ⟨h.1.symm, Ne.symm h.2⟩⟩
  loopless := ⟨by
    rintro (a | ⟨⟩ | ⟨j, t⟩) h <;> simp [adjR] at h⟩

@[simp] theorem adj_inl_inl (i i' : Fin (4 * d - 1)) :
    (G d k).Adj (.inl i) (.inl i') ↔ i ≠ i' := Iff.rfl
@[simp] theorem adj_inl_u (i : Fin (4 * d - 1)) (x : Unit) :
    (G d k).Adj (.inl i) (.inr (.inl x)) ↔ i.1 = 2 := Iff.rfl
@[simp] theorem adj_u_inl (i : Fin (4 * d - 1)) (x : Unit) :
    (G d k).Adj (.inr (.inl x)) (.inl i) ↔ i.1 = 2 := Iff.rfl
@[simp] theorem adj_inl_p (i : Fin (4 * d - 1)) (j : Fin 4) (t : Fin (k - 1)) :
    (G d k).Adj (.inl i) (.inr (.inr (j, t))) ↔ i.1 = anc j := Iff.rfl
@[simp] theorem adj_p_inl (i : Fin (4 * d - 1)) (j : Fin 4) (t : Fin (k - 1)) :
    (G d k).Adj (.inr (.inr (j, t))) (.inl i) ↔ i.1 = anc j := Iff.rfl
@[simp] theorem adj_p_p (j j' : Fin 4) (t t' : Fin (k - 1)) :
    (G d k).Adj (.inr (.inr (j, t))) (.inr (.inr (j', t'))) ↔ j = j' ∧ t ≠ t' := Iff.rfl
@[simp] theorem not_adj_u_p (x : Unit) (j : Fin 4) (t : Fin (k - 1)) :
    ¬ (G d k).Adj (.inr (.inl x)) (.inr (.inr (j, t))) := id
@[simp] theorem not_adj_p_u (x : Unit) (j : Fin 4) (t : Fin (k - 1)) :
    ¬ (G d k).Adj (.inr (.inr (j, t))) (.inr (.inl x)) := id
@[simp] theorem not_adj_u_u (x y : Unit) :
    ¬ (G d k).Adj (.inr (.inl x) : V d k) (.inr (.inl y)) := id

theorem card_V (hd : 1 ≤ d) (hk : 1 ≤ k) : Fintype.card (V d k) = 4 * (k + d - 1) := by
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_prod, Fintype.card_fin]
  omega

/-! ### Parts -/

/-- The part of a vertex: `0` for `Q`, `5` for `u`, `j + 1` for private block `j`. -/
def part : V d k → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 5
  | .inr (.inr (j, _)) => j.1 + 1

@[simp] theorem part_inl (i : Fin (4 * d - 1)) : part (.inl i : V d k) = 0 := rfl
@[simp] theorem part_u (x : Unit) : part (.inr (.inl x) : V d k) = 5 := rfl
@[simp] theorem part_p (j : Fin 4) (t : Fin (k - 1)) :
    part (.inr (.inr (j, t)) : V d k) = j.1 + 1 := rfl

theorem same_part_adj : ∀ a b : V d k, a ≠ b → part a = part b → (G d k).Adj a b := by
  rintro (a | ⟨⟩ | ⟨j, t⟩) (b | ⟨⟩ | ⟨j', t'⟩) hab h <;> simp only [part] at h <;>
    try omega
  · exact fun h' => hab (h' ▸ rfl)
  · exact (hab rfl).elim
  · have hj : j = j' := Fin.ext (by omega)
    subst hj
    exact (adj_p_p _ _ _ _).2 ⟨rfl, fun h' => hab (h' ▸ rfl)⟩

/-- Independent sets meet each part at most once. -/
theorem indep_card_le (s : Finset (V d k)) (hs : (G d k).IsIndepSet (s : Set (V d k)))
    (P : Finset ℕ) (hP : ∀ y ∈ s, part y ∈ P) : s.card ≤ P.card := by
  rw [← card_image_of_injOn (f := part) (fun x hx y hy hxy => by
    by_contra hne; exact hs hx hy hne (same_part_adj x y hne hxy))]
  exact card_le_card fun n hn => by
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hn; exact hP y hy

/-! ### Block graph and connectivity -/

/-- Each part other than `Q` is cut off by one vertex `z` adjacent to it. -/
theorem sep (hd : 1 ≤ d) (a : V d k) (ha : part a ≠ 0) : ∃ z, (G d k).Adj a z ∧
    ∀ y y', part y = part a → (G d k).Adj y y' → y' ≠ z → part y' = part a := by
  rcases a with a | ⟨⟩ | ⟨j, t⟩
  · exact (ha rfl).elim
  · refine ⟨.inl ⟨2, by omega⟩, by simp, ?_⟩
    rintro (y | ⟨⟩ | ⟨j', t'⟩) (y' | ⟨⟩ | ⟨j'', t''⟩) hy hyy' hz <;>
      simp_all [part] <;> try omega
    exact hz (Fin.ext hyy')
  · have hanc : anc j < 4 * d - 1 := by unfold anc; split_ifs <;> omega
    refine ⟨.inl ⟨anc j, hanc⟩, by simp, ?_⟩
    rintro (y | ⟨⟩ | ⟨j', t'⟩) (y' | ⟨⟩ | ⟨j'', t''⟩) hy hyy' hz <;>
      simp_all [part] <;> try omega
    have hj : j' = j := Fin.ext hy
    subst hj; exact hz (Fin.ext hyy')

theorem walk_closed {T : Set (V d k)} (P : V d k → Prop)
    (h : ∀ x y : T, (G d k).Adj x.1 y.1 → P x.1 → P y.1) {x y : T}
    (p : ((G d k).induce T).Walk x y) (hx : P x.1) : P y.1 := by
  induction p with
  | nil => exact hx
  | cons hadj _ ih => exact ih (h _ _ hadj hx)

theorem isBlockGraph (hd : 1 ≤ d) : IsBlockGraph (G d k) := by
  intro S hS hS' a ha b hb hab
  by_contra hna
  have hdiff : part a ≠ part b := fun h => hna (same_part_adj a b hab h)
  obtain ⟨a', b', ha', hb', hna', hpa, hpb⟩ : ∃ a' b', a' ∈ S ∧ b' ∈ S ∧
      ¬ (G d k).Adj a' b' ∧ part a' ≠ 0 ∧ part b' ≠ part a' := by
    by_cases h0 : part a = 0
    · exact ⟨b, a, hb, ha, fun h => hna h.symm, by omega, by omega⟩
    · exact ⟨a, b, ha, hb, hna, h0, Ne.symm hdiff⟩
  obtain ⟨z, haz, hcl⟩ := sep hd a' hpa
  have hbz : b' ≠ z := fun h => hna' (h ▸ haz)
  obtain ⟨T, hT, hzT, haT, hbT⟩ : ∃ T : Set (V d k), ((G d k).induce T).Connected ∧ z ∉ T ∧
      a' ∈ T ∧ b' ∈ T := by
    by_cases hz : z ∈ S
    · exact ⟨S \ {z}, hS' z hz, by simp, ⟨ha', haz.ne⟩, ⟨hb', hbz⟩⟩
    · exact ⟨S, hS, hz, ha', hb'⟩
  obtain ⟨p⟩ := hT.preconnected ⟨a', haT⟩ ⟨b', hbT⟩
  exact hpb (walk_closed (T := T) (fun y : V d k => part y = part a')
    (fun x y hxy hx => hcl x.1 y.1 hx hxy fun h => hzT (h ▸ y.2)) p rfl)

theorem connected (hd : 1 ≤ d) : (G d k).Connected := by
  set v : V d k := .inl ⟨0, by omega⟩
  have h0 : ∀ x, (G d k).Reachable v x := by
    rintro (i | ⟨⟩ | ⟨j, t⟩)
    · by_cases hi : i.1 = 0
      · have : i = ⟨0, by omega⟩ := Fin.ext hi
        rw [this]
      · exact Adj.reachable (by simp [v, Fin.ext_iff]; omega)
    · have hc : (G d k).Adj v (.inl ⟨2, by omega⟩) := by simp [v, Fin.ext_iff]
      exact hc.reachable.trans (Adj.reachable (by simp))
    · have hanc : anc j < 4 * d - 1 := by unfold anc; split_ifs <;> omega
      have h2 : (G d k).Adj (.inl ⟨anc j, hanc⟩) (.inr (.inr (j, t))) := by simp
      by_cases h : anc j = 0
      · have : (⟨anc j, hanc⟩ : Fin (4 * d - 1)) = ⟨0, by omega⟩ := Fin.ext h
        rw [this] at h2; exact h2.reachable
      · exact (Adj.reachable (by simp [v, Fin.ext_iff]; omega)).trans h2.reachable
  exact ⟨fun x y => (h0 x).symm.trans (h0 y)⟩

/-! ### Clique number -/

theorem class_card (hk : 2 ≤ k) (a : V d k) (ha : part a ≠ 0) :
    (univ.filter fun y : V d k => part y = part a).card ≤ k - 1 := by
  rcases a with a | ⟨⟩ | ⟨j, t⟩
  · exact (ha rfl).elim
  · refine (card_le_card (t := {.inr (.inl ())}) ?_).trans (by simp; omega)
    rintro (y | ⟨⟩ | ⟨j', t'⟩) hy <;> rw [Finset.mem_filter] at hy <;> simp at hy ⊢
    have := j'.2; omega
  · refine (card_le_card (t := univ.image fun t' : Fin (k - 1) => (.inr (.inr (j, t')) : V d k))
      ?_).trans (card_image_le.trans (by simp))
    have := j.2
    rintro (y | ⟨⟩ | ⟨j', t'⟩) hy <;> rw [Finset.mem_filter] at hy <;> simp at hy ⊢
    · omega
    · exact Fin.ext hy.symm

theorem clique_card_le (hd : 1 ≤ d) (hk : 4 * d - 1 ≤ k) (s : Finset (V d k))
    (hs : (G d k).IsClique (s : Set (V d k))) : s.card ≤ k := by
  by_cases h : ∃ a ∈ s, part a ≠ 0
  · obtain ⟨a, ha, hpa⟩ := h
    obtain ⟨z, -, hcl⟩ := sep hd a hpa
    have hsub : s ⊆ insert z (univ.filter fun y : V d k => part y = part a) := by
      intro y hy
      by_cases hya : y = a
      · simp [hya]
      by_cases hyz : y = z
      · simp [hyz]
      simp only [mem_insert, mem_filter, mem_univ, true_and]
      exact Or.inr (hcl a y rfl (hs ha hy (Ne.symm hya)) hyz)
    have := class_card (by omega) a hpa
    have := card_insert_le z (univ.filter fun y : V d k => part y = part a)
    have := card_le_card hsub
    omega
  · push Not at h
    have hsub : s ⊆ univ.map ⟨Sum.inl, Sum.inl_injective⟩ := by
      rintro (y | ⟨⟩ | ⟨j, t⟩) hy
      · simp
      · exact absurd (h _ hy) (by simp)
      · exact absurd (h _ hy) (by simp)
    have := card_le_card hsub
    simp at this
    omega

theorem cliqueNum_eq (hd : 1 ≤ d) (hk : 4 * d - 1 ≤ k) : (G d k).cliqueNum = k := by
  apply le_antisymm
  · obtain ⟨s, hs⟩ := (G d k).exists_isNClique_cliqueNum
    rw [← hs.card_eq]; exact clique_card_le hd hk s hs.isClique
  · set B : Finset (V d k) := insert (.inl ⟨0, by omega⟩)
      (univ.image fun t : Fin (k - 1) => .inr (.inr (0, t)))
    have hB : (G d k).IsClique (B : Set (V d k)) := by
      intro a ha b hb hab
      simp only [B, coe_insert, coe_image, coe_univ, Set.image_univ, Set.mem_insert_iff,
        Set.mem_range] at ha hb
      rcases ha with rfl | ⟨t, rfl⟩ <;> rcases hb with rfl | ⟨t', rfl⟩
      · exact (hab rfl).elim
      · simp [anc]
      · simp [anc]
      · simp only [adj_p_p, true_and]; exact fun h => hab (h ▸ rfl)
    have hcard : B.card = k := by
      rw [card_insert_of_notMem (by simp),
        card_image_of_injective _ (fun a b h => by simpa using h)]
      simp; omega
    have := hB.card_le_cliqueNum; omega

/-! ### `α_min = 4` -/

theorem four_le_of (l : List (V d k)) (hl : l.Pairwise fun y z => y ≠ z ∧ ¬ (G d k).Adj y z)
    (hlen : l.length = 4) (x : V d k) (hx : x ∈ l) : 4 ≤ αAt (G d k) x := by
  have : Std.Symm fun y z : V d k => y ≠ z ∧ ¬ (G d k).Adj y z :=
    ⟨fun y z h => ⟨h.1.symm, fun h' => h.2 h'.symm⟩⟩
  refine le_csSup ⟨Fintype.card (V d k), ?_⟩ ⟨l.toFinset, ?_, by simpa using hx, ?_⟩
  · rintro n ⟨s, -, -, rfl⟩; exact card_le_univ s
  · intro a ha b hb hab
    exact (hl.forall (by simpa using ha) (by simpa using hb) hab).2
  · rw [List.toFinset_card_of_nodup (hl.imp fun h => h.1), hlen]

theorem four_le_αAt (hd : 1 ≤ d) (hk : 2 ≤ k) (x : V d k) : 4 ≤ αAt (G d k) x := by
  have t0 : Fin (k - 1) := ⟨0, by omega⟩
  set u : V d k := .inr (.inl ())
  rcases x with i | ⟨⟩ | ⟨j, t⟩
  · by_cases h0 : i.1 = 0
    · refine four_le_of [.inl i, u, .inr (.inr (2, t0)), .inr (.inr (3, t0))] ?_ rfl _ (by simp)
      simp [u, anc, h0]
    by_cases h1 : i.1 = 1
    · refine four_le_of [.inl i, u, .inr (.inr (0, t0)), .inr (.inr (1, t0))] ?_ rfl _ (by simp)
      simp [u, anc, h1]
    by_cases h2 : i.1 = 2
    · refine four_le_of [.inl i, .inr (.inr (0, t0)), .inr (.inr (1, t0)), .inr (.inr (2, t0))]
        ?_ rfl _ (by simp)
      simp [anc, h2]
    · refine four_le_of [.inl i, u, .inr (.inr (0, t0)), .inr (.inr (2, t0))] ?_ rfl _ (by simp)
      simp [u, anc, h0, h1, h2]
  · refine four_le_of [.inr (.inl ()), .inl ⟨0, by omega⟩, .inr (.inr (2, t0)),
      .inr (.inr (3, t0))] ?_ rfl _ (by simp)
    simp [anc]
  · by_cases hj : j.1 < 2
    · refine four_le_of [.inr (.inr (j, t)), .inl ⟨1, by omega⟩, u,
        .inr (.inr (⟨1 - j.1, by omega⟩, t0))] ?_ rfl _ (by simp)
      simp [u, anc, hj, Fin.ext_iff]; omega
    · refine four_le_of [.inr (.inr (j, t)), .inl ⟨0, by omega⟩, u,
        .inr (.inr (⟨5 - j.1, by omega⟩, t0))] ?_ rfl _ (by simp)
      have := j.2
      simp [u, anc, hj, Fin.ext_iff]; omega

/-- The non-neighbours of `v` lie in `u` and the blocks at `w`. -/
theorem part_nonadj_v (hd : 1 ≤ d) (y : V d k) (hy : y ≠ .inl ⟨0, by omega⟩)
    (hn : ¬ (G d k).Adj (.inl ⟨0, by omega⟩) y) : part y = 5 ∨ part y = 3 ∨ part y = 4 := by
  rcases y with i | ⟨⟩ | ⟨j, t⟩
  · simp at hn; subst hn; exact absurd rfl hy
  · simp
  · have := j.2; simp [anc] at hn ⊢; omega

/-- The non-neighbours of `w` lie in `u` and the blocks at `v`. -/
theorem part_nonadj_w (hd : 1 ≤ d) (y : V d k) (hy : y ≠ .inl ⟨1, by omega⟩)
    (hn : ¬ (G d k).Adj (.inl ⟨1, by omega⟩) y) : part y = 5 ∨ part y = 1 ∨ part y = 2 := by
  rcases y with i | ⟨⟩ | ⟨j, t⟩
  · simp at hn; subst hn; exact absurd rfl hy
  · simp
  · have := j.2; simp [anc] at hn ⊢; omega

theorem αAt_v_le (hd : 1 ≤ d) : αAt (G d k) (.inl ⟨0, by omega⟩) ≤ 4 := by
  refine csSup_le ⟨1, {.inl ⟨0, by omega⟩}, by simp, by simp, by simp⟩ ?_
  rintro n ⟨s, hs, h0, rfl⟩
  refine indep_card_le s hs {0, 3, 4, 5} fun y hy => ?_
  by_cases hy0 : y = .inl ⟨0, by omega⟩
  · simp [hy0]
  rcases part_nonadj_v hd y hy0 (hs h0 hy (Ne.symm hy0)) with h | h | h <;> simp [h]

theorem αmin_eq (hd : 1 ≤ d) (hk : 2 ≤ k) : αmin (G d k) = 4 :=
  le_antisymm ((ciInf_le (OrderBot.bddBelow _) _).trans (αAt_v_le hd))
    (le_ciInf (four_le_αAt hd hk))

theorem L_eq (hd : 1 ≤ d) (hk : 4 * d - 1 ≤ k) : L (G d k) = k := by
  rw [L, cliqueNum_eq hd hk, αmin_eq hd (by omega), card_V hd (by omega)]
  apply max_eq_left
  omega


/-! ### No equitable colouring with fewer than `k + d` colours -/

theorem small_class (hd : 1 ≤ d) (s : Finset (V d k)) (hs : (G d k).IsIndepSet (s : Set (V d k)))
    (hu : (.inr (.inl ()) : V d k) ∉ s)
    (h : (.inl ⟨0, by omega⟩ : V d k) ∈ s ∨ (.inl ⟨1, by omega⟩ : V d k) ∈ s) : s.card ≤ 3 := by
  rcases h with h0 | h1
  · refine indep_card_le s hs {0, 3, 4} fun y hy => ?_
    by_cases hy0 : y = .inl ⟨0, by omega⟩
    · simp [hy0]
    rcases part_nonadj_v hd y hy0 (hs h0 hy (Ne.symm hy0)) with h | h | h
    · rcases y with _ | ⟨⟨⟩⟩ | ⟨j, t⟩
      · simp at h
      · exact (hu hy).elim
      · have := j.2; simp at h; omega
    all_goals simp [h]
  · refine indep_card_le s hs {0, 1, 2} fun y hy => ?_
    by_cases hy1 : y = .inl ⟨1, by omega⟩
    · simp [hy1]
    rcases part_nonadj_w hd y hy1 (hs h1 hy (Ne.symm hy1)) with h | h | h
    · rcases y with _ | ⟨⟨⟩⟩ | ⟨j, t⟩
      · simp at h
      · exact (hu hy).elim
      · have := j.2; simp at h; omega
    all_goals simp [h]

theorem no_equitable_lt (hd : 1 ≤ d) (hk : 4 * d - 1 ≤ k) (q : ℕ) (hq : q < k + d)
    (c : V d k → Fin q) : ¬ IsEquitableColoring (G d k) c := by
  rintro ⟨hp, hcl⟩
  have hq1 : 0 < q := (c (.inl ⟨0, by omega⟩)).pos
  have hvw : (G d k).Adj (.inl ⟨0, by omega⟩) (.inl ⟨1, by omega⟩) := by simp
  have key : ∀ x : V d k, (x = .inl ⟨0, by omega⟩ ∨ x = .inl ⟨1, by omega⟩) →
      c (.inr (.inl ())) ≠ c x → False := by
    intro x hx hux
    set s := univ.filter fun y => c y = c x
    have hs : (G d k).IsIndepSet (s : Set (V d k)) := by
      intro a ha b hb _ hab
      simp only [s, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      exact hp a b hab (ha.trans hb.symm)
    have hcard : s.card ≤ 3 := small_class hd s hs (by simpa [s] using hux)
      (by rcases hx with rfl | rfl <;> simp [s])
    have hlow : Fintype.card (V d k) / q ≤ s.card := (hcl (c x)).1
    rw [card_V hd (by omega)] at hlow
    have : 4 ≤ 4 * (k + d - 1) / q := (Nat.le_div_iff_mul_le hq1).2 (by omega)
    omega
  by_cases h : c (.inr (.inl ())) = c (.inl ⟨0, by omega⟩)
  · exact key _ (Or.inr rfl) (fun h' => hp _ _ hvw (h.symm.trans h'))
  · exact key _ (Or.inl rfl) h

/-! ### The equitable `(k + d)`-colouring -/

/-- Colour of private vertex `t` of block `j`: the `t`-th colour outside the omitted set `O_j`. -/
def f (d : ℕ) (j : Fin 4) (t : ℕ) : ℕ :=
  if j.1 = 0 then (if t = 0 then 1 else if t ≤ 3 * d - 3 then t + d else t + d + 1)
  else if j.1 = 1 then (if t < d then t + 1 else if t ≤ 3 * d - 3 then t + d else t + d + 1)
  else if j.1 = 2 then (if t = 0 then 0 else if t ≤ 2 * d - 2 then t + 1 else t + d + 1)
  else (if t = 0 then 0 else if t ≤ 3 * d - 2 then t + 1 else if t = 3 * d - 1 then 4 * d - 2
    else t + d + 1)

/-- The colours used by block `j` (the complement of `O_j`). -/
def allowed (d : ℕ) (j : Fin 4) (x : ℕ) : Prop :=
  if j.1 = 0 then x = 1 ∨ (d + 1 ≤ x ∧ x ≤ 4 * d - 3) ∨ 4 * d - 1 ≤ x
  else if j.1 = 1 then (1 ≤ x ∧ x ≤ d) ∨ (2 * d ≤ x ∧ x ≤ 4 * d - 3) ∨ 4 * d - 1 ≤ x
  else if j.1 = 2 then x = 0 ∨ (2 ≤ x ∧ x ≤ 2 * d - 1) ∨ 3 * d ≤ x
  else x = 0 ∨ (2 ≤ x ∧ x ≤ 3 * d - 1) ∨ x = 4 * d - 2 ∨ 4 * d + 1 ≤ x

instance (d : ℕ) (j : Fin 4) : DecidablePred (allowed d j) := fun x => by
  unfold allowed; split_ifs <;> infer_instance

/-- The inverse of `f d j` on the allowed colours. -/
def g (d : ℕ) (j : Fin 4) (x : ℕ) : ℕ :=
  if j.1 = 0 then (if x = 1 then 0 else if x ≤ 4 * d - 3 then x - d else x - d - 1)
  else if j.1 = 1 then (if x ≤ d then x - 1 else if x ≤ 4 * d - 3 then x - d else x - d - 1)
  else if j.1 = 2 then (if x = 0 then 0 else if x ≤ 2 * d - 1 then x - 1 else x - d - 1)
  else (if x = 0 then 0 else if x ≤ 3 * d - 1 then x - 1 else if x = 4 * d - 2 then 3 * d - 1
    else x - d - 1)

theorem f_eq_iff (hd : 2 ≤ d) (j : Fin 4) (t x : ℕ) :
    f d j t = x ↔ allowed d j x ∧ t = g d j x := by
  fin_cases j <;> simp only [f, allowed, g] <;> norm_num <;> split_ifs <;> omega

theorem f_inj (hd : 2 ≤ d) (j : Fin 4) {t t' : ℕ} (h : f d j t = f d j t') : t = t' :=
  ((f_eq_iff hd j t _).1 h).2.trans ((f_eq_iff hd j t' _).1 rfl).2.symm

theorem f_le (j : Fin 4) (t : ℕ) : f d j t ≤ t + d + 1 := by
  fin_cases j <;> simp only [f] <;> norm_num <;> split_ifs <;> omega

theorem f_ne_anc (hd : 2 ≤ d) (j : Fin 4) (t : ℕ) : f d j t ≠ anc j := by
  fin_cases j <;> simp only [f, anc] <;> norm_num <;> intro h <;> split_ifs at h <;> omega

theorem g_lt (hd : 2 ≤ d) (hk : 4 * d - 1 ≤ k) (j : Fin 4) (x : ℕ) (hx : x < k + d)
    (ha : allowed d j x) : g d j x < k - 1 := by
  fin_cases j <;> simp only [allowed, g] at ha ⊢ <;> norm_num at ha ⊢ <;> split_ifs <;> omega

/-- The colouring as natural numbers. -/
def col (d : ℕ) : V d k → ℕ
  | .inl i => i.1
  | .inr (.inl _) => 0
  | .inr (.inr (j, t)) => f d j t.1

theorem col_lt (hd : 2 ≤ d) (hk : 4 * d - 1 ≤ k) (y : V d k) : col d y < k + d := by
  rcases y with i | ⟨⟩ | ⟨j, t⟩
  · have := i.2; simp only [col]; omega
  · simp only [col]; omega
  · have := f_le (d := d) j t.1; have := t.2; simp only [col]; omega

/-- The equitable `(k + d)`-colouring. -/
def colour (hd : 2 ≤ d) (hk : 4 * d - 1 ≤ k) (y : V d k) : Fin (k + d) :=
  ⟨col d y, col_lt hd hk y⟩

theorem colour_proper (hd : 2 ≤ d) (hk : 4 * d - 1 ≤ k) :
    ∀ y y', (G d k).Adj y y' → colour hd hk y ≠ colour hd hk y' := by
  rintro (i | ⟨⟩ | ⟨j, t⟩) (i' | ⟨⟩ | ⟨j', t'⟩) h <;>
    simp only [colour, col, ne_eq, Fin.mk.injEq] <;> simp at h
  · exact fun h' => h (Fin.ext h')
  · omega
  · have := f_ne_anc hd j' t'.1; omega
  · omega
  · have := f_ne_anc hd j t.1; omega
  · obtain ⟨rfl, h⟩ := h
    exact fun h' => h (Fin.ext (f_inj hd j h'))

/-- Size of the colour class of `x`. -/
theorem class_card_eq (hd : 2 ≤ d) (hk : 4 * d - 1 ≤ k) (x : Fin (k + d)) :
    (univ.filter fun y => colour hd hk y = x).card =
      (if x.1 < 4 * d - 1 then 1 else 0) + (if x.1 = 0 then 1 else 0) +
        ∑ j : Fin 4, (if allowed d j x.1 then 1 else 0) := by
  have hQ : (∑ i : Fin (4 * d - 1), if colour hd hk (.inl i) = x then 1 else 0) =
      if x.1 < 4 * d - 1 then 1 else 0 := by
    simp only [colour, col, Fin.ext_iff]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i = x.1 then 1 else 0), sum_ite_eq']
    simp
  have hU : (∑ e : Unit, if colour hd hk (.inr (.inl e)) = x then 1 else 0) =
      if x.1 = 0 then 1 else 0 := by
    simp [colour, col, Fin.ext_iff, eq_comm]
  have hP : ∀ j : Fin 4, (∑ t : Fin (k - 1),
      if colour hd hk (.inr (.inr (j, t))) = x then 1 else 0) =
      if allowed d j x.1 then 1 else 0 := by
    intro j
    simp only [colour, col, Fin.ext_iff]
    rw [Fin.sum_univ_eq_sum_range (fun t => if f d j t = x.1 then 1 else 0)]
    simp only [f_eq_iff hd]
    by_cases ha : allowed d j x.1
    · simp only [ha, true_and, if_true]
      rw [sum_ite_eq']
      simp [g_lt hd hk j x.1 x.2 ha]
    · simp [ha]
  rw [card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, hQ, hU,
    sum_congr rfl fun j _ => hP j, add_assoc]

theorem colour_equitable (hd : 2 ≤ d) (hk : 4 * d - 1 ≤ k) :
    IsEquitableColoring (G d k) (colour hd hk) := by
  refine ⟨colour_proper hd hk, fun x => ?_⟩
  rw [class_card_eq hd hk x, card_V (by omega) (by omega)]
  have h3 : 4 * (k + d - 1) / (k + d) = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h4 : (4 * (k + d - 1) + (k + d) - 1) / (k + d) = 4 :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [h3, h4]
  have := x.2
  simp only [Fin.sum_univ_four, allowed]
  norm_num
  split_ifs <;> omega

theorem equitableChromaticNumber_eq (hd : 2 ≤ d) (hk : 4 * d - 1 ≤ k) :
    equitableChromaticNumber (G d k) = k + d := by
  apply le_antisymm (Nat.sInf_le (show k + d ∈ {q | ∃ c : V d k → Fin q,
    IsEquitableColoring (G d k) c} from ⟨_, colour_equitable hd hk⟩))
  refine le_csInf ⟨_, _, colour_equitable hd hk⟩ fun q ⟨c, hc⟩ => ?_
  by_contra h
  exact no_equitable_lt (by omega) hk q (by omega) c hc

/-! ### Main results -/

/-- **Lauri's theorem** (arXiv:2608.14517, Theorem 1.1): for `d ≥ 2` and `k ≥ 4d − 1`, `G_{d,k}`
is a connected block graph with `L(G_{d,k}) = k` and `χ_=(G_{d,k}) = k + d`. -/
theorem lauri_family (hd : 2 ≤ d) (hk : 4 * d - 1 ≤ k) :
    (G d k).Connected ∧ IsBlockGraph (G d k) ∧ L (G d k) = k ∧
      equitableChromaticNumber (G d k) = k + d :=
  ⟨connected (by omega), isBlockGraph (by omega), L_eq (by omega) hk,
    equitableChromaticNumber_eq hd hk⟩

/-- No bound `χ_=(G) ≤ L(G) + C` holds for all connected block graphs. -/
theorem gap_unbounded (C : ℕ) : ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
    G.Connected ∧ IsBlockGraph G ∧ L G + C < equitableChromaticNumber G := by
  obtain ⟨h1, h2, h3, h4⟩ := lauri_family (d := C + 2) (k := 4 * (C + 2) - 1) (by omega) le_rfl
  exact ⟨_, inferInstance, _, h1, h2, by rw [h3, h4]; omega⟩

end OpenProblemsLab.BlockEquitable.Family
