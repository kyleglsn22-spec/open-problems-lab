import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Large matchings in cubic graphs

We prove that a graph in which every vertex has degree 3 has a matching covering all but at
most `2 ⌊|V|/15⌋` vertices (from Tutte's theorem, via the Tutte–Berge deficiency trick and a
count of odd components). This is what Henning–Yeo use (as Lemma 1) for 2-regular hypergraphs.
-/

namespace OpenProblemsLab.HY.Cubic

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The vertices of a connected component, as a finset. -/
noncomputable def cx (L : SimpleGraph X) (c : L.ConnectedComponent) : Finset X :=
  by classical exact univ.filter (fun x => L.connectedComponentMk x = c)

omit [DecidableEq X] in
lemma mem_cx {L : SimpleGraph X} {c : L.ConnectedComponent} {x : X} :
    x ∈ cx L c ↔ L.connectedComponentMk x = c := by
  classical simp [cx]

omit [DecidableEq X] in
lemma card_cx (L : SimpleGraph X) (c : L.ConnectedComponent) : (cx L c).card = c.supp.ncard := by
  classical
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x; simp [mem_cx, SimpleGraph.ConnectedComponent.mem_supp_iff]

/-- Per component: if every vertex has degree 3 counting `b x` extra half-edges, an odd component
`C` with `B = ∑_{x∈C} b x` satisfies `15 ≤ 5 B + 2 |C|`. -/
lemma comp_bound (L : SimpleGraph X) [DecidableRel L.Adj] [L.LocallyFinite] (b : X → ℕ)
    (hdeg : ∀ x, L.degree x + b x = 3) (c : L.ConnectedComponent) (hodd : Odd (cx L c).card) :
    15 ≤ 5 * ∑ x ∈ cx L c, b x + 2 * (cx L c).card := by
  set C := cx L c with hC
  set P := (C ×ˢ C).filter (fun p => L.Adj p.1 p.2) with hP
  -- neighbours of a vertex of `C` lie in `C`
  have hnb : ∀ x ∈ C, L.degree x = (C.filter (L.Adj x)).card := by
    intro x hx
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext y
    simp only [SimpleGraph.mem_neighborFinset, mem_filter]
    constructor
    · intro hxy
      refine ⟨?_, hxy⟩
      rw [hC, mem_cx] at hx ⊢
      rw [← hx]
      exact (SimpleGraph.ConnectedComponent.eq.2 hxy.reachable).symm
    · exact fun h => h.2
  have hPsum : P.card = ∑ x ∈ C, L.degree x := by
    rw [hP, card_filter, sum_product]
    refine sum_congr rfl fun x hx => ?_
    rw [hnb x hx, card_filter]
  -- `P` has even size
  let Lc : SimpleGraph X :=
    { Adj := fun x y => L.Adj x y ∧ x ∈ C ∧ y ∈ C
      symm := ⟨fun x y h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun x h => h.1.ne rfl⟩ }
  classical
  have hPe : Even P.card := by
    have := Lc.two_mul_card_edgeFinset
    have hPeq : P = univ.filter (fun p : X × X => Lc.Adj p.1 p.2) := by
      ext ⟨x, y⟩; simp [hP, Lc]; tauto
    rw [hPeq, show (univ.filter fun p : X × X => Lc.Adj p.1 p.2) =
      univ.filter (fun (x, y) => Lc.Adj x y) from rfl, ← this]
    exact even_two_mul _
  have hPle : P.card ≤ C.card * C.card - C.card := by
    have : P ⊆ C.offDiag := by
      intro p hp
      rw [hP, mem_filter, mem_product] at hp
      exact mem_offDiag.2 ⟨hp.1.1, hp.1.2, hp.2.ne⟩
    have := card_le_card this
    rwa [offDiag_card] at this
  have hsum : P.card + ∑ x ∈ C, b x = 3 * C.card := by
    rw [hPsum, ← sum_add_distrib, sum_congr rfl fun x _ => hdeg x, sum_const, smul_eq_mul,
      mul_comm]
  set B := ∑ x ∈ C, b x
  by_contra hlt
  push Not at hlt
  have hB : B ≤ 2 := by omega
  have hc : C.card ≤ 4 := by
    rcases Nat.even_or_odd B with hBe | hBo
    · exfalso
      obtain ⟨k, hk⟩ := hPe; obtain ⟨j, hj⟩ := hBe; obtain ⟨i, hi⟩ := hodd
      omega
    · obtain ⟨j, hj⟩ := hBo
      omega
  obtain ⟨i, hi⟩ := hodd
  have : C.card = 1 ∨ C.card = 3 := by omega
  rcases this with h1 | h3
  · rw [h1] at hPle hsum; omega
  · rw [h3] at hPle hsum
    rcases Nat.even_or_odd B with hBe | hBo
    · obtain ⟨k, hk⟩ := hPe; obtain ⟨j, hj⟩ := hBe; omega
    · omega

/-- Summing `comp_bound` over the odd components. -/
lemma odd_bound (L : SimpleGraph X) [DecidableRel L.Adj] [L.LocallyFinite] (b : X → ℕ)
    (hdeg : ∀ x, L.degree x + b x = 3) :
    15 * L.oddComponents.ncard ≤ 5 * ∑ x, b x + 2 * Fintype.card X := by
  classical
  have hodd : L.oddComponents.ncard = (univ.filter (fun c => Odd (cx L c).card)).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext c; simp [card_cx]
  have hpart : ∀ f : X → ℕ, ∑ c : L.ConnectedComponent, ∑ x ∈ cx L c, f x = ∑ x, f x := by
    intro f
    have := Finset.sum_fiberwise (s := (univ : Finset X)) (g := L.connectedComponentMk) f
    rw [← this]
    refine sum_congr rfl fun c _ => sum_congr ?_ fun _ _ => rfl
    ext x; simp [mem_cx]
  rw [hodd, mul_comm, ← smul_eq_mul, ← sum_const]
  calc ∑ _c ∈ univ.filter (fun c => Odd (cx L c).card), 15
      ≤ ∑ c ∈ univ.filter (fun c => Odd (cx L c).card),
          (5 * ∑ x ∈ cx L c, b x + 2 * (cx L c).card) :=
        sum_le_sum fun c hc => comp_bound L b hdeg c (mem_filter.1 hc).2
    _ ≤ ∑ c, (5 * ∑ x ∈ cx L c, b x + 2 * (cx L c).card) :=
        sum_le_sum_of_subset (filter_subset _ _)
    _ = 5 * ∑ x, b x + 2 * Fintype.card X := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, hpart b]
        congr 2
        rw [← card_univ, card_eq_sum_ones, ← hpart (fun _ => 1)]
        simp

section Main

variable {W : Type*}

/-- Adjacency of `K` plus `d` universal vertices. -/
def adjU (K : SimpleGraph W) (d : ℕ) : W ⊕ Fin d → W ⊕ Fin d → Prop
  | .inl a, .inl b => K.Adj a b
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | .inr i, .inr j => i ≠ j

/-- `K` plus `d` universal vertices. -/
def withU (K : SimpleGraph W) (d : ℕ) : SimpleGraph (W ⊕ Fin d) where
  Adj := adjU K d
  symm := ⟨fun p q h => by
    rcases p with a | i <;> rcases q with b | j <;> simp_all [adjU, K.adj_comm, eq_comm]⟩
  loopless := ⟨fun p h => by rcases p with a | i <;> simp_all [adjU]⟩

@[simp] lemma withU_inl_inl {K : SimpleGraph W} {d : ℕ} {a b : W} :
    (withU K d).Adj (.inl a) (.inl b) ↔ K.Adj a b := Iff.rfl
@[simp] lemma withU_inl_inr {K : SimpleGraph W} {d : ℕ} {a : W} {i : Fin d} :
    (withU K d).Adj (.inl a) (.inr i) := trivial
@[simp] lemma withU_inr_inl {K : SimpleGraph W} {d : ℕ} {a : W} {i : Fin d} :
    (withU K d).Adj (.inr i) (.inl a) := trivial
@[simp] lemma withU_inr_inr {K : SimpleGraph W} {d : ℕ} {i j : Fin d} :
    (withU K d).Adj (.inr i) (.inr j) ↔ i ≠ j := Iff.rfl

/-- **Matchings in cubic graphs**: a graph with all degrees 3 has a matching missing at most
`2 ⌊|V|/15⌋` vertices. -/
theorem cubic_matching [Fintype W] [DecidableEq W] (K : SimpleGraph W) [DecidableRel K.Adj] (h3 : ∀ w, K.degree w = 3) :
    ∃ M : K.Subgraph, M.IsMatching ∧ Fintype.card W ≤ M.verts.ncard + 2 * (Fintype.card W / 15) := by
  classical
  set n := Fintype.card W with hn
  set d := 2 * (n / 15) with hd
  have hneven : Even n := by
    have := K.sum_degrees_eq_twice_card_edges
    simp only [h3, sum_const, card_univ, smul_eq_mul] at this
    rw [← hn] at this
    rw [Nat.even_iff]; omega
  set G' := withU K d with hG'
  -- no Tutte violator
  have hnoviol : ∀ u : Set (W ⊕ Fin d), ¬ G'.IsTutteViolator u := by
    intro u hviol
    unfold SimpleGraph.IsTutteViolator at hviol
    set L := ((⊤ : G'.Subgraph).deleteVerts u).coe with hL
    by_cases hall : ∀ i : Fin d, Sum.inr i ∈ u
    · -- Case B: all universal vertices deleted
      have hex : ∀ x : ((⊤ : G'.Subgraph).deleteVerts u).verts, ∃ a, x.1 = Sum.inl a := by
        rintro ⟨x | i, hx⟩
        · exact ⟨x, rfl⟩
        · exact absurd (hall i) (by simpa using hx)
      choose pj hpj using hex
      set S : Finset W := univ.filter (fun w => Sum.inl w ∈ u) with hS
      have hmemv : ∀ {a : W}, a ∉ S → Sum.inl a ∈ ((⊤ : G'.Subgraph).deleteVerts u).verts :=
        fun ha => Set.mem_sdiff_of_mem (Set.mem_univ _) (fun h' => ha (mem_filter.2 ⟨mem_univ _, h'⟩))
      have hpjS : ∀ x, pj x ∉ S := fun x hx =>
        (x.2 : x.1 ∈ Set.univ \ u).2 (by rw [hpj x]; exact (mem_filter.1 hx).2)
      set b : ((⊤ : G'.Subgraph).deleteVerts u).verts → ℕ :=
        fun x => (S.filter (fun s => K.Adj (pj x) s)).card with hb
      have hLdeg : ∀ x, L.degree x + b x = 3 := by
        intro x
        rw [← h3 (pj x), ← SimpleGraph.card_neighborFinset_eq_degree,
          ← SimpleGraph.card_neighborFinset_eq_degree]
        have : (K.neighborFinset (pj x)) = (K.neighborFinset (pj x)).filter (· ∉ S) ∪
            S.filter (fun s => K.Adj (pj x) s) := by
          ext y; by_cases hy : y ∈ S <;> simp [hy]
        rw [this, card_union_of_disjoint (by
          rw [disjoint_left]; intro y hy hy'; simp at hy hy'; tauto)]
        congr 1
        refine card_bij (fun y _ => pj y) ?_ ?_ ?_
        · intro y hy
          simp only [SimpleGraph.mem_neighborFinset, mem_filter] at hy ⊢
          refine ⟨?_, hpjS y⟩
          have : G'.Adj x.1 y.1 := SimpleGraph.Subgraph.coe_adj_sub _ _ _ hy
          rwa [hpj x, hpj y] at this
        · intro y _ y' _ h'
          exact Subtype.ext (by rw [hpj y, hpj y', h'])
        · intro a ha
          simp only [SimpleGraph.mem_neighborFinset, mem_filter] at ha
          refine ⟨⟨Sum.inl a, hmemv ha.2⟩, ?_, ?_⟩
          · simp only [SimpleGraph.mem_neighborFinset, hL, SimpleGraph.Subgraph.coe_adj,
              SimpleGraph.Subgraph.deleteVerts_adj, SimpleGraph.Subgraph.top_adj]
            refine ⟨trivial, (Set.mem_sdiff _).1 x.2 |>.2, trivial, (Set.mem_sdiff _).1 (hmemv ha.2) |>.2, ?_⟩
            rw [hpj x]; exact ha.1
          · have := hpj ⟨Sum.inl a, hmemv ha.2⟩
            exact (Sum.inl_injective this).symm
      have hbsum : ∑ x, b x ≤ 3 * S.card := by
        have : ∑ x, b x = ∑ s ∈ S, (univ.filter (fun x => K.Adj (pj x) s)).card := by
          simp only [hb, card_filter]
          rw [sum_comm]
        rw [this, mul_comm, ← smul_eq_mul, ← sum_const]
        refine sum_le_sum fun s _ => ?_
        rw [← h3 s, ← SimpleGraph.card_neighborFinset_eq_degree]
        refine card_le_card_of_injOn pj (fun x hx => ?_) (fun x _ y _ h' => ?_)
        · simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hx
          simpa [SimpleGraph.mem_neighborFinset] using hx.symm
        · exact Subtype.ext (by rw [hpj x, hpj y, h'])
      have hob := odd_bound L b hLdeg
      have hcardX : Fintype.card ((⊤ : G'.Subgraph).deleteVerts u).verts + S.card = n := by
        let e : ((⊤ : G'.Subgraph).deleteVerts u).verts ≃ {a : W // a ∉ S} :=
          { toFun := fun x => ⟨pj x, hpjS x⟩
            invFun := fun a => ⟨Sum.inl a.1, hmemv a.2⟩
            left_inv := fun x => Subtype.ext (hpj x).symm
            right_inv := fun a => Subtype.ext (by
              have := hpj ⟨Sum.inl a.1, hmemv a.2⟩
              exact (Sum.inl_injective this).symm) }
        rw [Fintype.card_congr e, Fintype.card_subtype]
        have := card_filter_add_card_filter_not (s := (univ : Finset W)) (fun a => a ∈ S)
        rw [filter_mem_eq_inter, univ_inter, card_univ, ← hn] at this
        omega
      have hpar := L.odd_ncard_oddComponents
      have hun : u.ncard = S.card + d := by
        have : u = ↑(S.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
            (univ : Finset (Fin d)).map ⟨Sum.inr, Sum.inr_injective⟩) := by
          ext x
          rcases x with a | i
          · simp [hS]
          · simp [hall i]
        rw [this, Set.ncard_coe_finset, card_union_of_disjoint, card_map, card_map, card_univ,
          Fintype.card_fin]
        rw [disjoint_left]; intro x hx hx'; simp at hx hx'; obtain ⟨a, -, rfl⟩ := hx; simp at hx'
      rw [Nat.card_eq_fintype_card] at hpar
      rw [hun] at hviol
      set O := L.oddComponents.ncard
      have hp : O % 2 = (n - S.card) % 2 := by
        rcases Nat.even_or_odd O with h | h
        · have : ¬ Odd (Fintype.card ((⊤ : G'.Subgraph).deleteVerts u).verts) :=
            fun h' => Nat.not_odd_iff_even.2 h (hpar.2 h')
          rw [Nat.not_odd_iff_even] at this
          rw [Nat.even_iff] at h this; omega
        · have := hpar.1 h
          rw [Nat.odd_iff] at h this; omega
      rw [Nat.even_iff] at hneven
      omega
    · -- Case A: some universal vertex survives
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      have hz : Sum.inr i ∈ ((⊤ : G'.Subgraph).deleteVerts u).verts :=
        Set.mem_sdiff_of_mem (Set.mem_univ _) hi
      set z : ((⊤ : G'.Subgraph).deleteVerts u).verts := ⟨Sum.inr i, hz⟩
      have hreach : ∀ x, L.Reachable x z := by
        intro x
        by_cases hxz : x = z
        · rw [hxz]
        refine SimpleGraph.Adj.reachable ?_
        show ((⊤ : G'.Subgraph).deleteVerts u).Adj x.1 z.1
        rw [SimpleGraph.Subgraph.deleteVerts_adj]
        refine ⟨trivial, x.2.2, trivial, hi, ?_⟩
        rw [SimpleGraph.Subgraph.top_adj]
        rcases hx : x.1 with a | j
        · exact trivial
        · show j ≠ i
          rintro rfl
          exact hxz (Subtype.ext hx)
      have hle : L.oddComponents.ncard ≤ 1 := by
        refine (Set.ncard_le_one (Set.toFinite _)).2 fun c _ c' _ => ?_
        induction c using SimpleGraph.ConnectedComponent.ind with | h x => ?_
        induction c' using SimpleGraph.ConnectedComponent.ind with | h y => ?_
        exact SimpleGraph.ConnectedComponent.eq.2 ((hreach x).trans (hreach y).symm)
      by_cases hu : u = ∅
      · subst hu
        have hpar := L.odd_ncard_oddComponents
        have hcard : Nat.card ((⊤ : G'.Subgraph).deleteVerts (∅ : Set (W ⊕ Fin d))).verts = n + d := by
          rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.sdiff_empty,
            SimpleGraph.Subgraph.verts_top, Nat.card_univ, Nat.card_eq_fintype_card,
            Fintype.card_sum, Fintype.card_fin]
        rw [hcard] at hpar
        simp only [Set.ncard_empty] at hviol
        have h1 : L.oddComponents.ncard = 1 := by omega
        rw [h1] at hpar
        have := hpar.1 odd_one
        rw [Nat.odd_iff] at this; rw [Nat.even_iff] at hneven
        omega
      · have : 0 < u.ncard := (Set.ncard_pos (Set.toFinite u)).2 (Set.nonempty_iff_ne_empty.2 hu)
        omega
  obtain ⟨M', hM'⟩ := (SimpleGraph.tutte (G := G')).2 hnoviol
  have hM'u := SimpleGraph.Subgraph.isPerfectMatching_iff.1 hM'
  let M : K.Subgraph :=
    { verts := {a | ∃ b, M'.Adj (Sum.inl a) (Sum.inl b)}
      Adj := fun a b => M'.Adj (Sum.inl a) (Sum.inl b)
      adj_sub := fun h => M'.adj_sub h
      edge_vert := fun h => ⟨_, h⟩
      symm := ⟨fun _ _ h => M'.adj_symm h⟩ }
  refine ⟨M, fun a ⟨b, hb⟩ => ⟨b, hb, fun w hw => ?_⟩, ?_⟩
  · exact Sum.inl_injective (hM'.1.eq_of_adj_left hw hb)
  · choose p hp using fun v => (hM'u v).exists
    set T := univ.filter (fun a => a ∉ M.verts) with hT
    have hTc : T.card ≤ d := by
      have := card_le_card_of_injOn (s := T)
        (t := (univ : Finset (Fin d)).map ⟨Sum.inr, Sum.inr_injective⟩)
        (fun a => p (Sum.inl a)) ?_ ?_
      · rwa [card_map, card_univ, Fintype.card_fin] at this
      · intro a ha
        simp only [hT, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha
        simp only [coe_map, Function.Embedding.coeFn_mk, coe_univ, Set.image_univ,
          Set.mem_range]
        rcases hpa : p (Sum.inl a) with b | j
        · exact absurd ⟨b, hpa ▸ hp (Sum.inl a)⟩ ha
        · exact ⟨j, rfl⟩
      · intro a _ a' _ h'
        exact Sum.inl_injective (hM'.1.eq_of_adj_right (hp _) (by
          rw [show p (Sum.inl a) = p (Sum.inl a') from h']; exact hp _))
    have hv : M.verts.ncard = (univ.filter (fun a => a ∈ M.verts)).card := by
      rw [← Set.ncard_coe_finset]; congr 1; ext; simp
    have := card_filter_add_card_filter_not (s := (univ : Finset W)) (fun a => a ∈ M.verts)
    rw [card_univ, ← hn] at this
    have hTeq : T.card = #(univ.filter fun a => ¬ a ∈ M.verts) := by
      rw [hT]
    rw [hv]
    omega

end Main

end OpenProblemsLab.HY.Cubic
