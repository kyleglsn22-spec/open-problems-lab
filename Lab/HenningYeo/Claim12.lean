import Lab.HenningYeo.Claim11e

/-!
# Henning–Yeo Claim 12: `α(H[x]) = 2`

Together with Claim 11 (`α(H[x]) ≤ 2`): every vertex has two non-adjacent neighbours. Otherwise
`N[x]` carries the whole (connected) hypergraph, which then has 7 vertices, 7 edges and a
transversal of size 3, so `17 τ ≤ 51 < 56 = w`.
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

/-- Two vertices lie in a common edge. -/
def Adj (E : Finset (Finset α)) (a b : α) : Prop := ∃ f ∈ E, a ∈ f ∧ b ∈ f

variable {E : Finset (Finset α)}

omit [DecidableEq α] in
lemma Adj.symm {a b : α} (h : Adj E a b) : Adj E b a := by
  obtain ⟨f, hf, ha, hb⟩ := h; exact ⟨f, hf, hb, ha⟩

omit [DecidableEq α] in
lemma adj_comm {a b : α} : Adj E a b ↔ Adj E b a := ⟨Adj.symm, Adj.symm⟩

omit [DecidableEq α] in
lemma adj_of_mem {f : Finset α} (hf : f ∈ E) {a b : α} (ha : a ∈ f) (hb : b ∈ f) : Adj E a b :=
  ⟨f, hf, ha, hb⟩

lemma mem_nbr_of_adj {a b : α} (h : Adj E a b) (hne : b ≠ a) : b ∈ nbr E {a} := by
  obtain ⟨f, hf, ha, hb⟩ := h
  exact MinCex.mem_nbr_of hf ha hb hne

/-- In a linear 3-uniform hypergraph a vertex of degree 3 has exactly six neighbours. -/
lemma card_nbr_six (hL : IsL3 E) {x : α} (hx : deg E x = 3) : (nbr E {x}).card = 6 := by
  have heq : nbr E {x} = (E.filter (x ∈ ·)).biUnion (fun f => f.erase x) := by
    ext v
    rw [mem_nbr_singleton, Finset.mem_biUnion]
    constructor
    · rintro ⟨hvx, f, hf, hxf, hvf⟩
      exact ⟨f, Finset.mem_filter.2 ⟨hf, hxf⟩, Finset.mem_erase.2 ⟨hvx, hvf⟩⟩
    · rintro ⟨f, hf, hv⟩
      obtain ⟨hf, hxf⟩ := Finset.mem_filter.1 hf
      exact ⟨(Finset.mem_erase.1 hv).1, f, hf, hxf, (Finset.mem_erase.1 hv).2⟩
  rw [heq, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (g := fun _ => 2), Finset.sum_const, smul_eq_mul]
    · unfold deg at hx; rw [hx]
    · intro f hf
      obtain ⟨hf, hxf⟩ := Finset.mem_filter.1 hf
      rw [Finset.card_erase_of_mem hxf, hL.card3 f hf]
  · intro f hf g hg hne
    obtain ⟨hf, hxf⟩ := Finset.mem_filter.1 hf
    obtain ⟨hg, hxg⟩ := Finset.mem_filter.1 hg
    exact disjoint_erase_of_ne hL hf hg hxf hxg hne

/-- In a 3-regular 3-uniform hypergraph, `m = n`. -/
lemma card_eq_card_verts (hL : IsL3 E) (hreg : ∀ v ∈ verts E, deg E v = 3) :
    E.card = (verts E).card := by
  have h := sum_deg_eq E (verts E)
  have h2 : ∑ f ∈ E, (f ∩ verts E).card = ∑ _f ∈ E, 3 := Finset.sum_congr rfl
    (fun f hf => by rw [Finset.inter_eq_left.2 (subset_verts hf), hL.card3 f hf])
  rw [Finset.sum_congr rfl hreg, h2] at h
  simp only [Finset.sum_const, smul_eq_mul] at h
  omega

/-- Three distinct edges at a vertex of degree 3 are all its edges. -/
lemma all3 {y : α} (hy : deg E y = 3) {a b c : Finset α} (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E)
    (hya : y ∈ a) (hyb : y ∈ b) (hyc : y ∈ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ f ∈ E, y ∈ f → f = a ∨ f = b ∨ f = c := by
  have hsub : ({a, b, c} : Finset (Finset α)) ⊆ E.filter (y ∈ ·) := by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl <;> exact Finset.mem_filter.2 ⟨by assumption, by assumption⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    unfold deg at hy
    rw [hy, Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc])
  intro f hf hyf
  have : f ∈ ({a, b, c} : Finset (Finset α)) := heq ▸ Finset.mem_filter.2 ⟨hf, hyf⟩
  simpa using this

namespace MinCex

/-- **Claim 11**, for three named vertices. -/
lemma claim11' (h : MinCex E) {x a b c : α} (ha : a ∈ nbr E {x}) (hb : b ∈ nbr E {x})
    (hc : c ∈ nbr E {x}) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (nab : ¬ Adj E a b)
    (nac : ¬ Adj E a c) (nbc : ¬ Adj E b c) : False := by
  refine h.claim11 (x := x) (S := {a, b, c}) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  · rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  · intro f hf
    by_contra hlt
    push Not at hlt
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 hlt
    rw [Finset.mem_inter] at hp hq
    have key : ∀ {p q : α}, p ∈ f → q ∈ f → p ≠ q → p ∈ ({a, b, c} : Finset α) →
        q ∈ ({a, b, c} : Finset α) → False := by
      intro p q hp hq hpq hpS hqS
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpS hqS
      rcases hpS with rfl | rfl | rfl <;> rcases hqS with rfl | rfl | rfl
      all_goals first
        | exact hpq rfl
        | exact nab ⟨f, hf, by assumption, by assumption⟩
        | exact nac ⟨f, hf, by assumption, by assumption⟩
        | exact nbc ⟨f, hf, by assumption, by assumption⟩
    exact key hp.1 hq.1 hpq hp.2 hq.2

/-- **Claim 12**: every vertex has two non-adjacent neighbours. -/
lemma claim12 (h : MinCex E) {x : α} (hx : x ∈ verts E) :
    ∃ a ∈ nbr E {x}, ∃ b ∈ nbr E {x}, a ≠ b ∧ ¬ Adj E a b := by
  by_contra hno
  push Not at hno
  have hL := h.L
  have hreg := h.claim10
  have hx3 := hreg x hx
  set N := insert x (nbr E {x}) with hN
  have hxN : x ∉ nbr E {x} := fun h' => (mem_nbr_singleton.1 h').1 rfl
  have hcN : N.card = 7 := by rw [Finset.card_insert_of_notMem hxN, card_nbr_six hL hx3]
  have hnbrE : ∀ {y}, y ∈ nbr E {x} → y ∈ verts E := fun hy => by
    obtain ⟨-, f, hf, -, hyf⟩ := mem_nbr_singleton.1 hy
    exact subset_verts hf hyf
  have hny : ∀ y ∈ nbr E {x}, nbr E {y} = N.erase y := by
    intro y hy
    have hsub : N.erase y ⊆ nbr E {y} := by
      intro z hz
      obtain ⟨hzy, hzN⟩ := Finset.mem_erase.1 hz
      rcases Finset.mem_insert.1 hzN with rfl | hz'
      · obtain ⟨-, f, hf, hxf, hyf⟩ := mem_nbr_singleton.1 hy
        exact MinCex.mem_nbr_of hf hyf hxf hzy
      · exact mem_nbr_of_adj (hno y hy z hz' (Ne.symm hzy)) hzy
    refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [Finset.card_erase_of_mem (Finset.mem_insert_of_mem hy), hcN]
    have := card_nbr_singleton_le hL.card3 y
    rw [hreg y (hnbrE hy)] at this
    omega
  have hsubN : ∀ f ∈ E, ∀ y ∈ f, y ∈ N → f ⊆ N := by
    intro f hf y hyf hyN c hc
    by_cases hcy : c = y
    · exact hcy ▸ hyN
    have hcn : c ∈ nbr E {y} := MinCex.mem_nbr_of hf hyf hc hcy
    rcases Finset.mem_insert.1 hyN with rfl | hy'
    · exact Finset.mem_insert_of_mem hcn
    · rw [hny y hy'] at hcn; exact Finset.mem_of_mem_erase hcn
  set F := E.filter (· ⊆ N)
  have hcl : IsClosed E F := by
    refine ⟨Finset.filter_subset _ _, fun f hf hmeet => ?_⟩
    obtain ⟨y, hyf, hyF⟩ := Finset.not_disjoint_iff.1 hmeet
    obtain ⟨g, hg, hyg⟩ := mem_verts.1 hyF
    exact Finset.mem_filter.2 ⟨hf, hsubN f hf y hyf ((Finset.mem_filter.1 hg).2 hyg)⟩
  obtain ⟨e₁, he₁⟩ : (E.filter (x ∈ ·)).Nonempty := Finset.card_pos.1 (by unfold deg at hx3; omega)
  obtain ⟨he₁E, hxe₁⟩ := Finset.mem_filter.1 he₁
  have hFE := h.closed_eq hcl ⟨e₁, Finset.mem_filter.2 ⟨he₁E, hsubN e₁ he₁E x hxe₁
    (Finset.mem_insert_self _ _)⟩⟩
  have hallN : ∀ f ∈ E, f ⊆ N := fun f hf => (Finset.mem_filter.1 (hFE ▸ hf : f ∈ F)).2
  obtain ⟨e₂, e₃, he₂, he₃, hx₂, hx₃, h21, h31, h23, hall⟩ := edges_three hx3 he₁E hxe₁
  have hT : IsTransversal E e₁ := by
    intro f hf
    by_contra hd
    rw [Finset.not_nonempty_iff_eq_empty] at hd
    have hxf : x ∉ f := fun h' => by
      have : x ∈ f ∩ e₁ := Finset.mem_inter.2 ⟨h', hxe₁⟩
      rw [hd] at this; exact Finset.notMem_empty x this
    have hsub : f ⊆ (f ∩ e₂) ∪ (f ∩ e₃) := by
      intro c hc
      have hcN := hallN f hf hc
      rcases Finset.mem_insert.1 hcN with rfl | hcn
      · exact absurd hc hxf
      obtain ⟨-, g, hg, hxg, hcg⟩ := mem_nbr_singleton.1 hcn
      rcases hall g hg hxg with rfl | rfl | rfl
      · have : c ∈ f ∩ g := Finset.mem_inter.2 ⟨hc, hcg⟩
        rw [hd] at this; exact absurd this (Finset.notMem_empty c)
      · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hc, hcg⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hc, hcg⟩)
    have h2 := hL.linear f hf e₂ he₂ (fun h' => hxf (h' ▸ hx₂))
    have h3 := hL.linear f hf e₃ he₃ (fun h' => hxf (h' ▸ hx₃))
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [hL.card3 f hf] at this
    omega
  have hV : 7 ≤ (verts E).card := by
    rw [← hcN]
    refine Finset.card_le_card fun v hv => ?_
    rcases Finset.mem_insert.1 hv with rfl | hv'
    · exact hx
    · exact hnbrE hv'
  have hm := card_eq_card_verts hL hreg
  apply h.not_good
  refine ⟨e₁, hT, ?_⟩
  rw [h.wt_eq, hL.card3 e₁ he₁E]
  omega

end MinCex

end OpenProblemsLab.HY
