import Lab.HenningYeo.Claim11d

/-!
# Henning–Yeo Claim 11

**Claim 11**: in a minimal counterexample no vertex has three pairwise non-adjacent neighbours
(`α(H[x]) ≤ 2`).
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

lemma disjoint_erase_of_ne {E : Finset (Finset α)} (hL : IsL3 E) {s : α} {g g' : Finset α}
    (hg : g ∈ E) (hg' : g' ∈ E) (hsg : s ∈ g) (hsg' : s ∈ g') (hne : g ≠ g') :
    Disjoint (g.erase s) (g'.erase s) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨hvs, hvg⟩ := Finset.mem_erase.1 hv
  exact hne (hL.eq_of_two hg hg' hvs hvg hsg (Finset.mem_erase.1 hv').2 hsg')

namespace C11

variable {E : Finset (Finset α)} {x : α} {S e₁ e₂ : Finset α}
variable (C : C11 E x S e₁ e₂)
include C

/-- The last step of Claim 11. -/
lemma final {s q : α} (hs : s ∈ S)
    (huniq : ∀ s' ∈ S, s' ≠ s → ∀ q' ∈ Q11 E S e₁ e₂, q' ∉ nbr E {s'})
    (hq : q ∈ Q11 E S e₁ e₂) (hqs : q ∈ nbr E {s}) : False := by
  have hL := C.h.L
  obtain ⟨hqs', fq, hfq, hsfq, hqfq⟩ := mem_nbr_singleton.1 hqs
  obtain ⟨f₂, f₃, hf2, hf3, hs2, hs3, h2q, h3q, h23, hall⟩ := edges_three (C.deg_s hs) hfq hsfq
  set Q := Q11 E S e₁ e₂
  have hc2 : ∀ g ∈ E, s ∈ g → ((g.erase s) ∩ Q).card ≤ 2 := fun g hg hsg => by
    have := Finset.card_le_card (Finset.inter_subset_left (s₁ := g.erase s) (s₂ := Q))
    rw [Finset.card_erase_of_mem hsg, hL.card3 g hg] at this
    omega
  have hsum : ((fq.erase s) ∩ Q).card + ((f₂.erase s) ∩ Q).card + ((f₃.erase s) ∩ Q).card ≤ 3 := by
    have d12 : Disjoint (fq.erase s ∩ Q) (f₂.erase s ∩ Q) := Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left
        (disjoint_erase_of_ne hL hfq hf2 hsfq hs2 (Ne.symm h2q)))
    have d13 : Disjoint (fq.erase s ∩ Q) (f₃.erase s ∩ Q) := Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left
        (disjoint_erase_of_ne hL hfq hf3 hsfq hs3 (Ne.symm h3q)))
    have d23 : Disjoint (f₂.erase s ∩ Q) (f₃.erase s ∩ Q) := Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left
        (disjoint_erase_of_ne hL hf2 hf3 hs2 hs3 h23))
    have hsub : (fq.erase s ∩ Q ∪ f₂.erase s ∩ Q) ∪ f₃.erase s ∩ Q ⊆ Q :=
      Finset.union_subset (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right)
        Finset.inter_subset_right
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨d13, d23⟩),
      Finset.card_union_of_disjoint d12] at this
    have : Q.card ≤ 3 := C.card_Q
    omega
  have hq1 : 1 ≤ ((fq.erase s) ∩ Q).card :=
    Finset.card_pos.2 ⟨q, Finset.mem_inter.2 ⟨Finset.mem_erase.2 ⟨hqs', hqfq⟩, hq⟩⟩
  have hb1 := hc2 fq hfq hsfq
  have hb2 := hc2 f₂ hf2 hs2
  have hb3 := hc2 f₃ hf3 hs3
  have hpickQ : ∀ g : Finset α, 1 ≤ ((g.erase s) ∩ Q).card → ∃ q' ∈ g, q' ∈ Q := fun g hg => by
    obtain ⟨q', hq'⟩ := Finset.card_pos.1 hg
    exact ⟨q', (Finset.mem_erase.1 (Finset.mem_inter.1 hq').1).2, (Finset.mem_inter.1 hq').2⟩
  rcases (show (1 ≤ ((fq.erase s) ∩ Q).card ∧ ((f₂.erase s) ∩ Q).card ≤ 1 ∧
      ((f₃.erase s) ∩ Q).card ≤ 1) ∨ (1 ≤ ((f₂.erase s) ∩ Q).card ∧
      ((fq.erase s) ∩ Q).card ≤ 1 ∧ ((f₃.erase s) ∩ Q).card ≤ 1) ∨
      (1 ≤ ((f₃.erase s) ∩ Q).card ∧ ((fq.erase s) ∩ Q).card ≤ 1 ∧
      ((f₂.erase s) ∩ Q).card ≤ 1) by omega) with ⟨hD, hA, hB⟩ | ⟨hD, hA, hB⟩ | ⟨hD, hA, hB⟩
  · obtain ⟨a₁, ha₁, ha₁s, ha₁R⟩ := C.exists_R hs hf2 hs2 hA
    obtain ⟨a₂, ha₂, ha₂s, ha₂R⟩ := C.exists_R hs hf3 hs3 hB
    obtain ⟨q', hq'D, hq'Q⟩ := hpickQ fq hD
    refine C.final_core hs huniq hf2 hf3 hs2 hs3 h23 (D := fq) (fun g hg hsg => ?_) ha₁ ha₁s ha₁R
      ha₂ ha₂s ha₂R hq'D hq'Q
    rcases hall g hg hsg with h' | h' | h'
    · exact Or.inr (Or.inr h')
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · obtain ⟨a₁, ha₁, ha₁s, ha₁R⟩ := C.exists_R hs hfq hsfq hA
    obtain ⟨a₂, ha₂, ha₂s, ha₂R⟩ := C.exists_R hs hf3 hs3 hB
    obtain ⟨q', hq'D, hq'Q⟩ := hpickQ f₂ hD
    refine C.final_core hs huniq hfq hf3 hsfq hs3 (Ne.symm h3q) (D := f₂) (fun g hg hsg => ?_)
      ha₁ ha₁s ha₁R ha₂ ha₂s ha₂R hq'D hq'Q
    rcases hall g hg hsg with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')
    · exact Or.inr (Or.inl h')
  · obtain ⟨a₁, ha₁, ha₁s, ha₁R⟩ := C.exists_R hs hfq hsfq hA
    obtain ⟨a₂, ha₂, ha₂s, ha₂R⟩ := C.exists_R hs hf2 hs2 hB
    obtain ⟨q', hq'D, hq'Q⟩ := hpickQ f₃ hD
    refine C.final_core hs huniq hfq hf2 hsfq hs2 (Ne.symm h2q) (D := f₃) (fun g hg hsg => ?_)
      ha₁ ha₁s ha₁R ha₂ ha₂s ha₂R hq'D hq'Q
    rcases hall g hg hsg with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')

lemma false : False := by
  have hpos : 0 < ∑ v ∈ Q11 E S e₁ e₂, deg (hit E S) v := by rw [C.sum_Q]; omega
  obtain ⟨q, hq, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.pos_iff_ne_zero.1 hpos)
  obtain ⟨g, hg⟩ := Finset.card_pos.1 (mem_Q.1 hq).2.2
  obtain ⟨hgS, hqg⟩ := Finset.mem_filter.1 hg
  obtain ⟨hgE, hgd⟩ := mem_hit.1 hgS
  obtain ⟨y, hyg, hyS⟩ := Finset.not_disjoint_iff.1 hgd
  have hqy : q ≠ y := fun h' => C.S_gone hyS (h' ▸ (mem_Q.1 hq).1)
  have hqn : q ∈ nbr E {y} := MinCex.mem_nbr_of hgE hyg hqg hqy
  by_cases huniq : ∀ s' ∈ S, s' ≠ y → ∀ q' ∈ Q11 E S e₁ e₂, q' ∉ nbr E {s'}
  · exact C.final hyS huniq hq hqn
  · push Not at huniq
    obtain ⟨s', hs', hs'y, q', hq', hq'n⟩ := huniq
    exact C.claim113 hyS hs' (Ne.symm hs'y) hq hq' hqn hq'n

end C11

namespace MinCex

variable {E : Finset (Finset α)}

/-- **Claim 11**: no vertex has three pairwise non-adjacent neighbours. -/
lemma claim11 (h : MinCex E) {x : α} {S : Finset α} (hS : S ⊆ nbr E {x}) (hcard : S.card = 3)
    (hind : ∀ f ∈ E, (f ∩ S).card ≤ 1) : False := by
  obtain ⟨e₁, e₂, C⟩ := C11.exists h h.claim10 hS hcard hind
  exact C.false

end MinCex

end OpenProblemsLab.HY
