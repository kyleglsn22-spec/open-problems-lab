import Lab.HenningYeo.Claim12

/-!
# Henning–Yeo Claims 13 and 14

**Claim 13**: if deleting three vertices `S` removes at least 8 edges, at most one further vertex
loses all its edges. **Claim 14**: for non-adjacent `s₁, s₂`, `H - {s₁, s₂}` has no edge whose
degrees are `(1, 1, ≥ 2)`.
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

lemma ne_of_card3 {a b c : α} (h : ({a, b, c} : Finset α).card = 3) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨fun hab => ?_, fun hac => ?_, fun hbc => ?_⟩
  · subst hab
    rw [Finset.insert_eq_of_mem (Finset.mem_insert_self _ _)] at h
    have := Finset.card_le_two (a := a) (b := c); omega
  · subst hac
    rw [Finset.insert_eq_of_mem (by simp)] at h
    have := Finset.card_le_two (a := b) (b := a); omega
  · subst hbc
    rw [Finset.pair_eq_singleton] at h
    have := Finset.card_le_two (a := a) (b := b); omega

variable {E : Finset (Finset α)}

lemma card_hit_le (hreg : ∀ v ∈ verts E, deg E v = 3) {S : Finset α}
    (hSE : S ⊆ verts E) : (hit E S).card ≤ ∑ f ∈ hit E S, (f ∩ S).card ∧
      ∑ f ∈ hit E S, (f ∩ S).card ≤ 3 * S.card := by
  constructor
  · rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun f hf =>
      Finset.card_pos.2 (Finset.not_disjoint_iff_nonempty_inter.1 (mem_hit.1 hf).2)
  · calc ∑ f ∈ hit E S, (f ∩ S).card ≤ ∑ f ∈ E, (f ∩ S).card :=
          Finset.sum_le_sum_of_subset (fun f hf => (mem_hit.1 hf).1)
      _ = ∑ s ∈ S, deg E s := (sum_deg_eq E S).symm
      _ = 3 * S.card := by
          rw [Finset.sum_congr rfl (fun s hs => hreg s (hSE hs)), Finset.sum_const, smul_eq_mul,
            mul_comm]

/-- Eight edges are lost when `c` is adjacent to neither `a` nor `b`. -/
lemma hit8 (hL : IsL3 E) (hreg : ∀ v ∈ verts E, deg E v = 3) {a b c : α} (ha : a ∈ verts E)
    (hb : b ∈ verts E) (hc : c ∈ verts E) (hab : a ≠ b) (nac : ¬ Adj E a c)
    (nbc : ¬ Adj E b c) : 8 ≤ (hit E {a, b, c}).card := by
  set Fa := E.filter (a ∈ ·)
  set Fb := E.filter (b ∈ ·)
  set Fc := E.filter (c ∈ ·)
  have hsub : Fa ∪ Fb ∪ Fc ⊆ hit E {a, b, c} := by
    intro f hf
    simp only [Fa, Fb, Fc, Finset.mem_union, Finset.mem_filter] at hf
    refine mem_hit.2 ⟨by tauto, Finset.not_disjoint_iff.2 ?_⟩
    rcases hf with (h' | h') | h'
    · exact ⟨a, h'.2, by simp⟩
    · exact ⟨b, h'.2, by simp⟩
    · exact ⟨c, h'.2, by simp⟩
  have hi : (Fa ∩ Fb).card ≤ 1 := by
    refine (Finset.card_le_card fun f hf => ?_).trans (card_le_one_two hL hab)
    simp only [Fa, Fb, Finset.mem_inter, Finset.mem_filter] at hf ⊢
    exact ⟨hf.1.1, hf.1.2, hf.2.2⟩
  have hd : Disjoint (Fa ∪ Fb) Fc := by
    rw [Finset.disjoint_left]
    intro f hf hfc
    simp only [Fa, Fb, Fc, Finset.mem_union, Finset.mem_filter] at hf hfc
    rcases hf with h' | h'
    · exact nac ⟨f, h'.1, h'.2, hfc.2⟩
    · exact nbc ⟨f, h'.1, h'.2, hfc.2⟩
  have e1 := Finset.card_union_add_card_inter Fa Fb
  have hFa : Fa.card = 3 := hreg a ha
  have hFb : Fb.card = 3 := hreg b hb
  have hFc : Fc.card = 3 := hreg c hc
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd] at this
  omega

namespace MinCex

/-- **Claim 13**. -/
lemma claim13 (h : MinCex E) {S : Finset α} (hcard : S.card = 3) (hSE : S ⊆ verts E)
    (h8 : 8 ≤ (hit E S).card) {u₁ u₂ : α} (hne : u₁ ≠ u₂) (h1S : u₁ ∉ S) (h2S : u₂ ∉ S)
    (h1E : u₁ ∈ verts E) (h2E : u₂ ∈ verts E) (h1 : ∀ f ∈ E, u₁ ∈ f → ¬ Disjoint f S)
    (h2 : ∀ f ∈ E, u₂ ∈ f → ¬ Disjoint f S) : False := by
  have hL := h.L
  have hreg := h.claim10
  obtain ⟨hA, hB⟩ := card_hit_le hreg hSE
  rw [hcard] at hB
  by_cases h9 : (hit E S).card = 9
  · -- `S` is independent, and `S ⊆ N(u₁)`
    have hind : ∀ f ∈ E, (f ∩ S).card ≤ 1 := by
      intro f hf
      by_contra hlt
      push Not at hlt
      have hfh : f ∈ hit E S := mem_hit.2 ⟨hf, fun hd => by
        rw [Finset.disjoint_iff_inter_eq_empty] at hd; rw [hd] at hlt; simp at hlt⟩
      have := Finset.add_sum_erase (hit E S) (fun g => (g ∩ S).card) hfh
      have h' : (hit E S).card - 1 ≤ ∑ g ∈ (hit E S).erase f, (g ∩ S).card := by
        rw [← Finset.card_erase_of_mem hfh, Finset.card_eq_sum_ones]
        exact Finset.sum_le_sum fun g hg => Finset.card_pos.2
          (Finset.not_disjoint_iff_nonempty_inter.1 (mem_hit.1 (Finset.mem_of_mem_erase hg)).2)
      omega
    have hpick : ∀ g ∈ E.filter (u₁ ∈ ·), ∃ s, s ∈ S ∧ s ∈ g := fun g hg => by
      obtain ⟨s, hsg, hsS⟩ := Finset.not_disjoint_iff.1
        (h1 g (Finset.mem_filter.1 hg).1 (Finset.mem_filter.1 hg).2)
      exact ⟨s, hsS, hsg⟩
    have : Nonempty α := ⟨u₁⟩
    choose! φ hφS hφg using hpick
    have hinj : Set.InjOn φ ((E.filter (u₁ ∈ ·) : Finset (Finset α)) : Set (Finset α)) := by
      intro g hg g' hg' heq
      have hu : u₁ ≠ φ g := fun h' => h1S (h' ▸ hφS g hg)
      exact hL.eq_of_two (Finset.mem_filter.1 hg).1 (Finset.mem_filter.1 hg').1 hu
        (Finset.mem_filter.1 hg).2 (hφg g hg) (Finset.mem_filter.1 hg').2 (heq ▸ hφg g' hg')
    have himg : (E.filter (u₁ ∈ ·)).image φ = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro s hs; obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hs; exact hφS g hg
      · rw [Finset.card_image_of_injOn hinj, hcard]
        have := hreg u₁ h1E; unfold deg at this; omega
    refine h.claim11 (x := u₁) (S := S) (fun s hs => ?_) hcard hind
    rw [← himg] at hs
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hs
    exact MinCex.mem_nbr_of (Finset.mem_filter.1 hg).1 (Finset.mem_filter.1 hg).2 (hφg g hg)
      (fun h' => h1S (h' ▸ hφS g hg))
  · -- a good reduction
    have h8' : (hit E S).card = 8 := by omega
    have hbal := sum_deg_hit hL hreg S
    have h6 := six_hE_le hL hreg S
    have hsub : insert u₁ (insert u₂ S) ⊆ verts E \ verts (del E S) := by
      intro v hv
      simp only [Finset.mem_insert] at hv
      rcases hv with rfl | rfl | hv
      · exact Finset.mem_sdiff.2 ⟨h1E, not_mem_verts_del h1⟩
      · exact Finset.mem_sdiff.2 ⟨h2E, not_mem_verts_del h2⟩
      · exact Finset.mem_sdiff.2 ⟨hSE hv, fun h' =>
          Finset.disjoint_left.1 (verts_del_disjoint E S) h' hv⟩
    have hc5 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hne, h1S]), Finset.card_insert_of_notMem h2S,
      hcard] at hc5
    obtain ⟨e, he⟩ : (hit E S).Nonempty := Finset.card_pos.1 (by omega)
    refine h.no_good_del (X := S) (R := verts E \ verts (del E S)) (D := hit E S)
      (hE (del E S)) Finset.sdiff_subset
      (Finset.disjoint_left.2 fun v hv => (Finset.mem_sdiff.1 hv).2) subset_rfl ⟨e, he⟩ le_rfl ?_
    rw [hcard]
    omega

/-- **Claim 13**, in the form used below. -/
lemma claim13' (h : MinCex E) {a b c : α} (ha : a ∈ verts E) (hb : b ∈ verts E)
    (hc : c ∈ verts E) (hab : a ≠ b) (nac : ¬ Adj E a c) (nbc : ¬ Adj E b c)
    {u₁ u₂ : α} (hne : u₁ ≠ u₂) (h1S : u₁ ≠ a ∧ u₁ ≠ b ∧ u₁ ≠ c) (h2S : u₂ ≠ a ∧ u₂ ≠ b ∧ u₂ ≠ c)
    (h1E : u₁ ∈ verts E) (h2E : u₂ ∈ verts E)
    (h1 : ∀ f ∈ E, u₁ ∈ f → a ∈ f ∨ b ∈ f ∨ c ∈ f)
    (h2 : ∀ f ∈ E, u₂ ∈ f → a ∈ f ∨ b ∈ f ∨ c ∈ f) : False := by
  have hac : a ≠ c := fun h' => nac (h' ▸ by
    obtain ⟨f, hf, haf⟩ := mem_verts.1 ha; exact ⟨f, hf, haf, haf⟩)
  have hbc : b ≠ c := fun h' => nbc (h' ▸ by
    obtain ⟨f, hf, hbf⟩ := mem_verts.1 hb; exact ⟨f, hf, hbf, hbf⟩)
  have hmeet : ∀ {u}, (∀ f ∈ E, u ∈ f → a ∈ f ∨ b ∈ f ∨ c ∈ f) →
      ∀ f ∈ E, u ∈ f → ¬ Disjoint f {a, b, c} := by
    intro u hu f hf huf
    rw [Finset.not_disjoint_iff]
    rcases hu f hf huf with h' | h' | h'
    · exact ⟨a, h', by simp⟩
    · exact ⟨b, h', by simp⟩
    · exact ⟨c, h', by simp⟩
  refine h.claim13 (S := {a, b, c}) ?_ ?_ (hit8 h.L h.claim10 ha hb hc hab nac nbc) hne
    (by simp [h1S.1, h1S.2.1, h1S.2.2]) (by simp [h2S.1, h2S.2.1, h2S.2.2]) h1E h2E
    (hmeet h1) (hmeet h2)
  · rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption

/-- **Claim 14**. -/
lemma claim14 (h : MinCex E) {s₁ s₂ : α} (hs : s₁ ≠ s₂) (hs₁E : s₁ ∈ verts E)
    (hs₂E : s₂ ∈ verts E) (hna : ¬ Adj E s₁ s₂) {u₁ u₂ u₃ : α}
    (he : ({u₁, u₂, u₃} : Finset α) ∈ E) (hs₁e : s₁ ∉ ({u₁, u₂, u₃} : Finset α))
    (hs₂e : s₂ ∉ ({u₁, u₂, u₃} : Finset α))
    (h1 : ∀ f ∈ E, u₁ ∈ f → f ≠ {u₁, u₂, u₃} → s₁ ∈ f ∨ s₂ ∈ f)
    (h2 : ∀ f ∈ E, u₂ ∈ f → f ≠ {u₁, u₂, u₃} → s₁ ∈ f ∨ s₂ ∈ f)
    {g : Finset α} (hg : g ∈ E) (hge : g ≠ {u₁, u₂, u₃}) (hu₃g : u₃ ∈ g) (hs₁g : s₁ ∉ g)
    (hs₂g : s₂ ∉ g) : False := by
  have hL := h.L
  have hreg := h.claim10
  set e : Finset α := {u₁, u₂, u₃}
  obtain ⟨h12, h13, h23⟩ := ne_of_card3 (hL.card3 e he)
  have hu₁e : u₁ ∈ e := by simp [e]
  have hu₂e : u₂ ∈ e := by simp [e]
  have hu₃e : u₃ ∈ e := by simp [e]
  have hs₁u : ∀ {u}, u ∈ e → u ≠ s₁ := fun hu h' => hs₁e (h' ▸ hu)
  have hs₂u : ∀ {u}, u ∈ e → u ≠ s₂ := fun hu h' => hs₂e (h' ▸ hu)
  have hS3 : ({s₁, s₂, u₃} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hs, Ne.symm (hs₁u hu₃e)]),
      Finset.card_pair (Ne.symm (hs₂u hu₃e))]
  set F₁ := E.filter (s₁ ∈ ·)
  set F₂ := E.filter (s₂ ∈ ·)
  have hd : Disjoint F₁ F₂ := by
    rw [Finset.disjoint_left]
    intro f hf hf'
    exact hna ⟨f, (Finset.mem_filter.1 hf).1, (Finset.mem_filter.1 hf).2,
      (Finset.mem_filter.1 hf').2⟩
  have hd2 : Disjoint (F₁ ∪ F₂) {e, g} := by
    rw [Finset.disjoint_left]
    intro f hf hf'
    simp only [F₁, F₂, Finset.mem_union, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton] at hf hf'
    rcases hf' with rfl | rfl <;> rcases hf with h' | h' <;> tauto
  have hsub : (F₁ ∪ F₂) ∪ {e, g} ⊆ hit E {s₁, s₂, u₃} := by
    intro f hf
    simp only [F₁, F₂, Finset.mem_union, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton] at hf
    refine mem_hit.2 ⟨?_, Finset.not_disjoint_iff.2 ?_⟩
    · rcases hf with (h' | h') | rfl | rfl
      · exact h'.1
      · exact h'.1
      · exact he
      · exact hg
    · rcases hf with (h' | h') | rfl | rfl
      · exact ⟨s₁, h'.2, by simp⟩
      · exact ⟨s₂, h'.2, by simp⟩
      · exact ⟨u₃, hu₃e, by simp⟩
      · exact ⟨u₃, hu₃g, by simp⟩
  have h8 : 8 ≤ (hit E {s₁, s₂, u₃}).card := by
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd,
      Finset.card_pair (Ne.symm hge)] at this
    have : F₁.card = 3 := hreg s₁ hs₁E
    have : F₂.card = 3 := hreg s₂ hs₂E
    omega
  have hmeet : ∀ {u}, u ∈ e → (∀ f ∈ E, u ∈ f → f ≠ e → s₁ ∈ f ∨ s₂ ∈ f) →
      ∀ f ∈ E, u ∈ f → ¬ Disjoint f {s₁, s₂, u₃} := by
    intro u _ hu f hf huf
    rw [Finset.not_disjoint_iff]
    by_cases hfe : f = e
    · exact ⟨u₃, hfe ▸ hu₃e, by simp⟩
    · rcases hu f hf huf hfe with h' | h'
      · exact ⟨s₁, h', by simp⟩
      · exact ⟨s₂, h', by simp⟩
  refine h.claim13 hS3 ?_ h8 h12 ?_ ?_ (subset_verts he hu₁e) (subset_verts he hu₂e)
    (hmeet hu₁e h1) (hmeet hu₂e h2)
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hs₁E
    · exact hs₂E
    · exact subset_verts he hu₃e
  · simp [hs₁u hu₁e, hs₂u hu₁e, h13]
  · simp [hs₁u hu₂e, hs₂u hu₂e, h23]

end MinCex

end OpenProblemsLab.HY
