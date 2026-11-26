import Lab.HenningYeo.Claim11b

/-!
# Henning–Yeo Claim 11, part 3: the sets `T, Q, R` and the common 5-good reduction

`T = e₁ ∪ e₂`, `R = T ∪ S ∪ {x}` (10 vertices), `B` = the 11 edges at `R`, and `Q` = the vertices of
`H - S` outside `T` that lost an edge (`|Q| ≤ 3`). Deleting any set `X ⊆ R ∪ {q}` of at most five
vertices that contains `q ∈ Q` and meets all of `B` is a good reduction (`red5`).
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

def Q11 (E : Finset (Finset α)) (S e₁ e₂ : Finset α) : Finset α :=
  ((verts (del E S)) \ (e₁ ∪ e₂)).filter (fun v => 0 < deg (hit E S) v)

def R11 (x : α) (S e₁ e₂ : Finset α) : Finset α := insert x S ∪ (e₁ ∪ e₂)

def B11 (E : Finset (Finset α)) (S e₁ e₂ : Finset α) : Finset (Finset α) := hit E S ∪ {e₁, e₂}

namespace C11

variable {E : Finset (Finset α)} {x : α} {S e₁ e₂ : Finset α}

lemma mem_Q {v : α} : v ∈ Q11 E S e₁ e₂ ↔
    v ∈ verts (del E S) ∧ v ∉ e₁ ∪ e₂ ∧ 0 < deg (hit E S) v := by
  simp [Q11, and_assoc]

lemma mem_R {v : α} : v ∈ R11 x S e₁ e₂ ↔ v = x ∨ v ∈ S ∨ v ∈ e₁ ∪ e₂ := by
  simp [R11]

lemma mem_B {f : Finset α} : f ∈ B11 E S e₁ e₂ ↔ f ∈ hit E S ∨ f = e₁ ∨ f = e₂ := by
  simp only [B11, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]

variable (C : C11 E x S e₁ e₂)
include C

lemma iso1 : e₁ ∈ isoEdges (del E S) := by rw [C.iso]; simp
lemma iso2 : e₂ ∈ isoEdges (del E S) := by rw [C.iso]; simp
lemma del1 : e₁ ∈ del E S := isoEdges_subset _ C.iso1
lemma del2 : e₂ ∈ del E S := isoEdges_subset _ C.iso2
lemma mem1 : e₁ ∈ E := del_subset _ _ C.del1
lemma mem2 : e₂ ∈ E := del_subset _ _ C.del2
lemma disj12 : Disjoint e₁ e₂ := isoEdges_pairwise C.iso1 C.iso2 C.ne

lemma T_verts : e₁ ∪ e₂ ⊆ verts (del E S) :=
  Finset.union_subset (subset_verts C.del1) (subset_verts C.del2)

lemma card_T : (e₁ ∪ e₂).card = 6 := by
  rw [Finset.card_union_of_disjoint C.disj12, C.h.L.card3 _ C.mem1, C.h.L.card3 _ C.mem2]

lemma iso_of_T {t : α} (ht : t ∈ e₁ ∪ e₂) : ∃ e ∈ isoEdges (del E S), t ∈ e := by
  rcases Finset.mem_union.1 ht with h1 | h2
  · exact ⟨e₁, C.iso1, h1⟩
  · exact ⟨e₂, C.iso2, h2⟩

lemma verts_cases {v : α} (hv : v ∈ verts E) : v ∈ insert x S ∨ v ∈ verts (del E S) := by
  by_cases h' : v ∈ verts (del E S)
  · exact Or.inr h'
  · left; rw [← C.gone]; exact Finset.mem_sdiff.2 ⟨hv, h'⟩

lemma x_gone : x ∉ verts (del E S) := by
  have : x ∈ verts E \ verts (del E S) := by rw [C.gone]; exact Finset.mem_insert_self _ _
  exact (Finset.mem_sdiff.1 this).2

lemma xS_verts : insert x S ⊆ verts E := by
  rw [← C.gone]; exact Finset.sdiff_subset

set_option linter.unusedSectionVars false in
lemma S_gone {s : α} (hs : s ∈ S) : s ∉ verts (del E S) := fun h' =>
  Finset.disjoint_left.1 (verts_del_disjoint E S) h' hs

lemma xS_gone {v : α} (hv : v ∈ insert x S) : v ∉ verts (del E S) := by
  rw [Finset.mem_insert] at hv
  rcases hv with rfl | hv
  · exact C.x_gone
  · exact C.S_gone hv

lemma deg_hit_T {t : α} (ht : t ∈ e₁ ∪ e₂) : deg (hit E S) t = 2 := by
  obtain ⟨e, he, hte⟩ := C.iso_of_T ht
  have := deg_del_add_hit E S t
  rw [deg_iso he hte, C.reg t (verts_mono (del_subset E S) (C.T_verts ht))] at this
  omega

lemma sum_Q : ∑ v ∈ Q11 E S e₁ e₂, deg (hit E S) v = 3 := by
  have h1 := Finset.sum_sdiff (f := fun v => deg (hit E S) v) C.T_verts
  have h2 : ∑ v ∈ e₁ ∪ e₂, deg (hit E S) v = 12 := by
    rw [Finset.sum_congr rfl (fun t ht => C.deg_hit_T ht), Finset.sum_const, C.card_T]; rfl
  have h3 : ∑ v ∈ Q11 E S e₁ e₂, deg (hit E S) v =
      ∑ v ∈ verts (del E S) \ (e₁ ∪ e₂), deg (hit E S) v :=
    Finset.sum_filter_of_ne fun v _ hv => Nat.pos_of_ne_zero hv
  have := C.U
  omega

lemma card_Q : (Q11 E S e₁ e₂).card ≤ 3 := by
  have := C.sum_Q
  rw [Finset.card_eq_sum_ones]
  calc ∑ _v ∈ Q11 E S e₁ e₂, 1 ≤ ∑ v ∈ Q11 E S e₁ e₂, deg (hit E S) v :=
        Finset.sum_le_sum fun v hv => (mem_Q.1 hv).2.2
    _ = 3 := this

/-- Every edge at a vertex of `R` is one of the 11 edges of `B`. -/
lemma edges_R {r : α} (hr : r ∈ R11 x S e₁ e₂) {f : Finset α} (hf : f ∈ E) (hrf : r ∈ f) :
    f ∈ B11 E S e₁ e₂ := by
  rw [mem_B]
  by_cases hfS : Disjoint f S
  · right
    have hfd : f ∈ del E S := mem_del.2 ⟨hf, hfS⟩
    have hrv : r ∈ verts (del E S) := subset_verts hfd hrf
    rcases mem_R.1 hr with rfl | hr | hr
    · exact absurd hrv C.x_gone
    · exact absurd hrv (C.S_gone hr)
    · rcases Finset.mem_union.1 hr with h1 | h2
      · left; exact eq_of_deg_one (deg_iso C.iso1 h1) C.del1 h1 hfd hrf
      · right; exact eq_of_deg_one (deg_iso C.iso2 h2) C.del2 h2 hfd hrf
  · exact Or.inl (mem_hit.2 ⟨hf, hfS⟩)

lemma R_verts : R11 x S e₁ e₂ ⊆ verts E :=
  Finset.union_subset C.xS_verts (C.T_verts.trans (verts_mono (del_subset E S)))

lemma card_R : (R11 x S e₁ e₂).card = 10 := by
  have hd : Disjoint (insert x S) (e₁ ∪ e₂) :=
    Finset.disjoint_left.2 fun v hv hvT => C.xS_gone hv (C.T_verts hvT)
  have hxS : x ∉ S := fun hx => by
    have := C.hS hx; rw [nbr, Finset.mem_sdiff] at this; exact this.2 (Finset.mem_singleton_self x)
  rw [R11, Finset.card_union_of_disjoint hd, C.card_T, Finset.card_insert_of_notMem hxS, C.card]

lemma Q_not_R {q : α} (hq : q ∈ Q11 E S e₁ e₂) : q ∉ R11 x S e₁ e₂ := by
  obtain ⟨hqv, hqT, -⟩ := mem_Q.1 hq
  rw [mem_R]
  rintro (rfl | hqS | hqT')
  · exact C.x_gone hqv
  · exact C.S_gone hqS hqv
  · exact hqT hqT'

lemma e1_not_hit : e₁ ∉ hit E S := fun h' =>
  Finset.disjoint_left.1 (disjoint_del_hit E S) C.del1 h'
lemma e2_not_hit : e₂ ∉ hit E S := fun h' =>
  Finset.disjoint_left.1 (disjoint_del_hit E S) C.del2 h'

lemma card_hit : (hit E S).card = 9 := by
  have hSE : S ⊆ verts E := fun s hs => C.xS_verts (Finset.mem_insert_of_mem hs)
  rw [card_hit_of_ind C.ind, Finset.sum_congr rfl (g := fun _ => 3) (fun s hs => C.reg s (hSE hs)),
    Finset.sum_const, C.card]
  rfl

lemma card_B : (B11 E S e₁ e₂).card = 11 := by
  have hd : Disjoint (hit E S) {e₁, e₂} := by
    rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    exact ⟨C.e1_not_hit, C.e2_not_hit⟩
  rw [B11, Finset.card_union_of_disjoint hd, C.card_hit, Finset.card_pair C.ne]

lemma B_sub : B11 E S e₁ e₂ ⊆ E := by
  intro f hf
  rcases mem_B.1 hf with hf | rfl | rfl
  · exact (mem_hit.1 hf).1
  · exact C.mem1
  · exact C.mem2

/-- The common 5-good reduction of Claims 11.2 and 11. -/
lemma red5 {X : Finset α} {q : α} (hq : q ∈ Q11 E S e₁ e₂) (hqX : q ∈ X)
    (hX : X ⊆ R11 x S e₁ e₂ ∪ {q}) (hXc : X.card ≤ 5)
    (hB : ∀ f ∈ B11 E S e₁ e₂, ¬ Disjoint f X) : False := by
  have hL := C.h.L
  have hqE : q ∈ verts E := verts_mono (del_subset E S) (mem_Q.1 hq).1
  -- all of `R ∪ {q}` disappears
  have hgone : Disjoint (R11 x S e₁ e₂ ∪ {q}) (verts (del E X)) := by
    rw [Finset.disjoint_left]
    intro v hv hvd
    rcases Finset.mem_union.1 hv with hvR | hvq
    · exact not_mem_verts_del (fun f hf hvf => hB f (C.edges_R hvR hf hvf)) hvd
    · rw [Finset.mem_singleton] at hvq
      subst hvq
      exact Finset.disjoint_left.1 (verts_del_disjoint E X) hvd hqX
  have hcR : (R11 x S e₁ e₂ ∪ {q}).card = 11 := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.2 (C.Q_not_R hq)),
      C.card_R, Finset.card_singleton]
  -- no isolated edge survives
  have h0 : hE (del E X) = 0 := by
    by_contra hne
    obtain ⟨f, hf⟩ : (isoEdges (del E X)).Nonempty :=
      Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
    have hfd := isoEdges_subset _ hf
    have hsub : f ⊆ (Q11 E S e₁ e₂).erase q := by
      intro v hvf
      have hvd : v ∈ verts (del E X) := subset_verts hfd hvf
      have hv1 := deg_iso hf hvf
      have hvE : v ∈ verts E := verts_mono (del_subset E X) hvd
      have hvR : v ∉ R11 x S e₁ e₂ ∪ {q} := fun h' => Finset.disjoint_left.1 hgone h' hvd
      have hvq : v ≠ q := fun h' => hvR (Finset.mem_union_right _ (by simp [h']))
      have hvR' : v ∉ R11 x S e₁ e₂ := fun h' => hvR (Finset.mem_union_left _ h')
      have hvS : v ∈ verts (del E S) := by
        rcases C.verts_cases hvE with h' | h'
        · exact absurd (Finset.mem_union_left _ h') hvR'
        · exact h'
      have hvT : v ∉ e₁ ∪ e₂ := fun h' => hvR' (Finset.mem_union_right _ h')
      refine Finset.mem_erase.2 ⟨hvq, mem_Q.2 ⟨hvS, hvT, ?_⟩⟩
      by_contra hz
      push Not at hz
      have hz0 : deg (hit E S) v = 0 := by omega
      -- every edge at `v` avoids `S`, so only an edge through `q` can meet `X`
      have hsub2 : (hit E X).filter (v ∈ ·) ⊆ E.filter (fun g => q ∈ g ∧ v ∈ g) := by
        intro g hg
        rw [Finset.mem_filter] at hg ⊢
        obtain ⟨hgX, hvg⟩ := hg
        obtain ⟨hgE, hgd⟩ := mem_hit.1 hgX
        obtain ⟨y, hyg, hyX⟩ := Finset.not_disjoint_iff.1 hgd
        refine ⟨hgE, ?_, hvg⟩
        rcases Finset.mem_union.1 (hX hyX) with hyR | hyq
        · exfalso
          rcases mem_B.1 (C.edges_R hyR hgE hyg) with hgS | rfl | rfl
          · have : 0 < deg (hit E S) v :=
              Finset.card_pos.2 ⟨g, Finset.mem_filter.2 ⟨hgS, hvg⟩⟩
            omega
          · exact hvT (Finset.mem_union_left _ hvg)
          · exact hvT (Finset.mem_union_right _ hvg)
        · rw [Finset.mem_singleton] at hyq; exact hyq ▸ hyg
      have hle : deg (hit E X) v ≤ 1 :=
        (Finset.card_le_card hsub2).trans (card_le_one_two hL (Ne.symm hvq))
      have := deg_del_add_hit E X v
      rw [hv1, C.reg v hvE] at this
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hq, hL.card3 f (del_subset _ _ hfd)] at this
    have := C.card_Q
    omega
  obtain ⟨b, hb⟩ : (B11 E S e₁ e₂).Nonempty := Finset.card_pos.1 (by rw [C.card_B]; omega)
  refine C.h.no_good_del (X := X) (R := R11 x S e₁ e₂ ∪ {q}) (D := B11 E S e₁ e₂) 0
    (Finset.union_subset C.R_verts (Finset.singleton_subset_iff.2 hqE)) hgone
    (fun f hf => mem_hit.2 ⟨C.B_sub hf, hB f hf⟩) ⟨b, hb⟩ h0.le ?_
  rw [hcR, C.card_B]
  omega

end C11

end OpenProblemsLab.HY
