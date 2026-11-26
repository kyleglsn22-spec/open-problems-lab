import Lab.HenningYeo.GadgetFacts

/-!
# Structure of copies of `H₁₀`, `H₁₀'`
-/

namespace OpenProblemsLab.HY

variable {α : Type*} [DecidableEq α]

section Copy

variable {K : Finset (Finset (Fin 10))} {g : Fin 10 → α} (hg : Function.Injective g)
include hg

lemma image_mem_image_iff {i : Fin 10} {f : Finset (Fin 10)} : g i ∈ f.image g ↔ i ∈ f := by
  simp [hg.eq_iff]

lemma deg_copy (i : Fin 10) : deg (K.image (fun e => e.image g)) (g i) = deg K i := by
  unfold deg
  have : (K.image (fun e => e.image g)).filter (g i ∈ ·) =
      (K.filter (i ∈ ·)).image (fun e => e.image g) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨f0, hf0, rfl⟩, hi⟩
      exact ⟨f0, ⟨hf0, (image_mem_image_iff hg).1 hi⟩, rfl⟩
    · rintro ⟨f0, ⟨hf0, hi⟩, rfl⟩
      exact ⟨⟨f0, hf0, rfl⟩, (image_mem_image_iff hg).2 hi⟩
  rw [this, Finset.card_image_of_injective _ (Finset.image_injective hg)]

omit hg in
lemma mem_verts_copy {u : α} (hu : u ∈ verts (K.image (fun e => e.image g))) : ∃ i, g i = u := by
  obtain ⟨f, hf, huf⟩ := mem_verts.1 hu
  obtain ⟨f0, -, rfl⟩ := Finset.mem_image.1 hf
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 huf
  exact ⟨i, rfl⟩

end Copy

/-- Data of a closed copy of `H₁₀`/`H₁₀'` inside `G`. -/
structure GCopy (G : Finset (Finset α)) (l : Fin 5) (a b : Fin 7) (g : Fin 10 → α) : Prop where
  valid : GValid l a b
  inj : Function.Injective g
  closed : IsClosed G ((gadget l a b).image (fun e => e.image g))

namespace GCopy

variable {G : Finset (Finset α)} {l : Fin 5} {a b : Fin 7} {g : Fin 10 → α}

lemma of_gadget {F : Finset (Finset α)} (hF : IsClosed G F) (hgad : IsGadget F) :
    ∃ l a b g, GCopy G l a b g ∧ F = (gadget l a b).image (fun e => e.image g) := by
  obtain ⟨l, a, b, ha, hb, hab, g, hg, rfl⟩ := hgad
  exact ⟨l, a, b, g, ⟨⟨ha, hb, hab⟩, hg, hF⟩, rfl⟩

lemma deg_eq (C : GCopy G l a b g) (i : Fin 10) : deg G (g i) = deg (gadget l a b) i := by
  have h1 := deg_copy (K := gadget l a b) C.inj i
  have hv : g i ∈ verts ((gadget l a b).image (fun e => e.image g)) :=
    mem_verts_of_deg_pos (by rw [h1]; exact gadget_cover l a b C.valid i)
  rw [← C.closed.deg_eq hv, h1]

lemma verts_mem (C : GCopy G l a b g) (i : Fin 10) :
    g i ∈ verts ((gadget l a b).image (fun e => e.image g)) :=
  mem_verts_of_deg_pos (by rw [deg_copy C.inj]; exact gadget_cover l a b C.valid i)

/-- An edge of `G` through a vertex of the copy is an edge of the copy. -/
lemma edge (C : GCopy G l a b g) {f : Finset α} (hf : f ∈ G) {i : Fin 10} (hi : g i ∈ f) :
    ∃ f0 ∈ gadget l a b, f = f0.image g := by
  obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.1
    (C.closed.2 f hf (Finset.not_disjoint_iff.2 ⟨g i, hi, C.verts_mem i⟩))
  exact ⟨f0, hf0, rfl⟩

end GCopy

/-- In a copy of `H₁₀`/`H₁₀'` that is a union of components of `G`: if `z` has degree 1 and lies
in the edge `f ∋ p, q`, then `p, q` have degree 2, and their other edges meet in a vertex of degree
at least 3. -/
lemma gadget_leaf {G F : Finset (Finset α)} (hF : IsClosed G F) (hgad : IsGadget F) {z : α}
    (hzF : z ∈ verts F) (hz : deg G z = 1) {f : Finset α} (hf : f ∈ G) (hzf : z ∈ f) {p q : α}
    (hpf : p ∈ f) (hqf : q ∈ f) (hpz : p ≠ z) (hqz : q ≠ z) (hpq : p ≠ q) {fp fq : Finset α}
    (hfp : fp ∈ G) (hpfp : p ∈ fp) (hfpf : fp ≠ f) (hfq : fq ∈ G) (hqfq : q ∈ fq)
    (hfqf : fq ≠ f) :
    deg G p = 2 ∧ deg G q = 2 ∧ ∃ c ∈ fp, c ∈ fq ∧ 3 ≤ deg G c := by
  obtain ⟨l, a, b, g, C, rfl⟩ := GCopy.of_gadget hF hgad
  have hv := C.valid
  obtain ⟨i, rfl⟩ := mem_verts_copy hzF
  have hi7 : i = 7 := gadget_leaf_unique l a b hv i (by rw [← C.deg_eq]; exact hz)
  subst hi7
  obtain ⟨f0, hf0, rfl⟩ := C.edge hf hzf
  have hf07 := gadget_edge7 l a b hv f0 hf0 ((image_mem_image_iff C.inj).1 hzf)
  subst hf07
  have h89 := gadget_deg89 l a b hv
  have hcases : ∀ r ∈ ({7, 8, 9} : Finset (Fin 10)).image g, r ≠ g 7 → r = g 8 ∨ r = g 9 := by
    intro r hr hr7
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact absurd rfl hr7
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- the other edges
  have key : ∀ j k : Fin 10, (j = 8 ∧ k = 9 ∨ j = 9 ∧ k = 8) → g j ∈ fp → g k ∈ fq →
      ∃ c ∈ fp, c ∈ fq ∧ 3 ≤ deg G c := by
    intro j k hjk hj hk
    obtain ⟨fp0, hfp0, rfl⟩ := C.edge hfp hj
    obtain ⟨fq0, hfq0, rfl⟩ := C.edge hfq hk
    have hne : ∀ e0 : Finset (Fin 10), e0.image g ≠ ({7, 8, 9} : Finset (Fin 10)).image g →
        e0 ≠ {7, 8, 9} := fun e0 h' h'' => h' (h'' ▸ rfl)
    have hp0 := hne _ hfpf
    have hq0 := hne _ hfqf
    have hj' := (image_mem_image_iff C.inj).1 hj
    have hk' := (image_mem_image_iff C.inj).1 hk
    rcases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨c, hc1, hc2, hc3⟩ := gadget_meet l a b hv fp0 hfp0 hj' hp0 fq0 hfq0 hk' hq0
      exact ⟨g c, Finset.mem_image_of_mem g hc1, Finset.mem_image_of_mem g hc2,
        by rw [C.deg_eq]; exact hc3⟩
    · obtain ⟨c, hc1, hc2, hc3⟩ := gadget_meet l a b hv fq0 hfq0 hk' hq0 fp0 hfp0 hj' hp0
      exact ⟨g c, Finset.mem_image_of_mem g hc2, Finset.mem_image_of_mem g hc1,
        by rw [C.deg_eq]; exact hc3⟩
  rcases hcases p hpf hpz with rfl | rfl <;> rcases hcases q hqf hqz with rfl | rfl
  · exact absurd rfl hpq
  · exact ⟨by rw [C.deg_eq]; exact h89.1, by rw [C.deg_eq]; exact h89.2,
      key 8 9 (Or.inl ⟨rfl, rfl⟩) hpfp hqfq⟩
  · exact ⟨by rw [C.deg_eq]; exact h89.2, by rw [C.deg_eq]; exact h89.1,
      key 9 8 (Or.inr ⟨rfl, rfl⟩) hpfp hqfq⟩
  · exact absurd rfl hpq

/-- A copy of `H₁₀`/`H₁₀'` has a single vertex of degree 1. -/
lemma gadget_one_leaf {G F : Finset (Finset α)} (hF : IsClosed G F) (hgad : IsGadget F) {y z : α}
    (hyF : y ∈ verts F) (hzF : z ∈ verts F) (hy : deg G y = 1) (hz : deg G z = 1) : y = z := by
  obtain ⟨l, a, b, g, C, rfl⟩ := GCopy.of_gadget hF hgad
  obtain ⟨i, rfl⟩ := mem_verts_copy hyF
  obtain ⟨j, rfl⟩ := mem_verts_copy hzF
  rw [gadget_leaf_unique l a b C.valid i (by rw [← C.deg_eq]; exact hy),
    gadget_leaf_unique l a b C.valid j (by rw [← C.deg_eq]; exact hz)]

end OpenProblemsLab.HY
