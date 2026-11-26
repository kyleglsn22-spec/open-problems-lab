import Lab.Erdos757.FourSevenths

/-!
# Erdős #757: the lower bound `9/17` (Ma–Tang), conditional on Henning–Yeo

Ma–Tang (arXiv:2602.23282, §5.2) prove that every `(4,5)`-set `A` has a Sidon subset of size at
least `9|A|/17`. Their argument has two parts:

* elementary facts about the hypergraph `H(A)` whose edges are the three-term progressions in `A`:
  `A` is weak Sidon, Sidon subsets are exactly the progression-free ones, `H(A)` has at most `|A|`
  edges, is linear, and contains no copy of `F₇`;
* the Henning–Yeo transversal theorem `17τ ≤ 5n + 3m` for linear `F₇`-free 3-uniform hypergraphs.

Everything in the first part is proved here from the upstream definitions. The Henning–Yeo
theorem (a 24-page combinatorial argument) is **not** formalized: it enters as the explicit
hypothesis `HenningYeoBound`, so every theorem that depends on it says so in its type.
No axioms beyond `propext`, `Classical.choice`, `Quot.sound` are used.
-/

open scoped Pointwise

namespace OpenProblemsLab.E757.LowerBound

open _root_.Erdos757

/-- The upstream `(4,5)` condition on a set of reals. -/
def Is45 (A : Set ℝ) : Prop := ∀ B ⊆ A, B.ncard = 4 → 11 ≤ (B - B).ncard

/-- Tries each disjunct of a goal `P₁ ∨ P₂ ∨ ... ∨ Pₖ` with `linarith`. -/
syntax "solve_disj" : tactic
macro_rules
  | `(tactic| solve_disj) =>
    `(tactic| first
      | (apply Or.inl; linarith)
      | (apply Or.inr; solve_disj)
      | linarith)

/-- Four distinct points of a `(4,5)`-set whose pairwise differences all lie in a list of at
most ten numbers give a contradiction. -/
lemma not45 {A : Set ℝ} (h : Is45 A) {a b c d : ℝ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hd : d ∈ A) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (L : List ℝ) (hL : L.length ≤ 10)
    (hdiff : ∀ x ∈ [a, b, c, d], ∀ y ∈ [a, b, c, d], x - y ∈ L) : False := by
  have hB : ({a, b, c, d} : Set ℝ) ⊆ A := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c, d} : Set ℝ).ncard = 4 := by
    rw [Set.ncard_eq_toFinset_card']
    simp [Finset.card_insert_of_notMem, *]
  have h11 := h _ hB hcard
  have hsub : ({a, b, c, d} : Set ℝ) - {a, b, c, d} ⊆ ((L.toFinset : Finset ℝ) : Set ℝ) := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_sub.1 hz
    have hx' : x ∈ [a, b, c, d] := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp
    have hy' : y ∈ [a, b, c, d] := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> simp
    simpa using hdiff x hx' y hy'
  have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at this
  have := L.toFinset_card_le
  omega

/-- Every `(4,5)`-set is weak Sidon (Ma–Tang, Prop. 2.2). -/
lemma weakSidon {A : Set ℝ} (h : Is45 A) {a b c d : ℝ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hd : d ∈ A) (hab : a ≠ b) (hcd : c ≠ d) (hs : a + b = c + d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  by_contra hne
  push Not at hne
  have hac : a ≠ c := fun e => hne.1 e (by linarith)
  have had : a ≠ d := fun e => hne.2 e (by linarith)
  have hbc : b ≠ c := fun e => hne.2 (by linarith) e
  have hbd : b ≠ d := fun e => hne.1 (by linarith) e
  exact not45 h ha hb hc hd hab hac had hbc hbd hcd
    [0, a - b, b - a, a - c, c - a, a - d, d - a, c - d, d - c] (by simp)
    (by intro x hx y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy ⊢
        rcases hx with rfl | rfl | rfl | rfl <;>
          rcases hy with rfl | rfl | rfl | rfl <;> solve_disj)


/- ## The A.P.-hypergraph of a finite set of reals -/

/-- Three-term arithmetic progressions `x < y < z`, `x + z = 2y`, inside `F`. -/
noncomputable def apTriples (F : Finset ℝ) : Finset (ℝ × ℝ × ℝ) :=
  (F ×ˢ F ×ˢ F).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.1 + t.2.2 = 2 * t.2.1)

/-- Edges of the A.P.-hypergraph `H(F)`: the 3-element sets that are arithmetic progressions. -/
noncomputable def apEdges (F : Finset ℝ) : Finset (Finset ℝ) :=
  (apTriples F).image (fun t => {t.1, t.2.1, t.2.2})

lemma mem_apTriples {F : Finset ℝ} {t : ℝ × ℝ × ℝ} : t ∈ apTriples F ↔
    t.1 ∈ F ∧ t.2.1 ∈ F ∧ t.2.2 ∈ F ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.1 + t.2.2 = 2 * t.2.1 := by
  simp [apTriples, and_assoc]

lemma mem_apEdges {F : Finset ℝ} {e : Finset ℝ} : e ∈ apEdges F ↔
    ∃ x y z, x ∈ F ∧ y ∈ F ∧ z ∈ F ∧ x < y ∧ y < z ∧ x + z = 2 * y ∧ e = {x, y, z} := by
  constructor
  · intro he
    obtain ⟨⟨x, y, z⟩, ht, rfl⟩ := Finset.mem_image.1 he
    rw [mem_apTriples] at ht
    exact ⟨x, y, z, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2, rfl⟩
  · rintro ⟨x, y, z, hx, hy, hz, hxy, hyz, hs, rfl⟩
    exact Finset.mem_image.2 ⟨(x, y, z), mem_apTriples.2 ⟨hx, hy, hz, hxy, hyz, hs⟩, rfl⟩

lemma apEdges_spec {F : Finset ℝ} {e : Finset ℝ} (he : e ∈ apEdges F) : e ⊆ F ∧ e.card = 3 := by
  obtain ⟨x, y, z, hx, hy, hz, hxy, hyz, -, rfl⟩ := mem_apEdges.1 he
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  · rw [Finset.card_insert_of_notMem, Finset.card_pair (by linarith)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨by linarith, by linarith⟩

/-- In a weak Sidon set each point is the middle of at most one progression, so the
hypergraph has at most as many edges as vertices (Ma–Tang, Lemma 2.4). -/
lemma card_apEdges_le {F : Finset ℝ} (h : Is45 (F : Set ℝ)) : (apEdges F).card ≤ F.card := by
  refine (Finset.card_image_le).trans (Finset.card_le_card_of_injOn (fun t => t.2.1) ?_ ?_)
  · intro t ht
    exact (mem_apTriples.1 ht).2.1
  · rintro ⟨x, y, z⟩ ht ⟨x', y', z'⟩ ht' (hyy : y = y')
    rw [Finset.mem_coe, mem_apTriples] at ht ht'
    obtain ⟨hx, hy, hz, hxy, hyz, hs⟩ := ht
    obtain ⟨hx', hy', hz', hxy', hyz', hs'⟩ := ht'
    subst hyy
    rcases weakSidon h hx hz hx' hz' (by linarith) (by linarith) (by linarith) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only at h1 h2; subst h1; subst h2; rfl
    · exact absurd h1 (by linarith)

/-- A subset of a weak Sidon set that contains no three-term progression is Sidon
(Ma–Tang, Lemma 2.3). -/
lemma isSidon_of_free {F S : Finset ℝ} (h : Is45 (F : Set ℝ)) (hSF : S ⊆ F)
    (hfree : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → x + z = 2 * y → False) :
    IsSidon (S : Set ℝ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs
  simp only [Finset.mem_coe] at hi₁ hj₁ hi₂ hj₂
  have mid : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, b ≠ c → 2 * a = b + c → False := by
    intro a ha b hb c hc hbc habc
    rcases lt_or_gt_of_ne hbc with hlt | hlt
    · exact hfree b hb a ha c hc (by linarith) (by linarith) (by linarith)
    · exact hfree c hc a ha b hb (by linarith) (by linarith) (by linarith)
  by_cases hi : i₁ = i₂ <;> by_cases hj : j₁ = j₂
  · subst hi; subst hj
    left; constructor <;> linarith
  · subst hi; exact (mid i₁ hi₁ j₁ hj₁ j₂ hj₂ hj (by linarith)).elim
  · subst hj; exact (mid j₁ hj₁ i₁ hi₁ i₂ hi₂ hi (by linarith)).elim
  · exact weakSidon h (hSF hi₁) (hSF hi₂) (hSF hj₁) (hSF hj₂) hi hj hs

/- ## Linearity (Ma–Tang, Lemma 2.5) -/

/-- An A.P. `x < y < z` containing `p < q` is one of three progressions. -/
lemma ap_through {x y z p q : ℝ} (hxy : x < y) (hyz : y < z) (hs : x + z = 2 * y) (hpq : p < q)
    (hp : p = x ∨ p = y ∨ p = z) (hq : q = x ∨ q = y ∨ q = z) :
    (x = p ∧ y = q ∧ z = 2 * q - p) ∨ (x = p ∧ y = (p + q) / 2 ∧ z = q) ∨
      (x = 2 * p - q ∧ y = p ∧ z = q) := by
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  all_goals first
    | exact absurd hpq (by linarith)
    | (left; refine ⟨rfl, rfl, by linarith⟩)
    | (right; left; refine ⟨rfl, by linarith, rfl⟩)
    | (right; right; refine ⟨by linarith, rfl, rfl⟩)

/-- Two different progressions through the same two points `p < q` violate `(4,5)`. -/
lemma two_aps {A : Set ℝ} (h : Is45 A) {p q r s : ℝ} (hpq : p < q) (hp : p ∈ A) (hq : q ∈ A)
    (hr : r ∈ A) (hs : s ∈ A)
    (hrs : (r = 2 * q - p ∧ s = (p + q) / 2) ∨ (r = 2 * p - q ∧ s = (p + q) / 2) ∨
      (r = 2 * p - q ∧ s = 2 * q - p)) : False := by
  rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine not45 h hp hq hr hs (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
      [0, (q - p) / 2, -((q - p) / 2), q - p, p - q, 3 * (q - p) / 2, -(3 * (q - p) / 2),
        2 * (q - p), -(2 * (q - p))] (by simp) ?_
    intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> solve_disj
  · refine not45 h hp hq hr hs (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
      [0, (q - p) / 2, -((q - p) / 2), q - p, p - q, 3 * (q - p) / 2, -(3 * (q - p) / 2),
        2 * (q - p), -(2 * (q - p))] (by simp) ?_
    intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> solve_disj
  · refine not45 h hp hq hr hs (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
      [0, q - p, p - q, 2 * (q - p), -(2 * (q - p)), 3 * (q - p), -(3 * (q - p))] (by simp) ?_
    intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> solve_disj

/-- Two progressions in `F` that share two points `p < q` are the same progression. -/
lemma triple_unique {F : Finset ℝ} (h : Is45 (F : Set ℝ)) {x y z x' y' z' p q : ℝ}
    (hx : x ∈ F) (hy : y ∈ F) (hz : z ∈ F) (hxy : x < y) (hyz : y < z) (hs : x + z = 2 * y)
    (hx' : x' ∈ F) (hy' : y' ∈ F) (hz' : z' ∈ F) (hxy' : x' < y') (hyz' : y' < z')
    (hs' : x' + z' = 2 * y') (hpq : p < q) (hpF : p ∈ F) (hqF : q ∈ F)
    (hp : p = x ∨ p = y ∨ p = z) (hq : q = x ∨ q = y ∨ q = z)
    (hp' : p = x' ∨ p = y' ∨ p = z') (hq' : q = x' ∨ q = y' ∨ q = z') :
    x = x' ∧ y = y' ∧ z = z' := by
  have h1 := ap_through hxy hyz hs hpq hp hq
  have h2 := ap_through hxy' hyz' hs' hpq hp' hq'
  have two := fun {r s : ℝ} (hr : r ∈ F) (hs : s ∈ F) => @two_aps _ h p q r s hpq hpF hqF hr hs
  rcases h1 with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;>
    rcases h2 with ⟨f1, f2, f3⟩ | ⟨f1, f2, f3⟩ | ⟨f1, f2, f3⟩
  all_goals first
    | exact ⟨by linarith, by linarith, by linarith⟩
    | exact (two hz hy' (Or.inl ⟨by linarith, by linarith⟩)).elim
    | exact (two hz' hy (Or.inl ⟨by linarith, by linarith⟩)).elim
    | exact (two hx' hz (Or.inr (Or.inr ⟨by linarith, by linarith⟩))).elim
    | exact (two hx hz' (Or.inr (Or.inr ⟨by linarith, by linarith⟩))).elim
    | exact (two hx' hy (Or.inr (Or.inl ⟨by linarith, by linarith⟩))).elim
    | exact (two hx hy' (Or.inr (Or.inl ⟨by linarith, by linarith⟩))).elim

lemma apEdges_linear_aux {F : Finset ℝ} (h : Is45 (F : Set ℝ)) {e f : Finset ℝ}
    (he : e ∈ apEdges F) (hf : f ∈ apEdges F) {p q : ℝ} (hpq : p < q) (hpe : p ∈ e)
    (hqe : q ∈ e) (hpf : p ∈ f) (hqf : q ∈ f) : e = f := by
  have hpF := (apEdges_spec he).1 hpe
  have hqF := (apEdges_spec he).1 hqe
  obtain ⟨x, y, z, hx, hy, hz, hxy, hyz, hs, rfl⟩ := mem_apEdges.1 he
  obtain ⟨x', y', z', hx', hy', hz', hxy', hyz', hs', rfl⟩ := mem_apEdges.1 hf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpe hqe hpf hqf
  obtain ⟨rfl, rfl, rfl⟩ := triple_unique h hx hy hz hxy hyz hs hx' hy' hz' hxy' hyz' hs' hpq
    hpF hqF hpe hqe hpf hqf
  rfl

/-- The A.P.-hypergraph of a `(4,5)`-set is linear (Ma–Tang, Lemma 2.5). -/
lemma apEdges_linear {F : Finset ℝ} (h : Is45 (F : Set ℝ)) :
    ∀ e ∈ apEdges F, ∀ f ∈ apEdges F, e ≠ f → (e ∩ f).card ≤ 1 := by
  intro e he f hf hef
  by_contra hc
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (not_le.1 hc)
  rw [Finset.mem_inter] at ha hb
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact hef (apEdges_linear_aux h he hf hlt ha.1 hb.1 ha.2 hb.2)
  · exact hef (apEdges_linear_aux h he hf hlt hb.1 ha.1 hb.2 ha.2)

/- ## The excluded configuration `F₇` (Ma–Tang, Lemma 5.2, cited there from Gyárfás–Lehel 1995) -/

/-- `E` has no (not necessarily induced) copy of `F₇`, the affine plane `AG(2,3)` with two
points deleted: vertices `0, …, 6` and edges `012, 034, 056, 135, 246`. -/
def F7Free {α : Type*} [DecidableEq α] (E : Finset (Finset α)) : Prop :=
  ∀ g : Fin 7 → α, Function.Injective g →
    ¬ (({g 0, g 1, g 2} : Finset α) ∈ E ∧ ({g 0, g 3, g 4} : Finset α) ∈ E ∧
      ({g 0, g 5, g 6} : Finset α) ∈ E ∧ ({g 1, g 3, g 5} : Finset α) ∈ E ∧
      ({g 2, g 4, g 6} : Finset α) ∈ E)

/-- A 3-element edge `{a, b, c}` of `H(F)`: one of its points is the average of the others. -/
lemma ap3 {F : Finset ℝ} {a b c : ℝ} (he : ({a, b, c} : Finset ℝ) ∈ apEdges F) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    (2 * a = b + c ∨ 2 * b = a + c ∨ 2 * c = a + b) ∧ a ∈ F ∧ b ∈ F ∧ c ∈ F := by
  have hsub := (apEdges_spec he).1
  refine ⟨?_, hsub (by simp), hsub (by simp), hsub (by simp)⟩
  obtain ⟨x, y, z, -, -, -, hxy, hyz, hs, heq⟩ := mem_apEdges.1 he
  have hy : y ∈ ({a, b, c} : Finset ℝ) := by rw [heq]; simp
  have hsum := congrArg (fun s : Finset ℝ => s.sum id) heq
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc,
    Finset.sum_insert (by simp [hxy.ne, (hxy.trans hyz).ne]), Finset.sum_pair hyz.ne] at hsum
  simp only [id] at hsum
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl
  · left; linarith
  · right; left; linarith
  · right; right; linarith

/-- The A.P.-hypergraph of a `(4,5)`-set contains no copy of `F₇`. Every one of the
`3⁵ = 243` ways to place the middle terms forces two of the seven points to coincide or
four of them to violate the weak Sidon property. -/
lemma apEdges_F7Free {F : Finset ℝ} (h : Is45 (F : Set ℝ)) : F7Free (apEdges F) := by
  intro g hg ⟨e1, e2, e3, e4, e5⟩
  obtain ⟨h1, m0, m1, m2⟩ := ap3 e1 (hg.ne (by decide)) (hg.ne (by decide)) (hg.ne (by decide))
  obtain ⟨h2, -, m3, m4⟩ := ap3 e2 (hg.ne (by decide)) (hg.ne (by decide)) (hg.ne (by decide))
  obtain ⟨h3, -, m5, m6⟩ := ap3 e3 (hg.ne (by decide)) (hg.ne (by decide)) (hg.ne (by decide))
  obtain ⟨h4, -, -, -⟩ := ap3 e4 (hg.ne (by decide)) (hg.ne (by decide)) (hg.ne (by decide))
  obtain ⟨h5, -, -, -⟩ := ap3 e5 (hg.ne (by decide)) (hg.ne (by decide)) (hg.ne (by decide))
  have hmem : ∀ i, g i ∈ F := by intro i; fin_cases i <;> assumption
  have hws : ∀ a b c d : Fin 7, a ≠ b → c ≠ d → a ≠ c → a ≠ d → g a + g b = g c + g d →
      False := by
    intro a b c d hab hcd hac had hs
    rcases weakSidon h (hmem a) (hmem b) (hmem c) (hmem d) (hg.ne hab) (hg.ne hcd) hs with
      ⟨e, -⟩ | ⟨e, -⟩
    · exact hac (hg e)
    · exact had (hg e)
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 <;> rcases h4 with h4 | h4 | h4 <;>
    rcases h5 with h5 | h5 | h5
  · exact hws 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1) * h1 + (1) * h2)
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (2/3) * h4 + (-1/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact hws 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1) * h1 + (1) * h2)
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-4/3) * h1 + (2/3) * h2 + (2/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (4/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact hws 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1) * h1 + (1) * h2)
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 2 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-2/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 4 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/6) * h1 + (1/6) * h2 + (-1/3) * h3 + (-1/6) * h4 + (-1/6) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (4/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (2/3) * h4 + (2/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (4/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (4/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (4/3) * h2 + (1/3) * h3 + (2/3) * h4 + (2/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 1 = g 6) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-2/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 3 = g 6) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 2 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/6) * h1 + (-1/3) * h2 + (1/6) * h3 + (-1/6) * h4 + (-1/6) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (2/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 3 = g 6) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-1/6) * h2 + (-1/6) * h3 + (-1/3) * h4 + (1/6) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (2/3) * h4 + (-1/3) * h5 : g 1 = g 4) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (2/3) * h4 + (-1/3) * h5 : g 1 = g 6) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-1/6) * h2 + (-1/6) * h3 + (-1/3) * h4 + (1/6) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (2/3) * h4 + (-1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-1/6) * h2 + (-1/6) * h3 + (-1/3) * h4 + (1/6) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (2/3) * h4 + (-1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact hws 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by linear_combination (1/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (2/3) * h5)
  · exact absurd (by linear_combination (2/9) * h1 + (-4/9) * h2 + (-1/9) * h3 + (1/9) * h4 + (-2/9) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 2 = g 4) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 2 = g 4) (hg.ne (by decide))
  · exact hws 0 4 1 5 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1) * h2 + (1) * h4)
  · exact absurd (by linear_combination (4/9) * h1 + (-2/9) * h2 + (1/9) * h3 + (-4/9) * h4 + (2/9) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact hws 0 3 4 6 (by decide) (by decide) (by decide) (by decide) (by linear_combination (1/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (-1/3) * h5)
  · exact absurd (by linear_combination (-2/3) * h1 + (-2/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (4/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (2/3) * h4 + (2/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (1/3) * h2 + (4/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 1 = g 4) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (2/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 4 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (4/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (1/3) * h2 + (4/3) * h3 + (2/3) * h4 + (2/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact hws 0 1 2 4 (by decide) (by decide) (by decide) (by decide) (by linear_combination (1/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (2/3) * h4 + (-1/3) * h5)
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (2/3) * h4 + (-1/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/9) * h1 + (-1/9) * h2 + (-4/9) * h3 + (1/9) * h4 + (-2/9) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (4/9) * h1 + (1/9) * h2 + (-2/9) * h3 + (-4/9) * h4 + (2/9) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact hws 0 4 3 5 (by decide) (by decide) (by decide) (by decide) (by linear_combination (1/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (-1/3) * h5)
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 2 = g 4) (hg.ne (by decide))
  · exact hws 0 6 1 3 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1) * h3 + (1) * h4)
  · exact absurd (by linear_combination (-2/3) * h1 + (-2/3) * h2 + (-2/3) * h3 + (2/3) * h4 + (-1/3) * h5 : g 2 = g 4) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (1/6) * h2 + (1/6) * h3 + (-1/6) * h4 + (1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 2 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (-2/3) * h4 + (-2/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 2 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (-2/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (1/6) * h2 + (1/6) * h3 + (-1/6) * h4 + (-1/6) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 1 = g 4) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 1 = g 6) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (1/3) * h2 + (1/3) * h3 + (2/3) * h4 + (-1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/6) * h1 + (1/3) * h2 + (-1/6) * h3 + (-1/3) * h4 + (1/6) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 2 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/6) * h1 + (1/3) * h2 + (-1/6) * h3 + (-1/3) * h4 + (1/6) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (2/3) * h4 + (-1/3) * h5 : g 3 = g 6) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/6) * h1 + (1/3) * h2 + (-1/6) * h3 + (-1/3) * h4 + (1/6) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (2/3) * h4 + (-1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 2 = g 4) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 2 = g 4) (hg.ne (by decide))
  · exact hws 0 2 3 5 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1) * h1 + (1) * h4)
  · exact absurd (by linear_combination (-4/9) * h1 + (2/9) * h2 + (-1/9) * h3 + (1/9) * h4 + (-2/9) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact hws 0 1 2 6 (by decide) (by decide) (by decide) (by decide) (by linear_combination (2/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5)
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact hws 0 1 2 6 (by decide) (by decide) (by decide) (by decide) (by linear_combination (1/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (-1/3) * h5)
  · exact absurd (by linear_combination (-2/9) * h1 + (4/9) * h2 + (1/9) * h3 + (-4/9) * h4 + (2/9) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (2/3) * h2 + (2/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (1/3) * h2 + (1/3) * h3 + (2/3) * h4 + (-1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/6) * h1 + (-1/6) * h2 + (1/3) * h3 + (-1/3) * h4 + (1/6) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (2/3) * h4 + (-1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/6) * h1 + (-1/6) * h2 + (1/3) * h3 + (-1/3) * h4 + (1/6) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 2 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 4 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/6) * h1 + (-1/6) * h2 + (1/3) * h3 + (-1/3) * h4 + (1/6) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact hws 0 2 3 5 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1) * h1 + (1) * h4)
  · exact absurd (by linear_combination (1/6) * h1 + (-1/3) * h2 + (1/6) * h3 + (1/3) * h4 + (-1/6) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/6) * h1 + (-1/6) * h2 + (1/3) * h3 + (2/3) * h4 + (1/6) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-1/6) * h2 + (-1/6) * h3 + (-1/3) * h4 + (1/6) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact hws 0 4 1 5 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1) * h2 + (1) * h4)
  · exact absurd (by linear_combination (1/6) * h1 + (1/6) * h2 + (-1/3) * h3 + (-2/3) * h4 + (-1/6) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact hws 0 6 1 3 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1) * h3 + (1) * h4)
  · exact absurd (by linear_combination (-4/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (4/3) * h4 + (-2/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 3 = g 6) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 1 = g 6) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-4/3) * h2 + (-1/3) * h3 + (4/3) * h4 + (-2/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact hws 0 3 1 6 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-2/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (-1/3) * h5)
  · exact hws 0 1 3 6 (by decide) (by decide) (by decide) (by decide) (by linear_combination (1/3) * h1 + (-2/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (-1/3) * h5)
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 2 = g 4) (hg.ne (by decide))
  · exact hws 0 2 3 5 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1) * h1 + (1) * h4)
  · exact absurd (by linear_combination (-2/3) * h1 + (-2/3) * h2 + (-2/3) * h3 + (2/3) * h4 + (-1/3) * h5 : g 2 = g 4) (hg.ne (by decide))
  · exact hws 0 1 2 4 (by decide) (by decide) (by decide) (by decide) (by linear_combination (1/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5)
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/9) * h1 + (1/9) * h2 + (4/9) * h3 + (-4/9) * h4 + (2/9) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-4/9) * h1 + (-1/9) * h2 + (2/9) * h3 + (1/9) * h4 + (-2/9) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (2/3) * h2 + (2/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact hws 0 1 2 4 (by decide) (by decide) (by decide) (by decide) (by linear_combination (2/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (1/3) * h4 + (1/3) * h5)
  · exact absurd (by linear_combination (-4/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (4/3) * h4 + (-2/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (-2/3) * h5 : g 3 = g 6) (hg.ne (by decide))
  · exact hws 0 5 1 4 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-2/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5)
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact hws 0 1 4 5 (by decide) (by decide) (by decide) (by decide) (by linear_combination (1/3) * h1 + (-2/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (-1/3) * h5)
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 1 = g 4) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (-4/3) * h3 + (4/3) * h4 + (-2/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (-1/6) * h2 + (-1/6) * h3 + (1/6) * h4 + (-1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (2/3) * h4 + (2/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (2/3) * h4 + (2/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact hws 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (-2/3) * h5)
  · exact absurd (by linear_combination (-2/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 1 = g 4) (hg.ne (by decide))
  · exact hws 0 5 1 2 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (-2/3) * h5)
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 1 = g 6) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 2 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 2 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (4/3) * h2 + (-2/3) * h3 + (2/3) * h4 + (2/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-2/3) * h2 + (4/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (4/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-2/3) * h2 + (4/3) * h3 + (2/3) * h4 + (2/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (2/3) * h4 + (-1/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/9) * h1 + (4/9) * h2 + (-2/9) * h3 + (-4/9) * h4 + (2/9) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact hws 0 2 1 5 (by decide) (by decide) (by decide) (by decide) (by linear_combination (1/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (-1/3) * h5)
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact hws 0 2 1 5 (by decide) (by decide) (by decide) (by decide) (by linear_combination (2/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5)
  · exact absurd (by linear_combination (-1/9) * h1 + (2/9) * h2 + (-4/9) * h3 + (1/9) * h4 + (-2/9) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact hws 0 6 1 3 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1) * h3 + (1) * h4)
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 2 = g 4) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (2/3) * h2 + (2/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 2 = g 4) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 1 = g 4) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (2/3) * h3 + (-2/3) * h4 + (-2/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/6) * h1 + (2/3) * h2 + (1/6) * h3 + (-1/6) * h4 + (1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (2/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (-2/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 4 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (2/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact hws 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by linear_combination (1/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5)
  · exact absurd (by linear_combination (1/9) * h1 + (-2/9) * h2 + (4/9) * h3 + (-4/9) * h4 + (2/9) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact hws 0 4 1 5 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1) * h2 + (1) * h4)
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 2 = g 4) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (2/3) * h2 + (2/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 2 = g 4) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (-2/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/9) * h1 + (-4/9) * h2 + (2/9) * h3 + (1/9) * h4 + (-2/9) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact hws 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by linear_combination (2/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (1/3) * h4 + (1/3) * h5)
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (1/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact hws 0 4 1 2 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (1/3) * h5)
  · exact hws 0 6 1 2 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (1/3) * h5)
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-4/3) * h2 + (2/3) * h3 + (4/3) * h4 + (-2/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (-2/3) * h5 : g 1 = g 6) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (-2/3) * h4 + (-2/3) * h5 : g 1 = g 4) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (-4/3) * h3 + (4/3) * h4 + (-2/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact hws 0 1 3 4 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (-2/3) * h5)
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (2/3) * h4 + (2/3) * h5 : g 1 = g 4) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (2/3) * h4 + (2/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/6) * h1 + (-2/3) * h2 + (-1/6) * h3 + (1/6) * h4 + (-1/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-2/3) * h2 + (-2/3) * h3 + (2/3) * h4 + (2/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (-1/3) * h5 : g 3 = g 6) (hg.ne (by decide))
  · exact hws 0 1 4 5 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (-2/3) * h5)
  · exact absurd (by linear_combination (1/3) * h1 + (-2/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (2/3) * h3 + (-2/3) * h4 + (-2/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 1 = g 6) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (-2/3) * h4 + (-2/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (2/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 3 = g 6) (hg.ne (by decide))
  · exact absurd (by linear_combination (2/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (2/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/6) * h1 + (1/6) * h2 + (2/3) * h3 + (-1/6) * h4 + (1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-2/3) * h2 + (1/3) * h3 + (2/3) * h4 + (2/3) * h5 : g 1 = g 6) (hg.ne (by decide))
  · exact hws 0 3 1 6 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (-2/3) * h5)
  · exact absurd (by linear_combination (-2/3) * h1 + (1/3) * h2 + (1/3) * h3 + (2/3) * h4 + (2/3) * h5 : g 3 = g 6) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-2/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact hws 0 1 3 6 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (-1/3) * h3 + (-2/3) * h4 + (-2/3) * h5)
  · exact absurd (by linear_combination (-2/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (2/3) * h4 + (2/3) * h5 : g 0 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (-2/3) * h2 + (-2/3) * h3 + (2/3) * h4 + (2/3) * h5 : g 0 = g 1) (hg.ne (by decide))
  · exact absurd (by linear_combination (-1/6) * h1 + (-1/6) * h2 + (-2/3) * h3 + (1/6) * h4 + (-1/3) * h5 : g 0 = g 5) (hg.ne (by decide))
  · exact hws 0 1 4 6 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1/2) * h2 + (-1/2) * h3 + (1/2) * h4)
  · exact absurd (by linear_combination (-1/3) * h1 + (2/3) * h2 + (-1/3) * h3 + (1/3) * h4 + (-2/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (1/3) * h1 + (1/3) * h2 + (-2/3) * h3 + (2/3) * h4 + (2/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (1/3) * h2 + (1/3) * h3 + (-1/3) * h4 + (2/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact hws 0 3 2 6 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1/2) * h1 + (-1/2) * h3 + (1/2) * h4)
  · exact absurd (by linear_combination (-1/3) * h1 + (-1/3) * h2 + (2/3) * h3 + (-2/3) * h4 + (-2/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-4/3) * h1 + (2/3) * h2 + (2/3) * h3 + (1/3) * h4 + (4/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact absurd (by linear_combination (-2/3) * h1 + (4/3) * h2 + (-2/3) * h3 + (-1/3) * h4 + (-4/3) * h5 : g 1 = g 3) (hg.ne (by decide))
  · exact hws 0 5 2 4 (by decide) (by decide) (by decide) (by decide) (by linear_combination (-1/2) * h1 + (-1/2) * h2 + (1/2) * h4)

/- ## The lower bound, conditional on the Henning–Yeo theorem -/

/-- **Henning–Yeo** (Graphs Combin. 37 (2021) 867–890, Thm. 7), as used by Ma–Tang (Thm. 5.3),
specialised to vertex sets of reals: a linear 3-uniform hypergraph with no copy of `F₇` has a
transversal `T` with `17|T| ≤ 5n + 3m`. This is *not proved here*; it is a hypothesis of the
theorems below. Our version only asks for linear hypergraphs with no (not necessarily induced)
copy of `F₇`, so it follows from the published theorem under any reading of "subhypergraph". -/
def HenningYeoBound : Prop :=
  ∀ (V : Finset ℝ) (E : Finset (Finset ℝ)), (∀ e ∈ E, e ⊆ V ∧ e.card = 3) →
    (∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e ∩ f).card ≤ 1) → F7Free E →
    ∃ T ⊆ V, (∀ e ∈ E, ∃ x ∈ T, x ∈ e) ∧ 17 * T.card ≤ 5 * V.card + 3 * E.card

/-- Every `(4,5)`-set `A` has a Sidon subset of size at least `9|A|/17`, assuming Henning–Yeo
(Ma–Tang, arXiv:2602.23282, §5.2). -/
theorem isAdmissible_nine_seventeenths (hHY : HenningYeoBound) : IsAdmissible (9 / 17) := by
  intro A hA h45
  obtain ⟨F, rfl⟩ : ∃ F : Finset ℝ, (F : Set ℝ) = A := ⟨hA.toFinset, hA.coe_toFinset⟩
  have h : Is45 (F : Set ℝ) := h45
  obtain ⟨T, hTV, hcov, hbound⟩ := hHY F (apEdges F) (fun e he => apEdges_spec he)
    (apEdges_linear h) (apEdges_F7Free h)
  refine ⟨((F \ T : Finset ℝ) : Set ℝ), Finset.coe_subset.2 Finset.sdiff_subset, ?_, ?_⟩
  · apply isSidon_of_free h Finset.sdiff_subset
    intro x hx y hy z hz hxy hyz hs
    have hxF := Finset.sdiff_subset hx
    have hyF := Finset.sdiff_subset hy
    have hzF := Finset.sdiff_subset hz
    obtain ⟨w, hwT, hw⟩ := hcov {x, y, z} (mem_apEdges.2 ⟨x, y, z, hxF, hyF, hzF, hxy, hyz, hs, rfl⟩)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact (Finset.mem_sdiff.1 hx).2 hwT
    · exact (Finset.mem_sdiff.1 hy).2 hwT
    · exact (Finset.mem_sdiff.1 hz).2 hwT
  · rw [Set.ncard_coe_finset, Set.ncard_coe_finset, Finset.card_sdiff_of_subset hTV]
    have hm := card_apEdges_le h
    have hT : T.card ≤ F.card := Finset.card_le_card hTV
    rw [Nat.cast_sub hT]
    have h8 : ((17 * T.card : ℕ) : ℝ) ≤ ((8 * F.card : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 17 * T.card ≤ 8 * F.card)
    push_cast at h8
    linarith

/-- **Erdős #757, best known lower bound** (Ma–Tang): `9/17 ≤ sSup`, assuming Henning–Yeo. -/
theorem nine_seventeenths_le_sSup (hHY : HenningYeoBound) :
    9 / 17 ≤ sSup {c : ℝ | IsAdmissible c} :=
  le_csSup ⟨4 / 7, fun _ hc => FourSevenths.admissible_le hc⟩
    (isAdmissible_nine_seventeenths hHY)

/-- The upstream statement `erdos_757.variants.lowerBound` (`1/2 < sSup`), assuming
Henning–Yeo. -/
theorem erdos_757_lowerBound_of_henningYeo (hHY : HenningYeoBound) {_A : Set ℝ} :
    1 / (2 : ℝ) < sSup {c | IsAdmissible c} := by
  have := nine_seventeenths_le_sSup hHY
  linarith

/-- The wrapper has exactly the upstream type of `erdos_757.variants.lowerBound`, plus the
Henning–Yeo hypothesis. -/
example : HenningYeoBound → type_of% @Erdos757.erdos_757.variants.lowerBound :=
  @erdos_757_lowerBound_of_henningYeo

end OpenProblemsLab.E757.LowerBound
