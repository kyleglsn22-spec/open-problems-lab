import Lab.ListTotal.Counterexample

/-!
# List Total Colouring fails for every total chromatic number `k ≥ 4`

Noel (arXiv:2609.38417) disproved the List Total Colouring Conjecture with a cubic graph:
four copies of `K_{2,3}` joined pairwise by single *cross edges* (formalized in
`Lab/ListTotal/Counterexample.lean`). We generalize his construction to every maximum degree
`d ≥ 3` (here `d = n + 3`):

* blocks `B_0, …, B_d`, each a copy of `K_{d-1,d}`: block `i` has `d - 1` *private* vertices
  `(i, inl m)` and `d` *terminals* `(i, inr j)`, `j ≠ i`;
* terminal `(i, inr j)` is joined by a cross edge to terminal `(j, inr i)`.

The real graph is `d`-regular on `(d+1)(2d-1)` vertices. For simple indexing the type also contains
`d + 1` *dummy* vertices `(i, inr i)`, which are isolated and play no role.

Main results (`k = n + 4 = d + 1`):

* `degree_le`: every vertex has at most `d` neighbours;

* `totalChromaticNumber_G : (GN n).totalChromaticNumber = n + 4` (an explicit colouring; fewer
  colours fail because a private vertex and its `d` edges need `d + 1` colours);
* `not_totalChoosable : ¬ (GN n).TotalChoosable (n + 4)`;
* `exists_counterexample : ∀ k ≥ 4, ∃` a finite simple graph with maximum degree `≤ k - 1` and
  `χ'' = k` that is not totally `k`-choosable. So the List Total Colouring Conjecture fails for every value `k ≥ 4` of `χ''`
  (it is known to hold when the maximum degree is at most 2).

## The lists (colours `0, …, d + 1`)

Everything inside block `i` gets `{0, …, d+1} ∖ {i}`. The cross edge between blocks `p < q`
omits `om p q`, chosen so that every colour `t` is omitted by some cross edge `{p, q}` with
`t ∉ {p, q}`: `{t+1, t+2}` omits `t` for `t ≤ d - 2`, `{0, d}` omits `d - 1`, `{0, 1}` omits `d`,
and every other cross edge omits `d + 1` (e.g. `{0, 2}`).

## Proof

1. `priv_eq`: in a total colouring of `K_{d-1,d}` from `d + 1` colours all private vertices get
   the same colour `sᵢ`. (Each private vertex and its `d` edges use the whole palette. If two
   terminals shared a colour `g`, the `g`-edges of the `d - 1` private vertices would go to the
   other `d - 2` terminals injectively. So the `d` terminals get distinct colours, all different
   from every private colour; that forces one private colour.)
2. `block`: the cross edge leaving block `i` has colour `i` or `sᵢ` (the terminal and its `d - 1`
   block edges fill the palette minus `sᵢ`).
3. `star`: the sets `Sᵢ = {i, sᵢ}` (`d + 1 ≥ 4` of them) meet pairwise, so they share a colour `t`
   (two-element sets meeting pairwise form a star or lie in a triangle, and a triangle holds at most
   three indices `i`).
4. The cross edge `{p, q}` omitting `t` (with `t ∉ {p, q}`) then has `Sₚ ∩ S_q = {t}`, so it would
   need colour `t`, which its list lacks.
-/

namespace OpenProblemsLab.ListTotalGeneral

open Finset SimpleGraph
open OpenProblemsLab.ListTotal (ed tc_vv tc_ve_left tc_ve_right tc_ee tc_ee')

/-! ### Two filling lemmas -/

/-- An injective map from a type with at least `|P|` elements into `P` hits every element. -/
theorem fill {ι : Type*} [Fintype ι] {P : Finset ℕ} (f : ι → ℕ) (hf : Function.Injective f)
    (hP : ∀ i, f i ∈ P) (hc : P.card ≤ Fintype.card ι) {x : ℕ} (hx : x ∈ P) : ∃ i, f i = x := by
  have hsub : univ.image f ⊆ P := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := mem_image.1 hy
    exact hP i
  have heq := eq_of_subset_of_card_le hsub (by rw [card_image_of_injective _ hf, card_univ]; exact hc)
  rw [← heq] at hx
  obtain ⟨i, -, hi⟩ := mem_image.1 hx
  exact ⟨i, hi⟩

/-- The same, for a map avoiding one element `a ∈ P`. -/
theorem fill_erase {ι : Type*} [Fintype ι] {P : Finset ℕ} (f : ι → ℕ)
    (hf : Function.Injective f) (hP : ∀ i, f i ∈ P) (a : ℕ) (ha : a ∈ P) (hfa : ∀ i, f i ≠ a)
    (hc : P.card ≤ Fintype.card ι + 1) {x : ℕ} (hx : x ∈ P) (hxa : x ≠ a) : ∃ i, f i = x :=
  fill f hf (fun i => mem_erase.2 ⟨hfa i, hP i⟩) (by rw [card_erase_of_mem ha]; omega)
    (mem_erase.2 ⟨hxa, hx⟩)

/-! ### Step 1: the private vertices of `K_{d-1,d}` share a colour -/

/-- **Private vertices are monochromatic.** Private vertices `m : M`, terminals `j : T`
(`|T| = d`, `|M| ≥ d - 1`), all colours in a palette `P` of `d + 1` colours; `s`, `τ`, `e` are the
colours of private vertices, terminals and edges. -/
theorem priv_eq {M T : Type*} [Fintype M] [Fintype T] [DecidableEq T] {P : Finset ℕ}
    (hP : P.card = Fintype.card T + 1) (hM : Fintype.card T < Fintype.card M + 2)
    (s : M → ℕ) (τ : T → ℕ) (e : M → T → ℕ)
    (hs : ∀ m, s m ∈ P) (hτ : ∀ j, τ j ∈ P) (he : ∀ m j, e m j ∈ P)
    (h1 : ∀ m j, s m ≠ τ j) (h2 : ∀ m j, s m ≠ e m j) (h3 : ∀ m j, τ j ≠ e m j)
    (h4 : ∀ m j j', j ≠ j' → e m j ≠ e m j') (h5 : ∀ m m' j, m ≠ m' → e m j ≠ e m' j)
    (m m' : M) : s m = s m' := by
  classical
  have einj : ∀ m, Function.Injective (e m) := fun m j j' h => by
    by_contra hne
    exact h4 m j j' hne h
  have star : ∀ m g, g ∈ P → g ≠ s m → ∃ j, e m j = g := fun m g hg hgs =>
    fill_erase (e m) (einj m) (he m) (s m) (hs m) (fun j => (h2 m j).symm) (by omega) hg hgs
  have τinj : Function.Injective τ := by
    intro j1 j2 h12
    by_contra hne
    have hφ : ∀ m, ∃ j, e m j = τ j1 := fun m => star m _ (hτ j1) (h1 m j1).symm
    choose φ hφ using hφ
    have hinj : Set.InjOn φ (univ : Finset M) := fun a _ b _ h => by
      by_contra hab
      have hb : e b (φ a) = τ j1 := by rw [h]; exact hφ b
      exact h5 a b (φ a) hab ((hφ a).trans hb.symm)
    have hcard := card_le_card_of_injOn φ (s := univ) (t := (univ.erase j1).erase j2)
      (fun a _ => by
        refine mem_erase.2 ⟨?_, mem_erase.2 ⟨?_, mem_univ _⟩⟩
        · intro h
          exact h3 a j2 (by rw [← h12, ← hφ a, h])
        · intro h
          exact h3 a j1 (by rw [← hφ a, h])) hinj
    rw [card_univ, card_erase_of_mem (mem_erase.2 ⟨fun h => hne h.symm, mem_univ _⟩),
      card_erase_of_mem (mem_univ _), card_univ] at hcard
    have h2T := card_le_univ ({j1, j2} : Finset T)
    rw [card_pair hne] at h2T
    omega
  have himg : ∀ m, univ.image τ = P.erase (s m) := fun m =>
    eq_of_subset_of_card_le
      (fun y hy => by
        obtain ⟨j, -, rfl⟩ := mem_image.1 hy
        exact mem_erase.2 ⟨(h1 m j).symm, hτ j⟩)
      (by rw [card_erase_of_mem (hs m), card_image_of_injective _ τinj, card_univ]; omega)
  by_contra hne
  have hm : s m ∈ P.erase (s m') := mem_erase.2 ⟨hne, hs m⟩
  rw [← himg m', himg m] at hm
  simp at hm

/-! ### Step 2: the colour of a cross edge -/

/-- At a terminal of colour `τ` with block edges `e m` (`|M| = d - 1`) inside a palette `P` of
`d + 1` colours avoiding the private colour `s`, an edge of colour `x ∈ P ∪ {a}` avoiding all of
these has colour `a` or `s`. -/
theorem cross_in {M : Type*} [Fintype M] {P : Finset ℕ} (hP : P.card = Fintype.card M + 2)
    {a s τ x : ℕ} (e : M → ℕ) (hs : s ∈ P) (hτ : τ ∈ P) (he : ∀ m, e m ∈ P)
    (hsτ : s ≠ τ) (hse : ∀ m, s ≠ e m) (hτe : ∀ m, τ ≠ e m)
    (hee : ∀ m m', m ≠ m' → e m ≠ e m')
    (hx : x = a ∨ x ∈ P) (hxτ : x ≠ τ) (hxe : ∀ m, x ≠ e m) : x = a ∨ x = s := by
  rcases hx with hx | hx
  · exact Or.inl hx
  by_contra hne
  push Not at hne
  let f : Option M → ℕ := fun o => o.elim τ e
  have hf : Function.Injective f := by
    rintro (_ | m) (_ | m') h
    · rfl
    · exact absurd h (hτe m')
    · exact absurd h.symm (hτe m)
    · by_contra hne'
      exact hee m m' (fun h' => hne' (by rw [h'])) h
  obtain ⟨o, ho⟩ := fill_erase f hf (by rintro (_ | m); exacts [hτ, he m]) s hs
    (by rintro (_ | m); exacts [hsτ.symm, (hse m).symm]) (by rw [Fintype.card_option]; omega)
    hx hne.2
  rcases o with _ | m
  · exact hxτ ho.symm
  · exact hxe m ho.symm

/-! ### Step 3: pairwise meeting pairs `{i, sᵢ}` form a star -/

/-- If the sets `{i, sᵢ}` (`i = 0, …, n+3`, `sᵢ ≠ i`) meet pairwise, they have a common element. -/
theorem star {n : ℕ} (s : Fin (n + 4) → ℕ) (hs : ∀ i, s i ≠ (i : ℕ))
    (hC : ∀ i j : Fin (n + 4), (i : ℕ) = j ∨ s j = i ∨ s i = j ∨ s i = s j) :
    ∃ t : ℕ, ∀ x : Fin (n + 4), t = x ∨ t = s x := by
  have v0 : ((⟨0, by omega⟩ : Fin (n + 4)) : ℕ) = 0 := rfl
  by_cases h0 : ∀ x : Fin (n + 4), (0 : ℕ) = x ∨ 0 = s x
  · exact ⟨0, h0⟩
  by_cases h1 : ∀ x : Fin (n + 4), s ⟨0, by omega⟩ = x ∨ s ⟨0, by omega⟩ = s x
  · exact ⟨_, h1⟩
  exfalso
  push Not at h0 h1
  obtain ⟨y, hy1, hy2⟩ := h0
  obtain ⟨z, hz1, hz2⟩ := h1
  have a0 := hs ⟨0, by omega⟩
  have ay := hs y
  have az := hs z
  have c0y := hC ⟨0, by omega⟩ y
  have c0z := hC ⟨0, by omega⟩ z
  have cyz := hC y z
  have hz0 : (z : ℕ) ≠ 0 := fun e => hz2 (by rw [show z = ⟨0, by omega⟩ from Fin.ext e])
  have hyz : (y : ℕ) ≠ z := by
    intro e
    have : y = z := Fin.ext e
    subst this
    omega
  obtain ⟨e1, e2, e3⟩ : s ⟨0, by omega⟩ = y ∧ s y = z ∧ s z = 0 := by omega
  clear c0y c0z cyz hy1 hy2 hz1 hz2
  have key : ∀ x : Fin (n + 4), (x : ℕ) = 0 ∨ (x : ℕ) = y ∨ (x : ℕ) = z := fun x => by
    have := hC x ⟨0, by omega⟩
    have := hC x y
    have := hC x z
    have := hs x
    omega
  have k1 := key ⟨1, by omega⟩
  have k2 := key ⟨2, by omega⟩
  have k3 := key ⟨3, by omega⟩
  have v1 : ((⟨1, by omega⟩ : Fin (n + 4)) : ℕ) = 1 := rfl
  have v2 : ((⟨2, by omega⟩ : Fin (n + 4)) : ℕ) = 2 := rfl
  have v3 : ((⟨3, by omega⟩ : Fin (n + 4)) : ℕ) = 3 := rfl
  omega

/-! ### The graph -/

/-- Vertices: `(i, inl m)` is private vertex `m` of block `i`; `(i, inr j)` (`j ≠ i`) is the
terminal of block `i` pointing to block `j`; `(i, inr i)` is an isolated dummy. -/
abbrev V (n : ℕ) := Fin (n + 4) × (Fin (n + 2) ⊕ Fin (n + 4))

/-- Adjacency: private–terminal inside a block, and the cross edges `(i, inr j) – (j, inr i)`. -/
def gAdj (n : ℕ) : V n → V n → Prop
  | (_, .inl _), (_, .inl _) => False
  | (i, .inl _), (i', .inr j) => i = i' ∧ j ≠ i
  | (i, .inr j), (i', .inl _) => i = i' ∧ j ≠ i
  | (i, .inr j), (i', .inr j') => j = i' ∧ j' = i ∧ i ≠ i'

/-- The generalized Noel graph (maximum degree `n + 3`). -/
def GN (n : ℕ) : SimpleGraph (V n) where
  Adj := gAdj n
  symm := by
    refine ⟨?_⟩
    rintro ⟨i, a | j⟩ ⟨i', b | j'⟩ h <;> simp only [gAdj] at h ⊢
    · obtain ⟨rfl, h⟩ := h
      exact ⟨rfl, h⟩
    · obtain ⟨rfl, h⟩ := h
      exact ⟨rfl, h⟩
    · exact ⟨h.2.1, h.1, fun e => h.2.2 e.symm⟩
  loopless := by
    refine ⟨?_⟩
    rintro ⟨i, a | j⟩ h <;> simp [gAdj] at h

instance (n : ℕ) : DecidableRel (GN n).Adj := fun u v => by
  change Decidable (gAdj n u v)
  rcases u with ⟨i, a | j⟩ <;> rcases v with ⟨i', b | j'⟩ <;> dsimp only [gAdj] <;>
    infer_instance

theorem adj_pt {n : ℕ} (i : Fin (n + 4)) (m : Fin (n + 2)) (j : Fin (n + 4)) (h : j ≠ i) :
    (GN n).Adj (i, .inl m) (i, .inr j) := by
  simp [GN, gAdj, h]

theorem adj_cross {n : ℕ} (i j : Fin (n + 4)) (h : i ≠ j) :
    (GN n).Adj (i, .inr j) (j, .inr i) := by
  simp [GN, gAdj, h]

/-- Every vertex has at most `n + 3` neighbours (so the maximum degree is `d = n + 3`; it is
exactly `d`, since `χ'' = d + 1` forces a vertex of degree `≥ d`). -/
theorem degree_le (n : ℕ) (v : V n) : (univ.filter ((GN n).Adj v)).card ≤ n + 3 := by
  rcases v with ⟨i, m | j⟩
  · calc _ ≤ ((univ.erase i).image (fun j => ((i, .inr j) : V n))).card := card_le_card ?_
      _ ≤ (univ.erase i).card := card_image_le
      _ = n + 3 := by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega
    rintro ⟨i', b | j'⟩ hw <;> have h := (mem_filter.1 hw).2 <;>
      simp only [GN, gAdj] at h
    obtain ⟨rfl, h⟩ := h
    exact mem_image.2 ⟨j', mem_erase.2 ⟨h, mem_univ _⟩, rfl⟩
  · calc _ ≤ (insert ((j, .inr i) : V n) (univ.image (fun m => ((i, .inl m) : V n)))).card :=
          card_le_card ?_
      _ ≤ (univ.image (fun m => ((i, .inl m) : V n))).card + 1 := card_insert_le _ _
      _ ≤ (univ : Finset (Fin (n + 2))).card + 1 := Nat.add_le_add_right card_image_le 1
      _ = n + 3 := by simp
    rintro ⟨i', b | j'⟩ hw <;> have h := (mem_filter.1 hw).2 <;>
      simp only [GN, gAdj] at h
    · obtain ⟨rfl, -⟩ := h
      exact mem_insert_of_mem (mem_image.2 ⟨b, mem_univ _, rfl⟩)
    · obtain ⟨rfl, rfl, -⟩ := h
      exact mem_insert_self _ _

/-! ### The lists -/

/-- The colour omitted by the cross edge between blocks `a` and `b` (`d = n + 3`). -/
def om (n a b : ℕ) : ℕ :=
  if 1 ≤ min a b ∧ max a b = min a b + 1 then min a b - 1
  else if min a b = 0 ∧ max a b = n + 3 then n + 2
  else if min a b = 0 ∧ max a b = 1 then n + 3
  else n + 4

theorem om_symm (n a b : ℕ) : om n a b = om n b a := by
  unfold om
  rw [min_comm, max_comm]

theorem om_lt (n a b : ℕ) (hb : max a b < n + 4) : om n a b < n + 5 := by
  unfold om
  split_ifs <;> omega

/-- List of the edge `uv`. -/
def eL (n : ℕ) (u v : V n) : Finset ℕ :=
  if u.1 = v.1 then (range (n + 5)).erase u.1 else (range (n + 5)).erase (om n u.1 v.1)

theorem eL_symm (n : ℕ) (u v : V n) : eL n u v = eL n v u := by
  unfold eL
  by_cases h : u.1 = v.1
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h), om_symm]

/-- The bad list assignment, from the colours `0, …, n + 4`. -/
def L (n : ℕ) : V n ⊕ (GN n).edgeSet → Finset ℕ
  | .inl v => (range (n + 5)).erase v.1
  | .inr e => Sym2.lift ⟨eL n, eL_symm n⟩ e.val

theorem card_L (n : ℕ) : ∀ x, n + 4 ≤ (L n x).card := by
  rintro (v | ⟨e, he⟩)
  · simp only [L]
    rw [card_erase_of_mem (by simp; omega), card_range]
    omega
  · induction e using Sym2.ind with
    | _ u v =>
      show n + 4 ≤ (eL n u v).card
      unfold eL
      split_ifs
      · rw [card_erase_of_mem (by simp; omega), card_range]
        omega
      · rw [card_erase_of_mem (by simp; exact om_lt n _ _ (by omega)), card_range]
        omega

/-! ### No total colouring from the lists -/

/-- Two edges at a common vertex `u`, with `u` second in both. -/
theorem tc_ee_right {W : Type*} [DecidableEq W] {H : SimpleGraph W} {ι : Type*}
    {c : W ⊕ H.edgeSet → ι} (hc : H.IsTotalColoring c) {u v w : W} (h₁ : H.Adj v u)
    (h₂ : H.Adj w u) (hvw : v ≠ w) : c (Sum.inr (ed H h₁)) ≠ c (Sum.inr (ed H h₂)) := by
  have e1 : ed H h₁ = ed H h₁.symm := Subtype.ext Sym2.eq_swap
  have e2 : ed H h₂ = ed H h₂.symm := Subtype.ext Sym2.eq_swap
  rw [e1, e2]
  exact tc_ee hc h₁.symm h₂.symm hvw

theorem card_ne (n : ℕ) (i : Fin (n + 4)) : Fintype.card {j : Fin (n + 4) // j ≠ i} = n + 3 := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  omega

section Main

variable {n : ℕ} {c : V n ⊕ (GN n).edgeSet → ℕ} (hc : (GN n).IsTotalColoring c)
  (hL : ∀ x, c x ∈ L n x)
include hc hL

/-- **Block lemma.** The cross edge leaving block `i` towards block `j` has colour `i` or the
(common) private colour of block `i`. -/
theorem block (i j : Fin (n + 4)) (hij : i ≠ j) :
    c (.inr (ed (GN n) (adj_cross i j hij))) = i ∨
      c (.inr (ed (GN n) (adj_cross i j hij))) = c (.inl (i, .inl 0)) := by
  have hP : ((range (n + 5)).erase (i : ℕ)).card = n + 4 := by
    rw [card_erase_of_mem (by simp; omega), card_range]
    omega
  have vs : ∀ m, c (.inl (i, .inl m)) ∈ (range (n + 5)).erase (i : ℕ) := fun m => hL (.inl (i, .inl m))
  have vt : ∀ j, c (.inl (i, .inr j)) ∈ (range (n + 5)).erase (i : ℕ) := fun j => hL (.inl (i, .inr j))
  have ve : ∀ m j (h : j ≠ i), c (.inr (ed (GN n) (adj_pt i m j h))) ∈
      (range (n + 5)).erase (i : ℕ) := fun m j h => by
    have hl : c (.inr (ed (GN n) (adj_pt i m j h))) ∈ eL n (i, .inl m) (i, .inr j) := hL _
    simpa [eL] using hl
  have priv : ∀ m, c (.inl (i, .inl m)) = c (.inl (i, .inl 0)) := fun m =>
    priv_eq (M := Fin (n + 2)) (T := {j : Fin (n + 4) // j ≠ i})
      (P := (range (n + 5)).erase (i : ℕ)) (by rw [hP, card_ne]) (by rw [card_ne, Fintype.card_fin]; omega)
      (fun m => c (.inl (i, .inl m))) (fun j => c (.inl (i, .inr j.1)))
      (fun m j => c (.inr (ed (GN n) (adj_pt i m j.1 j.2)))) vs (fun j => vt j.1)
      (fun m j => ve m j.1 j.2) (fun m j => tc_vv hc (adj_pt i m j.1 j.2))
      (fun m j => tc_ve_left hc (adj_pt i m j.1 j.2))
      (fun m j => tc_ve_right hc (adj_pt i m j.1 j.2))
      (fun m j j' h => tc_ee hc (adj_pt i m j.1 j.2) (adj_pt i m j'.1 j'.2) (fun e => h (Subtype.ext
        (Sum.inr_injective (congrArg Prod.snd e)))))
      (fun m m' j h => tc_ee_right hc (adj_pt i m j.1 j.2) (adj_pt i m' j.1 j.2)
        (fun e => h (Sum.inl_injective (congrArg Prod.snd e))))
      m 0
  have hx : c (.inr (ed (GN n) (adj_cross i j hij))) = i ∨
      c (.inr (ed (GN n) (adj_cross i j hij))) ∈ (range (n + 5)).erase (i : ℕ) := by
    have hl : c (.inr (ed (GN n) (adj_cross i j hij))) ∈ eL n (i, .inr j) (j, .inr i) := hL _
    simp only [eL] at hl
    rw [if_neg hij] at hl
    by_cases h : c (.inr (ed (GN n) (adj_cross i j hij))) = i
    · exact Or.inl h
    · exact Or.inr (mem_erase.2 ⟨h, mem_of_mem_erase hl⟩)
  refine cross_in (M := Fin (n + 2)) (by rw [hP, Fintype.card_fin])
    (fun m => c (.inr (ed (GN n) (adj_pt i m j (Ne.symm hij))))) (vs 0) (vt j)
    (fun m => ve m j (Ne.symm hij)) (tc_vv hc (adj_pt i 0 j (Ne.symm hij)))
    (fun m => by rw [← priv m]; exact tc_ve_left hc (adj_pt i m j (Ne.symm hij)))
    (fun m => tc_ve_right hc (adj_pt i m j (Ne.symm hij)))
    (fun m m' h => tc_ee_right hc (adj_pt i m j (Ne.symm hij)) (adj_pt i m' j (Ne.symm hij))
      (fun e => h (Sum.inl_injective (congrArg Prod.snd e))))
    hx (tc_ve_left hc (adj_cross i j hij)).symm
    (fun m => (tc_ee' hc (adj_pt i m j (Ne.symm hij)) (adj_cross i j hij)
      (fun e => Sum.inl_ne_inr (congrArg Prod.snd e))).symm)

end Main

/-- **No total colouring from the lists `L n`.** -/
theorem no_coloring {n : ℕ} (c : V n ⊕ (GN n).edgeSet → ℕ) (hc : (GN n).IsTotalColoring c)
    (hL : ∀ x, c x ∈ L n x) : False := by
  set s : Fin (n + 4) → ℕ := fun i => c (.inl (i, .inl 0)) with hs_def
  have hsP : ∀ i : Fin (n + 4), s i ∈ (range (n + 5)).erase (i : ℕ) := fun i => hL (.inl (i, .inl 0))
  have cross : ∀ p q : Fin (n + 4), p ≠ q →
      ∃ x : ℕ, (x = (p : ℕ) ∨ x = s p) ∧ (x = (q : ℕ) ∨ x = s q) ∧ x ≠ om n p q := fun p q hpq => by
    refine ⟨c (.inr (ed (GN n) (adj_cross p q hpq))), block hc hL p q hpq, ?_, ?_⟩
    · have he : ed (GN n) (adj_cross p q hpq) = ed (GN n) (adj_cross q p (Ne.symm hpq)) :=
        Subtype.ext Sym2.eq_swap
      rw [he]
      exact block hc hL q p (Ne.symm hpq)
    · have hl : c (.inr (ed (GN n) (adj_cross p q hpq))) ∈ eL n (p, .inr q) (q, .inr p) := hL _
      simp only [eL] at hl
      rw [if_neg hpq] at hl
      exact (mem_erase.1 hl).1
  have hs : ∀ i : Fin (n + 4), s i ≠ (i : ℕ) := fun i => (mem_erase.1 (hsP i)).1
  have hC : ∀ i j : Fin (n + 4), (i : ℕ) = j ∨ s j = i ∨ s i = j ∨ s i = s j := fun i j => by
    by_cases h : i = j
    · left
      rw [h]
    obtain ⟨x, h1, h2, -⟩ := cross i j h
    have : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    omega
  obtain ⟨t, ht⟩ := star s hs hC
  have tlt : t < n + 5 := by
    rcases ht ⟨0, by omega⟩ with h | h
    · rw [h]; simp
    · have := (mem_erase.1 (hsP ⟨0, by omega⟩)).2
      rw [mem_range] at this
      omega
  have fin : ∀ p q : Fin (n + 4), p ≠ q → om n p q = t → t ≠ p → t ≠ q → False :=
    fun p q hpq hom htp htq => by
      obtain ⟨x, h1, h2, h3⟩ := cross p q hpq
      have := ht p
      have := ht q
      have : (p : ℕ) ≠ q := fun e => hpq (Fin.ext e)
      omega
  rcases (by omega : t ≤ n + 1 ∨ t = n + 2 ∨ t = n + 3 ∨ t = n + 4) with h | h | h | h
  · refine fin ⟨t + 1, by omega⟩ ⟨t + 2, by omega⟩
      (fun e => by have := congrArg Fin.val e; dsimp only at this; omega) ?_
      (by dsimp only; omega) (by dsimp only; omega)
    dsimp only
    unfold om
    rw [min_eq_left (by omega), max_eq_right (by omega)]
    split_ifs <;> omega
  · refine fin ⟨0, by omega⟩ ⟨n + 3, by omega⟩
      (fun e => by have := congrArg Fin.val e; dsimp only at this; omega) ?_
      (by dsimp only; omega) (by dsimp only; omega)
    dsimp only
    unfold om
    rw [min_eq_left (by omega), max_eq_right (by omega)]
    split_ifs <;> omega
  · refine fin ⟨0, by omega⟩ ⟨1, by omega⟩
      (fun e => by have := congrArg Fin.val e; dsimp only at this; omega) ?_
      (by dsimp only; omega) (by dsimp only; omega)
    dsimp only
    unfold om
    rw [min_eq_left (by omega), max_eq_right (by omega)]
    split_ifs <;> omega
  · refine fin ⟨0, by omega⟩ ⟨2, by omega⟩
      (fun e => by have := congrArg Fin.val e; dsimp only at this; omega) ?_
      (by dsimp only; omega) (by dsimp only; omega)
    dsimp only
    unfold om
    rw [min_eq_left (by omega), max_eq_right (by omega)]
    split_ifs <;> omega

/-- The generalized Noel graph is not totally `(n + 4)`-choosable. -/
theorem not_totalChoosable (n : ℕ) : ¬ (GN n).TotalChoosable (n + 4) := by
  intro h
  obtain ⟨c, hcL, hc⟩ := h (L n) (card_L n)
  exact no_coloring c hc hcL

/-! ### A total colouring with `n + 4` colours -/

section Ring

open Fin.CommRing

/-- Position of `j` among the indices `≠ i`. -/
def rk (i j : ℕ) : ℕ := if j < i then j else j - 1

/-- Terminal colour (in `ℤ / (n + 3)`): row `i` is a cyclic shift of the positions. -/
def Mc (n i j : ℕ) : Fin (n + 3) := (rk i j : Fin (n + 3)) + (i : Fin (n + 3))

/-- Colour of the edge from private vertex `m` to terminal `(i, inr j)`. -/
def pe (n i m j : ℕ) : Fin (n + 3) := Mc n i j + ((m + 1 : ℕ) : Fin (n + 3))

theorem castF {n a : ℕ} (h : a < n + 3) : ((a : Fin (n + 3)) : ℕ) = a := by
  rw [Fin.val_natCast, Nat.mod_eq_of_lt h]

theorem rk_lt {n : ℕ} (i j : Fin (n + 4)) (h : j ≠ i) : rk i j < n + 3 := by
  have : (j : ℕ) ≠ (i : ℕ) := fun e => h (Fin.ext e)
  have := i.isLt
  have := j.isLt
  unfold rk
  split_ifs <;> omega

theorem Mc_cross {n : ℕ} {i j : Fin (n + 4)} (hij : i ≠ j) : Mc n i j ≠ Mc n j i := by
  have hne : (i : ℕ) ≠ (j : ℕ) := fun e => hij (Fin.ext e)
  unfold Mc rk
  rcases lt_or_gt_of_ne hne with h | h
  · rw [if_neg (by omega), if_pos h]
    intro e
    rw [Nat.cast_sub (by omega), Nat.cast_one] at e
    have : (1 : Fin (n + 3)) = 0 := by linear_combination -e
    exact one_ne_zero this
  · rw [if_pos h, if_neg (by omega)]
    intro e
    rw [Nat.cast_sub (by omega), Nat.cast_one] at e
    have : (1 : Fin (n + 3)) = 0 := by linear_combination e
    exact one_ne_zero this

theorem Mc_row {n : ℕ} {i j j' : Fin (n + 4)} (hj : j ≠ i) (hj' : j' ≠ i) (hjj : j ≠ j') :
    Mc n i j ≠ Mc n i j' := by
  intro e
  have h := congrArg Fin.val (add_right_cancel e)
  rw [castF (rk_lt i j hj), castF (rk_lt i j' hj')] at h
  have : (j : ℕ) ≠ (j' : ℕ) := fun e => hjj (Fin.ext e)
  have : (j : ℕ) ≠ (i : ℕ) := fun e => hj (Fin.ext e)
  have : (j' : ℕ) ≠ (i : ℕ) := fun e => hj' (Fin.ext e)
  unfold rk at h
  split_ifs at h <;> omega

theorem pe_ne_Mc {n i j : ℕ} (m : Fin (n + 2)) : pe n i m j ≠ Mc n i j := by
  intro h
  unfold pe at h
  have h2 := add_left_cancel (h.trans (add_zero _).symm)
  have h3 := congrArg Fin.val h2
  rw [castF (by omega)] at h3
  simp at h3

theorem pe_row {n : ℕ} {i j j' : Fin (n + 4)} (m : ℕ) (hj : j ≠ i) (hj' : j' ≠ i)
    (hjj : j ≠ j') : pe n i m j ≠ pe n i m j' := fun e => Mc_row hj hj' hjj (add_right_cancel e)

theorem pe_col {n i j : ℕ} {m m' : Fin (n + 2)} (h : m ≠ m') : pe n i m j ≠ pe n i m' j := by
  intro e
  have h2 := congrArg Fin.val (add_left_cancel e)
  rw [castF (by omega), castF (by omega)] at h2
  exact h (Fin.ext (by omega))

end Ring

/-- Vertex colours: private vertices get the top colour `n + 3`. -/
def colV (n : ℕ) : V n → Fin (n + 4)
  | (_, .inl _) => Fin.last _
  | (i, .inr j) => (Mc n i j).castSucc

/-- Edge colours: cross edges get the top colour `n + 3`. -/
def colE (n : ℕ) : V n → V n → Fin (n + 4)
  | (_, .inl _), (_, .inl _) => Fin.last _
  | (i, .inl m), (_, .inr j) => (pe n i m j).castSucc
  | (_, .inr j), (i, .inl m) => (pe n i m j).castSucc
  | (_, .inr _), (_, .inr _) => Fin.last _

theorem colE_symm (n : ℕ) (u v : V n) : colE n u v = colE n v u := by
  rcases u with ⟨i, a | j⟩ <;> rcases v with ⟨i', b | j'⟩ <;> rfl

theorem col_vv {n : ℕ} (u v : V n) (h : gAdj n u v) : colV n u ≠ colV n v := by
  rcases u with ⟨i, a | j⟩ <;> rcases v with ⟨i', b | j'⟩ <;> simp only [gAdj] at h <;>
    simp only [colV]
  · exact (Fin.castSucc_lt_last _).ne'
  · exact (Fin.castSucc_lt_last _).ne
  · obtain ⟨h1, h2, hne⟩ := h
    subst h1 h2
    intro e
    exact Mc_cross hne (Fin.castSucc_injective _ e)

theorem col_ve {n : ℕ} (u v : V n) (h : gAdj n u v) : colV n u ≠ colE n u v := by
  rcases u with ⟨i, a | j⟩ <;> rcases v with ⟨i', b | j'⟩ <;> simp only [gAdj] at h <;>
    simp only [colV, colE]
  · exact (Fin.castSucc_lt_last _).ne'
  · obtain ⟨h1, -⟩ := h
    subst h1
    intro e
    exact pe_ne_Mc b (Fin.castSucc_injective _ e).symm
  · exact (Fin.castSucc_lt_last _).ne

theorem col_ee {n : ℕ} (u v w : V n) (h1 : gAdj n u v) (h2 : gAdj n u w) (hvw : v ≠ w) :
    colE n u v ≠ colE n u w := by
  rcases u with ⟨i, a | j⟩ <;> rcases v with ⟨i1, b1 | j1⟩ <;> rcases w with ⟨i2, b2 | j2⟩ <;>
    simp only [gAdj] at h1 h2 <;> simp only [colE]
  · obtain ⟨rfl, hj1⟩ := h1
    obtain ⟨rfl, hj2⟩ := h2
    have hj : j1 ≠ j2 := fun e => hvw (by rw [e])
    intro e
    exact pe_row a hj1 hj2 hj (Fin.castSucc_injective _ e)
  · obtain ⟨rfl, -⟩ := h1
    obtain ⟨rfl, -⟩ := h2
    have hb : b1 ≠ b2 := fun e => hvw (by rw [e])
    intro e
    exact pe_col hb (Fin.castSucc_injective _ e)
  · exact (Fin.castSucc_lt_last _).ne
  · exact (Fin.castSucc_lt_last _).ne'
  · obtain ⟨rfl, rfl, -⟩ := h1
    obtain ⟨rfl, rfl, -⟩ := h2
    exact absurd rfl hvw

/-- The total `(n + 4)`-colouring. -/
def colT (n : ℕ) : V n ⊕ (GN n).edgeSet → Fin (n + 4)
  | .inl v => colV n v
  | .inr e => Sym2.lift ⟨colE n, colE_symm n⟩ e.val

theorem colT_edge {n : ℕ} {u v : V n} (e : (GN n).edgeSet) (he : e.val = s(u, v)) :
    colT n (.inr e) = colE n u v := by
  simp only [colT, he, Sym2.lift_mk]

theorem isTotalColoring_colT (n : ℕ) : (GN n).IsTotalColoring (colT n) := by
  refine ⟨fun u v h => col_vv u v h, ?_, ?_⟩
  · rintro ⟨e, he⟩ ⟨f, hf⟩ hef ⟨v, hve, hvf⟩
    obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.1 hve
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 hvf
    have hx : gAdj n v x := he
    have hy : gAdj n v y := hf
    rw [colT_edge _ rfl, colT_edge _ rfl]
    refine col_ee v x y hx hy ?_
    rintro rfl
    exact hef rfl
  · rintro v ⟨e, he⟩ hve
    obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.1 hve
    have hx : gAdj n v x := he
    rw [colT_edge _ rfl]
    exact col_ve v x hx

theorem totalColorable (n : ℕ) : (GN n).TotalColorable (n + 4) :=
  ⟨colT n, isTotalColoring_colT n⟩

/-- Fewer colours fail: private vertex `(0, inl 0)` and its `n + 3` edges need `n + 4` colours. -/
theorem not_totalColorable_of_lt (n : ℕ) {k : ℕ} (hk : k < n + 4) : ¬ (GN n).TotalColorable k := by
  rintro ⟨c, hc⟩
  let f : Fin (n + 4) → Fin k := fun j =>
    if h : j = 0 then c (.inl (0, .inl 0)) else c (.inr (ed (GN n) (adj_pt 0 0 j h)))
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : x = 0 <;> by_cases hy : y = 0
    · rw [hx, hy]
    · simp only [f, dif_pos hx, dif_neg hy] at hxy
      exact absurd hxy (tc_ve_left hc _)
    · simp only [f, dif_neg hx, dif_pos hy] at hxy
      exact absurd hxy.symm (tc_ve_left hc _)
    · simp only [f, dif_neg hx, dif_neg hy] at hxy
      by_contra hne
      exact tc_ee hc _ _ (fun e => hne (Sum.inr_injective (congrArg Prod.snd e))) hxy
  have := Fintype.card_le_of_injective f hf
  simp at this
  omega

theorem totalChromaticNumber_G (n : ℕ) : (GN n).totalChromaticNumber = n + 4 := by
  apply le_antisymm (Nat.sInf_le (totalColorable n))
  apply le_csInf ⟨n + 4, totalColorable n⟩
  intro k hk
  by_contra h
  exact not_totalColorable_of_lt n (by omega) hk

theorem listTotalChromaticNumber_G_ne (n : ℕ) : (GN n).listTotalChromaticNumber ≠ n + 4 := by
  intro h
  have hne : {k | (GN n).TotalChoosable k}.Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty] at he
    simp [SimpleGraph.listTotalChromaticNumber, he] at h
  have := Nat.sInf_mem hne
  rw [show sInf {k | (GN n).TotalChoosable k} = n + 4 from h] at this
  exact not_totalChoosable n this

/-- **List Total Colouring fails for every total chromatic number `k ≥ 4`:** there is a finite
simple graph with `χ''(G) = k` that is not totally `k`-choosable. -/
theorem exists_counterexample (k : ℕ) (hk : 4 ≤ k) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W)
      (_ : DecidableRel H.Adj),
      (∀ v, (univ.filter (H.Adj v)).card ≤ k - 1) ∧
      H.totalChromaticNumber = k ∧ ¬ H.TotalChoosable k ∧
      H.listTotalChromaticNumber ≠ H.totalChromaticNumber := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 4 := ⟨k - 4, by omega⟩
  refine ⟨V n, inferInstance, inferInstance, GN n, inferInstance,
    fun v => (degree_le n v).trans (by omega), totalChromaticNumber_G n,
    not_totalChoosable n, ?_⟩
  rw [totalChromaticNumber_G n]
  exact listTotalChromaticNumber_G_ne n

/-- In particular the List Total Colouring Conjecture is false (again). -/
theorem not_listTotalColouringConjecture :
    ¬ OpenProblemsLab.ListTotal.ListTotalColouringConjecture := by
  intro h
  have := h (V 0) (GN 0)
  rw [totalChromaticNumber_G 0] at this
  exact listTotalChromaticNumber_G_ne 0 this

end OpenProblemsLab.ListTotalGeneral
