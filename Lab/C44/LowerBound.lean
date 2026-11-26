import Mathlib

/-!
# Constant C44: the lower bound `3/2` (Chiarelli–Hatami–Saks construction)

For a Boolean function `f`, `deg f` is the degree of its multilinear polynomial over `ℝ`
(inputs and output read as `0/1`), and a variable is relevant if flipping it changes `f`
somewhere. `C44` is the least `C` with `#relevant(f) ≤ C · 2^(deg f)` for all `f`
(Tao's optimization-constants table, constant 44a).

We formalize the construction `Ξ_d` of Chiarelli, Hatami and Saks
(arXiv:1801.08564, Section 3): a Boolean function of degree at most `d` on
`3 · 2^(d-1) - 2` variables, all relevant. Consequently any admissible `C` is `≥ 3/2`.

`DegLE f d` says that `f` (as a `0/1`-valued real function) is a real linear combination
of monomials `∏_{i ∈ S} x_i` with `|S| ≤ d`. By uniqueness of the multilinear
representation this is exactly `deg f ≤ d`.
-/

set_option linter.unusedSectionVars false

namespace OpenProblemsLab.C44

open Finset

section Defs

variable {ι : Type*}

/-- `0/1` reading of a bit. -/
def bv (b : Bool) : ℝ := if b then 1 else 0

/-- The multilinear monomial `∏_{i ∈ S} x_i` on `{0,1}^ι`. -/
def mono (S : Finset ι) (x : ι → Bool) : ℝ := ∏ i ∈ S, bv (x i)

/-- Real functions on the cube spanned by monomials of size at most `d`. -/
def P (ι : Type*) (d : ℕ) : Submodule ℝ ((ι → Bool) → ℝ) :=
  Submodule.span ℝ {g | ∃ S : Finset ι, S.card ≤ d ∧ g = mono S}

/-- `f` has real degree at most `d`. -/
def DegLE (f : (ι → Bool) → Bool) (d : ℕ) : Prop := (fun x => bv (f x)) ∈ P ι d

/-- Flip coordinate `i`. -/
def flip [DecidableEq ι] (x : ι → Bool) (i : ι) : ι → Bool := Function.update x i (!x i)

/-- Variable `i` is relevant for `f`. -/
def Relevant [DecidableEq ι] (f : (ι → Bool) → Bool) (i : ι) : Prop := ∃ x, f (flip x i) ≠ f x

end Defs

section Span

variable {ι : Type*} [DecidableEq ι]

lemma bv_mul_self (b : Bool) : bv b * bv b = bv b := by cases b <;> simp [bv]

lemma mono_mul (S T : Finset ι) : mono S * mono T = mono (S ∪ T) := by
  funext x
  simp only [Pi.mul_apply, mono]
  rw [← Finset.prod_union_inter]
  have hsub : S ∩ T ⊆ S ∪ T := fun i hi => Finset.mem_union_left _ (Finset.mem_inter.1 hi).1
  rw [← Finset.prod_sdiff hsub, mul_assoc, ← Finset.prod_mul_distrib]
  simp [bv_mul_self]

lemma P_mono {a b : ℕ} (h : a ≤ b) : P ι a ≤ P ι b := by
  apply Submodule.span_mono
  rintro g ⟨S, hS, rfl⟩
  exact ⟨S, hS.trans h, rfl⟩

lemma mono_mem_P (S : Finset ι) : mono S ∈ P ι S.card :=
  Submodule.subset_span ⟨S, le_rfl, rfl⟩

lemma one_mem_P (d : ℕ) : (1 : (ι → Bool) → ℝ) ∈ P ι d := by
  have : (1 : (ι → Bool) → ℝ) = mono ∅ := by funext x; simp [mono]
  rw [this]; exact P_mono (Nat.zero_le _) (mono_mem_P ∅)

lemma var_mem_P (i : ι) : (fun x : ι → Bool => bv (x i)) ∈ P ι 1 := by
  have : (fun x : ι → Bool => bv (x i)) = mono {i} := by funext x; simp [mono]
  rw [this]; simpa using mono_mem_P (ι := ι) {i}

lemma mul_mem_P {a b : ℕ} {f g : (ι → Bool) → ℝ} (hf : f ∈ P ι a) (hg : g ∈ P ι b) :
    f * g ∈ P ι (a + b) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨S, hS, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨T, hT, rfl⟩ := hg
      rw [mono_mul]
      exact P_mono ((Finset.card_union_le S T).trans (Nat.add_le_add hS hT)) (mono_mem_P _)
    | zero => simp
    | add g₁ g₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
    | smul c g _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => simp
  | add f₁ f₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
  | smul c f _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

/-- Pulling back along an injective renaming of variables preserves degree. -/
lemma comp_mem_P {κ : Type*} [DecidableEq κ] (e : κ → ι) (he : Function.Injective e) {d : ℕ}
    {g : (κ → Bool) → ℝ} (hg : g ∈ P κ d) : (fun x : ι → Bool => g (x ∘ e)) ∈ P ι d := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨S, hS, rfl⟩ := hg
    have : (fun x : ι → Bool => mono S (x ∘ e)) = mono (S.image e) := by
      funext x; simp [mono, Finset.prod_image (fun a _ b _ h => he h)]
    rw [this]
    exact P_mono ((Finset.card_image_le).trans hS) (mono_mem_P _)
  | zero => exact Submodule.zero_mem _
  | add f₁ f₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
  | smul c f _ h => exact Submodule.smul_mem _ c h

end Span

/-- `±1` reading of a bit (`false ↦ 1`, `true ↦ -1`). -/
def pm (b : Bool) : ℝ := 1 - 2 * bv b

lemma degLE_iff_pm {ι : Type*} [DecidableEq ι] (f : (ι → Bool) → Bool) (d : ℕ) :
    DegLE f d ↔ (fun x => pm (f x)) ∈ P ι d := by
  have h1 : (fun x => pm (f x)) = (1 : (ι → Bool) → ℝ) - (2 : ℝ) • (fun x => bv (f x)) := by
    funext x; simp [pm]
  have h2 : (fun x => bv (f x)) = ((1 : ℝ) / 2) • ((1 : (ι → Bool) → ℝ) - fun x => pm (f x)) := by
    funext x
    simp only [pm, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul]
    ring
  constructor
  · intro h; rw [h1]; exact sub_mem (one_mem_P d) (Submodule.smul_mem _ _ h)
  · intro h; unfold DegLE; rw [h2]; exact Submodule.smul_mem _ _ (sub_mem (one_mem_P d) h)

/-! ## The construction -/

/-- Variable sets: `X 0` has one variable; `X (k+1)` has two control bits `s, t`
(`inl false`, `inl true`) and two copies of `X k`. -/
abbrev X : ℕ → Type
  | 0 => Unit
  | k + 1 => Bool ⊕ (Bool × X k)

instance instDecEqX : (k : ℕ) → DecidableEq (X k)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | k + 1 => @instDecidableEqSum _ _ _ (@instDecidableEqProd _ _ _ (instDecEqX k))

instance instFintypeX : (k : ℕ) → Fintype (X k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 => @instFintypeSum _ _ _ (@instFintypeProd _ _ _ (instFintypeX k))

lemma card_X : ∀ k : ℕ, Fintype.card (X k) + 2 = 3 * 2 ^ k
  | 0 => rfl
  | k + 1 => by
    have ih := card_X k
    have : Fintype.card (X (k + 1)) = 2 + 2 * Fintype.card (X k) := by
      show Fintype.card (Bool ⊕ (Bool × X k)) = _
      simp [Fintype.card_sum, Fintype.card_prod]
    rw [this, pow_succ]; omega

/-- Embedding of copy `c` of `X k` into `X (k+1)`. -/
def emb (k : ℕ) (c : Bool) : X k → X (k + 1) := fun v => Sum.inr (c, v)

lemma emb_injective (k : ℕ) (c : Bool) : Function.Injective (emb k c) := by
  intro a b h
  have h' : ((c, a) : Bool × X k) = (c, b) := Sum.inr_injective h
  exact (Prod.ext_iff.1 h').2

/-- The Chiarelli–Hatami–Saks function: `Ξ (k+1) (s,t,x,y) = s·Ξ k x` if `s = t`,
and `s·Ξ k y` otherwise (in `±1` notation; `xor` is `±1` multiplication). -/
def Xi : (k : ℕ) → (X k → Bool) → Bool
  | 0 => fun x => x ()
  | k + 1 => fun x =>
      let s := x (Sum.inl false)
      let t := x (Sum.inl true)
      xor s (if s = t then Xi k (x ∘ emb k false) else Xi k (x ∘ emb k true))

lemma pm_Xi_succ (k : ℕ) (x : X (k + 1) → Bool) :
    pm (Xi (k + 1) x) =
      (pm (x (Sum.inl false)) + pm (x (Sum.inl true))) / 2 * pm (Xi k (x ∘ emb k false)) +
      (pm (x (Sum.inl false)) - pm (x (Sum.inl true))) / 2 * pm (Xi k (x ∘ emb k true)) := by
  simp only [Xi]
  cases x (Sum.inl false) <;> cases x (Sum.inl true) <;>
    cases Xi k (x ∘ emb k false) <;> cases Xi k (x ∘ emb k true) <;> norm_num [pm, bv]

/-- `Ξ k` has degree at most `k + 1`. -/
theorem Xi_degLE : ∀ k : ℕ, DegLE (Xi k) (k + 1)
  | 0 => by
    rw [DegLE]
    exact var_mem_P (ι := X 0) ()
  | k + 1 => by
    rw [degLE_iff_pm]
    have ih := (degLE_iff_pm _ _).1 (Xi_degLE k)
    have hs : (fun x : X (k + 1) → Bool => pm (x (Sum.inl false))) ∈ P (X (k + 1)) 1 := by
      have : (fun x : X (k + 1) → Bool => pm (x (Sum.inl false))) =
          1 - (2 : ℝ) • (fun x : X (k + 1) → Bool => bv (x (Sum.inl false))) := by
        funext x; simp [pm]
      rw [this]; exact sub_mem (one_mem_P 1) (Submodule.smul_mem _ _ (var_mem_P _))
    have ht : (fun x : X (k + 1) → Bool => pm (x (Sum.inl true))) ∈ P (X (k + 1)) 1 := by
      have : (fun x : X (k + 1) → Bool => pm (x (Sum.inl true))) =
          1 - (2 : ℝ) • (fun x : X (k + 1) → Bool => bv (x (Sum.inl true))) := by
        funext x; simp [pm]
      rw [this]; exact sub_mem (one_mem_P 1) (Submodule.smul_mem _ _ (var_mem_P _))
    have h0 := comp_mem_P (emb k false) (emb_injective k false) ih
    have h1 := comp_mem_P (emb k true) (emb_injective k true) ih
    have key : (fun x => pm (Xi (k + 1) x)) =
        ((1 / 2 : ℝ) • ((fun x : X (k + 1) → Bool => pm (x (Sum.inl false))) +
            (fun x : X (k + 1) → Bool => pm (x (Sum.inl true))))) *
          (fun x : X (k + 1) → Bool => pm (Xi k (x ∘ emb k false))) +
        ((1 / 2 : ℝ) • ((fun x : X (k + 1) → Bool => pm (x (Sum.inl false))) -
            (fun x : X (k + 1) → Bool => pm (x (Sum.inl true))))) *
          (fun x : X (k + 1) → Bool => pm (Xi k (x ∘ emb k true))) := by
      funext x; rw [pm_Xi_succ]; simp; ring
    rw [key]
    have e : k + 1 + 1 = 1 + (k + 1) := by omega
    rw [e]
    exact add_mem (mul_mem_P (Submodule.smul_mem _ _ (add_mem hs ht)) h0)
      (mul_mem_P (Submodule.smul_mem _ _ (sub_mem hs ht)) h1)

/-- An input of `Ξ (k+1)`: control bits `s, t` and the two copies `y₀, y₁`. -/
def mk (k : ℕ) (s t : Bool) (y₀ y₁ : X k → Bool) : X (k + 1) → Bool
  | Sum.inl false => s
  | Sum.inl true => t
  | Sum.inr (c, u) => if c then y₁ u else y₀ u

lemma Xi_mk (k : ℕ) (s t : Bool) (y₀ y₁ : X k → Bool) :
    Xi (k + 1) (mk k s t y₀ y₁) = xor s (if s = t then Xi k y₀ else Xi k y₁) := by
  have h0 : mk k s t y₀ y₁ ∘ emb k false = y₀ := by funext u; rfl
  have h1 : mk k s t y₀ y₁ ∘ emb k true = y₁ := by funext u; rfl
  simp only [Xi, h0, h1]
  rfl

lemma flip_mk_s (k : ℕ) (s t : Bool) (y₀ y₁ : X k → Bool) :
    flip (mk k s t y₀ y₁) (Sum.inl false) = mk k (!s) t y₀ y₁ := by
  funext v
  rcases v with b | ⟨c, u⟩
  · cases b <;> simp [flip, mk, Function.update]
  · simp [flip, mk, Function.update]

lemma flip_mk_t (k : ℕ) (s t : Bool) (y₀ y₁ : X k → Bool) :
    flip (mk k s t y₀ y₁) (Sum.inl true) = mk k s (!t) y₀ y₁ := by
  funext v
  rcases v with b | ⟨c, u⟩
  · cases b <;> simp [flip, mk, Function.update]
  · simp [flip, mk, Function.update]

lemma flip_mk_copy (k : ℕ) (s t : Bool) (y₀ y₁ : X k → Bool) (c : Bool) (w : X k) :
    flip (mk k s t y₀ y₁) (Sum.inr (c, w)) =
      mk k s t (if c then y₀ else flip y₀ w) (if c then flip y₁ w else y₁) := by
  funext v
  rcases v with b | ⟨c', u⟩
  · cases b <;> simp [flip, mk, Function.update]
  · by_cases hu : u = w
    · subst hu; cases c <;> cases c' <;> simp [flip, mk, Function.update]
    · cases c <;> cases c' <;> simp [flip, mk, Function.update, hu]

/-- `Ξ k` takes both values. -/
lemma Xi_surj : ∀ (k : ℕ) (b : Bool), ∃ x, Xi k x = b
  | 0, b => ⟨fun _ => b, rfl⟩
  | k + 1, b => by
    obtain ⟨y, hy⟩ := Xi_surj k b
    exact ⟨mk k false false y y, by simp [Xi_mk, hy]⟩

/-- Every variable of `Ξ k` is relevant. -/
theorem Xi_relevant : ∀ (k : ℕ) (v : X k), Relevant (Xi k) v
  | 0, () => ⟨fun _ => false, by decide⟩
  | k + 1, Sum.inl false => by
    -- s = t and both copies agree: flipping s switches the copy and the sign
    obtain ⟨y, hy⟩ := Xi_surj k false
    exact ⟨mk k false false y y, by rw [flip_mk_s, Xi_mk, Xi_mk]; simp [hy]⟩
  | k + 1, Sum.inl true => by
    -- s = t and the copies disagree: flipping t switches the copy
    obtain ⟨y₀, hy₀⟩ := Xi_surj k false
    obtain ⟨y₁, hy₁⟩ := Xi_surj k true
    exact ⟨mk k false false y₀ y₁, by rw [flip_mk_t, Xi_mk, Xi_mk]; simp [hy₀, hy₁]⟩
  | k + 1, Sum.inr (c, w) => by
    -- s = false, t = c selects copy c; flip w inside it
    obtain ⟨y, hy⟩ := Xi_relevant k w
    refine ⟨mk k false c y y, ?_⟩
    rw [flip_mk_copy, Xi_mk, Xi_mk]
    cases c <;> simpa using hy

/-! ## Main results -/

/-- **Chiarelli–Hatami–Saks.** For every `d ≥ 1` there is a Boolean function on
`n = 3 · 2^(d-1) - 2` variables, of degree at most `d`, all of whose variables are relevant. -/
theorem exists_degLE_all_relevant (d : ℕ) (hd : 1 ≤ d) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool), n + 2 = 3 * 2 ^ (d - 1) ∧ DegLE f d ∧
      ∀ i, Relevant f i := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  let eq := Fintype.equivFin (X k)
  refine ⟨Fintype.card (X k), fun y => Xi k (y ∘ eq), by simpa using card_X k, ?_, ?_⟩
  · unfold DegLE
    exact comp_mem_P (κ := X k) eq eq.injective (Xi_degLE k)
  · intro i
    obtain ⟨x, hx⟩ := Xi_relevant k (eq.symm i)
    refine ⟨x ∘ eq.symm, ?_⟩
    have h1 : (flip (x ∘ eq.symm) i) ∘ eq = flip x (eq.symm i) := by
      funext v
      simp only [Function.comp_apply, flip, Function.update]
      by_cases h : v = eq.symm i
      · subst h; simp
      · have : eq v ≠ i := fun h' => h (by rw [← h']; simp)
        simp [h, this]
    have h2 : (x ∘ eq.symm) ∘ eq = x := by funext v; simp
    simpa [h1, h2] using hx

open Classical in
/-- **`C44 ≥ 3/2`.** If every Boolean function of degree at most `d` has at most `C · 2^d`
relevant variables, then `C ≥ 3/2`. -/
theorem three_halves_le (C : ℝ)
    (hC : ∀ (n d : ℕ) (f : (Fin n → Bool) → Bool), DegLE f d →
      ((Finset.univ.filter (fun i => Relevant f i)).card : ℝ) ≤ C * 2 ^ d) :
    3 / 2 ≤ C := by
  by_contra hlt
  push Not at hlt
  -- choose d with 2 / 2^d < 3/2 - C
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (3 / 2 - C) / 2 by linarith)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  obtain ⟨n, f, hn, hdeg, hrel⟩ := exists_degLE_all_relevant (m + 1) (by omega)
  have hcard := hC n (m + 1) f hdeg
  have hall : (Finset.univ.filter (fun i => Relevant f i)) = Finset.univ := by
    ext i; simp [hrel i]
  rw [hall, Finset.card_univ, Fintype.card_fin] at hcard
  have hn' : (n : ℝ) = 3 * 2 ^ m - 2 := by
    have : ((n + 2 : ℕ) : ℝ) = ((3 * 2 ^ m : ℕ) : ℝ) := by rw [hn]; simp
    push_cast at this; linarith
  rw [hn'] at hcard
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have : (1 / 2 : ℝ) ^ m = 1 / 2 ^ m := by rw [div_pow, one_pow]
  rw [this] at hm
  rw [pow_succ] at hcard
  have hm' : 1 < (3 / 2 - C) / 2 * 2 ^ m := by
    rw [div_lt_iff₀ h2m] at hm; linarith
  nlinarith

end OpenProblemsLab.C44
