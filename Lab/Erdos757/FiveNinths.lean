import FormalConjectures.ErdosProblems.«757»

/-!
# Erdős #757: `sSup {c | IsAdmissible c} ≤ 5 / 9`

The family (a reader submission on erdosproblemaday.com, 7bkzb8):
`O = {0, 49, 75, 83, 98, 101, 117, 119, 121, 159, 269}`, `φ x = 101 + 18 x / 269`,
`S 0 = O`, `S (k+1) = O ∪ φ '' S k`.

* `card_S`: `|S k| = 11 + 9 k`.
* `sidon_bound`: every Sidon subset of `S k` has at most `7 + 5 k` points (a transfer argument
  with potential `σ`, two finite checks on subsets of `O`).
* `good_S`: no `S k` has a relation `a + b = c + d` among four distinct points, and no two
  different 3-term progressions in `S k` share two points. `card45` turns this into the
  (4,5) property. The induction uses a finite check of `S 2` (29 points) and a "no mixing"
  lemma (`nmA`, `nmB1`, `nmB2`): a relation through a point of `O` stays inside `S 1`.
  That lemma is a kernel-checked interval computation over the points of `S 3` and the
  interval `φ^[4] [0, 269]`.
* Hence every admissible `c` satisfies `c (11 + 9 k) ≤ 7 + 5 k` for all `k`, so `c ≤ 5/9`.

All finite facts are checked with `decide +kernel` (no `native_decide`).
This formalizes `explorer/erdos757/gadgets/five_ninths_all_k.py`.
-/

open scoped Pointwise

namespace OpenProblemsLab.E757.FiveNinths

open _root_.Erdos757

-- Check the many small kernel computations one at a time (in parallel they need far more memory).
set_option Elab.async false

def Oz : Finset ℤ := {0, 49, 75, 83, 98, 101, 117, 119, 121, 159, 269}

def O : Finset ℚ := Oz.image (Int.cast)

def φ (x : ℚ) : ℚ := 101 + 18 / 269 * x

def S : ℕ → Finset ℚ
  | 0 => O
  | k + 1 => O ∪ (S k).image φ

lemma mem_O {y : ℚ} : y ∈ O ↔ ∃ z ∈ Oz, (z : ℚ) = y := Finset.mem_image

lemma intCast_mem_O {z : ℤ} (hz : z ∈ Oz) : (z : ℚ) ∈ O := mem_O.2 ⟨z, hz, rfl⟩

lemma φ_inj : Function.Injective φ := by
  intro x y h
  simp only [φ] at h
  linarith

lemma O_sub_S : ∀ k, O ⊆ S k
  | 0 => subset_refl _
  | _ + 1 => Finset.subset_union_left

lemma mem_S_succ {k : ℕ} {y : ℚ} : y ∈ S (k + 1) ↔ y ∈ O ∨ ∃ z ∈ S k, φ z = y := by
  simp [S]

lemma Oz_bounds : ∀ z ∈ Oz, 0 ≤ z ∧ z ≤ 269 ∧ (z ≤ 101 ∨ 117 ≤ z) := by decide

lemma O_bounds {y : ℚ} (hy : y ∈ O) : 0 ≤ y ∧ y ≤ 269 ∧ (y ≤ 101 ∨ 117 ≤ y) := by
  obtain ⟨z, hz, rfl⟩ := mem_O.1 hy
  obtain ⟨h1, h2, h3⟩ := Oz_bounds z hz
  refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, ?_⟩
  rcases h3 with h | h
  · exact Or.inl (by exact_mod_cast h)
  · exact Or.inr (by exact_mod_cast h)

lemma S_bounds : ∀ k, ∀ y ∈ S k, 0 ≤ y ∧ y ≤ 269
  | 0, _, hy => ⟨(O_bounds hy).1, (O_bounds hy).2.1⟩
  | k + 1, y, hy => by
    rcases mem_S_succ.1 hy with h | ⟨z, hz, rfl⟩
    · exact ⟨(O_bounds h).1, (O_bounds h).2.1⟩
    · obtain ⟨h1, h2⟩ := S_bounds k z hz
      simp only [φ]
      constructor <;> linarith

/-- Every point of `S n` is `φ^[j] o` with `j ≤ m` and `o ∈ O`, or lies in `φ^[m+1] [0,269]`. -/
lemma decomp : ∀ m n, ∀ y ∈ S n,
    (∃ j ≤ m, ∃ o ∈ O, y = φ^[j] o) ∨ ∃ z, 0 ≤ z ∧ z ≤ 269 ∧ y = φ^[m + 1] z := by
  intro m
  induction m with
  | zero =>
    intro n y hy
    cases n with
    | zero => exact Or.inl ⟨0, le_rfl, y, hy, rfl⟩
    | succ k =>
      rcases mem_S_succ.1 hy with h | ⟨z, hz, rfl⟩
      · exact Or.inl ⟨0, le_rfl, y, h, rfl⟩
      · exact Or.inr ⟨z, (S_bounds k z hz).1, (S_bounds k z hz).2, rfl⟩
  | succ m ih =>
    intro n y hy
    cases n with
    | zero => exact Or.inl ⟨0, Nat.zero_le _, y, hy, rfl⟩
    | succ k =>
      rcases mem_S_succ.1 hy with h | ⟨z, hz, rfl⟩
      · exact Or.inl ⟨0, Nat.zero_le _, y, h, rfl⟩
      · rcases ih k z hz with ⟨j, hj, o, ho, rfl⟩ | ⟨w, h0, h1, rfl⟩
        · exact Or.inl ⟨j + 1, by omega, o, ho, (Function.iterate_succ_apply' φ j o).symm⟩
        · exact Or.inr ⟨w, h0, h1, (Function.iterate_succ_apply' φ (m + 1) w).symm⟩

/- ## Counting: `|S k| = 11 + 9 k` -/

lemma φ_Oz : ∀ z ∈ Oz, ∀ w ∈ Oz, w * 269 = 101 * 269 + 18 * z → z = 0 ∨ z = 269 := by
  decide +kernel

lemma zero_mem_O : (0 : ℚ) ∈ O := mem_O.2 ⟨0, by decide, by simp⟩
lemma mem_O_269 : (269 : ℚ) ∈ O := mem_O.2 ⟨269, by decide, by simp⟩
lemma mem_O_101 : (101 : ℚ) ∈ O := mem_O.2 ⟨101, by decide, by simp⟩
lemma mem_O_119 : (119 : ℚ) ∈ O := mem_O.2 ⟨119, by decide, by simp⟩

/-- A point of `O` that is also in `φ '' S k` comes from `0` or `269`. -/
lemma O_inter {k : ℕ} {y z : ℚ} (hy : y ∈ O) (hz : z ∈ S k) (h : φ z = y) :
    z = 0 ∨ z = 269 := by
  rcases decomp 0 k z hz with ⟨j, hj, o, ho, rfl⟩ | ⟨w, h0, h1, rfl⟩
  · obtain rfl : j = 0 := by omega
    obtain ⟨a, ha, rfl⟩ := mem_O.1 ho
    obtain ⟨b, hb, rfl⟩ := mem_O.1 hy
    simp only [Function.iterate_zero, id] at h ⊢
    have h' : (b : ℚ) * 269 = 101 * 269 + 18 * a := by simp only [φ] at h; linarith
    rcases φ_Oz a ha b hb (by exact_mod_cast h') with h | h
    · left; simp [h]
    · right; simp [h]
  · exfalso
    have hb := (O_bounds hy).2.2
    simp only [zero_add, Function.iterate_one, φ] at h
    rcases hb with hb | hb <;> linarith

lemma inter_eq (k : ℕ) : O ∩ (S k).image φ = {101, 119} := by
  ext y
  simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hy, z, hz, rfl⟩
    rcases O_inter hy hz rfl with rfl | rfl
    · left; norm_num [φ]
    · right; norm_num [φ]
  · rintro (rfl | rfl)
    · exact ⟨mem_O_101, 0, O_sub_S k zero_mem_O, by norm_num [φ]⟩
    · exact ⟨mem_O_119, 269, O_sub_S k mem_O_269, by norm_num [φ]⟩

lemma card_O : O.card = 11 := by
  rw [O, Finset.card_image_of_injective _ Int.cast_injective]; decide

lemma card_S : ∀ k, (S k).card = 11 + 9 * k
  | 0 => card_O
  | k + 1 => by
    have h := Finset.card_union_add_card_inter O ((S k).image φ)
    rw [inter_eq, Finset.card_image_of_injective _ φ_inj, card_S k, card_O] at h
    have h2 : ({101, 119} : Finset ℚ).card = 2 := by norm_num
    change (O ∪ (S k).image φ).card = _
    omega

/- ## Sidon bound: every Sidon subset of `S k` has at most `7 + 5 k` points -/

/-- The nine 3-term progressions `(a, b, c)`, `a + c = 2 b`, inside `Oz`. -/
def APz : List (ℤ × ℤ × ℤ) :=
  [(0, 49, 98), (49, 75, 101), (49, 83, 117), (49, 159, 269), (75, 98, 121), (75, 117, 159),
   (83, 101, 119), (83, 121, 159), (117, 119, 121)]

lemma APz_spec : ∀ t ∈ APz, t.1 + t.2.2 = t.2.1 + t.2.1 ∧ t.1 < t.2.1 := by decide

def HitsZ (T : Finset ℤ) : Prop := ∃ t ∈ APz, t.1 ∈ T ∧ t.2.1 ∈ T ∧ t.2.2 ∈ T

instance : DecidablePred HitsZ := fun T => by unfold HitsZ; infer_instance

def sz (T : Finset ℤ) : ℕ := if (0 : ℤ) ∈ T ∧ (269 : ℤ) ∈ T then 0 else 1
def tz (T : Finset ℤ) : ℕ := if (101 : ℤ) ∈ T ∧ (119 : ℤ) ∈ T then 0 else 1
def cz (T : Finset ℤ) : ℕ := (if (101 : ℤ) ∈ T then 1 else 0) + (if (119 : ℤ) ∈ T then 1 else 0)

/-- `Oz` without `0` and `49`; the subset checks are split by whether `0`, `49` are present. -/
def Oz2 : Finset ℤ := {75, 83, 98, 101, 117, 119, 121, 159, 269}

lemma Oz_eq : Oz = insert 0 (insert 49 Oz2) := by decide +kernel

lemma forall_powerset_insert {Q : Finset ℤ → Prop} {a : ℤ} {s : Finset ℤ}
    (h1 : ∀ T ∈ s.powerset, Q T) (h2 : ∀ T ∈ s.powerset, Q (insert a T)) :
    ∀ T ∈ (insert a s).powerset, Q T := by
  intro T hT
  rw [Finset.powerset_insert, Finset.mem_union, Finset.mem_image] at hT
  rcases hT with hT | ⟨U, hU, rfl⟩
  exacts [h1 T hT, h2 U hU]

def Qb (T : Finset ℤ) : Prop := HitsZ T ∨ T.card + sz T ≤ 7
def Qs (T : Finset ℤ) : Prop := HitsZ T ∨ T.card + sz T ≤ 5 + cz T + tz T
instance : DecidablePred Qb := fun T => by unfold Qb; infer_instance
instance : DecidablePred Qs := fun T => by unfold Qs; infer_instance

lemma qb00 : ∀ T ∈ Oz2.powerset, Qb T := by decide +kernel
lemma qb01 : ∀ T ∈ Oz2.powerset, Qb (insert 49 T) := by decide +kernel
lemma qb10 : ∀ T ∈ Oz2.powerset, Qb (insert 0 T) := by decide +kernel
lemma qb11 : ∀ T ∈ Oz2.powerset, Qb (insert 0 (insert 49 T)) := by decide +kernel
lemma qs00 : ∀ T ∈ Oz2.powerset, Qs T := by decide +kernel
lemma qs01 : ∀ T ∈ Oz2.powerset, Qs (insert 49 T) := by decide +kernel
lemma qs10 : ∀ T ∈ Oz2.powerset, Qs (insert 0 T) := by decide +kernel
lemma qs11 : ∀ T ∈ Oz2.powerset, Qs (insert 0 (insert 49 T)) := by decide +kernel

lemma base_z : ∀ T ∈ Oz.powerset, HitsZ T ∨ T.card + sz T ≤ 7 := by
  rw [Oz_eq]
  exact forall_powerset_insert (Q := Qb) (forall_powerset_insert qb00 qb01)
    (forall_powerset_insert (Q := fun T => Qb (insert 0 T)) qb10 qb11)

lemma step_z : ∀ T ∈ Oz.powerset, HitsZ T ∨ T.card + sz T ≤ 5 + cz T + tz T := by
  rw [Oz_eq]
  exact forall_powerset_insert (Q := Qs) (forall_powerset_insert qs00 qs01)
    (forall_powerset_insert (Q := fun T => Qs (insert 0 T)) qs10 qs11)


def σ (J : Finset ℚ) : ℕ := if (0 : ℚ) ∈ J ∧ (269 : ℚ) ∈ J then 0 else 1

lemma sidon_sub {I T : Finset ℚ} (hI : IsSidon (I : Set ℚ)) (hT : T ⊆ I) :
    IsSidon (T : Set ℚ) :=
  fun a ha b hb c hc d hd h => hI a (hT ha) b (hT hb) c (hT hc) d (hT hd) h

lemma sidon_pull {I J : Finset ℚ} (hI : IsSidon (I : Set ℚ)) (hJ : ∀ z ∈ J, φ z ∈ I) :
    IsSidon (J : Set ℚ) := by
  intro a ha b hb c hc d hd h
  have := hI (φ a) (hJ a ha) (φ b) (hJ b hb) (φ c) (hJ c hc) (φ d) (hJ d hd)
    (by simp only [φ]; linarith)
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨φ_inj h1, φ_inj h2⟩
  · exact Or.inr ⟨φ_inj h1, φ_inj h2⟩

/-- A Sidon subset of `O` comes from a subset of `Oz` that contains none of the nine APs. -/
lemma transfer {T : Finset ℚ} (hT : T ⊆ O) (hS : IsSidon (T : Set ℚ)) :
    ∃ Tz ∈ Oz.powerset, ¬ HitsZ Tz ∧ Tz.card = T.card ∧ ∀ z : ℤ, z ∈ Tz ↔ (z : ℚ) ∈ T := by
  classical
  have hmem : ∀ z : ℤ, z ∈ Oz.filter (fun z : ℤ => (z : ℚ) ∈ T) ↔ (z : ℚ) ∈ T := by
    intro z
    rw [Finset.mem_filter]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    obtain ⟨w, hw, hwz⟩ := mem_O.1 (hT h)
    rwa [← Int.cast_injective hwz]
  refine ⟨Oz.filter (fun z : ℤ => (z : ℚ) ∈ T), Finset.mem_powerset.2 (Finset.filter_subset _ _),
    ?_, ?_, hmem⟩
  · rintro ⟨⟨a, b, c⟩, ht, ha, hb, hc⟩
    obtain ⟨hsum, hlt⟩ : a + c = b + b ∧ a < b := APz_spec _ ht
    rw [hmem] at ha hb hc
    have := hS _ ha _ hb _ hc _ hb (by exact_mod_cast hsum)
    rcases this with ⟨h, -⟩ | ⟨h, -⟩ <;> (have h' := Int.cast_injective h; dsimp only at h'; omega)
  · have himg : (Oz.filter (fun z : ℤ => (z : ℚ) ∈ T)).image (Int.cast : ℤ → ℚ) = T := by
      ext y
      rw [Finset.mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩; exact (hmem z).1 hz
      · intro hy
        obtain ⟨w, -, rfl⟩ := mem_O.1 (hT hy)
        exact ⟨w, (hmem w).2 hy, rfl⟩
    rw [← Finset.card_image_of_injective _ (Int.cast_injective (α := ℚ)), himg]

theorem sidon_bound : ∀ k, ∀ J : Finset ℚ, J ⊆ S k → IsSidon (J : Set ℚ) →
    J.card + σ J ≤ 7 + 5 * k
  | 0, J, hJ, hS => by
    obtain ⟨Tz, hTz, hnh, hcard, hmem⟩ := transfer hJ hS
    have h := (base_z Tz hTz).resolve_left hnh
    have e : sz Tz = σ J := by
      simp only [sz, σ, hmem, Int.cast_zero, Int.cast_ofNat]
    omega
  | k + 1, I, hI, hS => by
    classical
    set T := I.filter (· ∈ O) with hTdef
    set J := (S k).filter (fun z => φ z ∈ I) with hJdef
    have hTO : T ⊆ O := fun x hx => (Finset.mem_filter.1 hx).2
    have hTS : IsSidon (T : Set ℚ) := sidon_sub hS (Finset.filter_subset _ _)
    have hJS : IsSidon (J : Set ℚ) := sidon_pull hS (fun z hz => (Finset.mem_filter.1 hz).2)
    have ih := sidon_bound k J (Finset.filter_subset _ _) hJS
    obtain ⟨Tz, hTz, hnh, hcard, hmem⟩ := transfer hTO hTS
    have hstep := (step_z Tz hTz).resolve_left hnh
    have hU : I = T ∪ J.image φ := by
      ext y
      simp only [hTdef, hJdef, Finset.mem_union, Finset.mem_filter, Finset.mem_image]
      constructor
      · intro hy
        rcases mem_S_succ.1 (hI hy) with h | ⟨z, hz, rfl⟩
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨z, ⟨hz, hy⟩, rfl⟩
      · rintro (⟨hy, -⟩ | ⟨z, ⟨-, hz⟩, rfl⟩) <;> assumption
    have hInt : T ∩ J.image φ = ({(101 : ℚ), 119} : Finset ℚ).filter (· ∈ I) := by
      ext y
      simp only [hTdef, hJdef, Finset.mem_inter, Finset.mem_filter, Finset.mem_image,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hyI, hyO⟩, z, ⟨hz, -⟩, rfl⟩
        refine ⟨?_, hyI⟩
        rcases O_inter hyO hz rfl with rfl | rfl
        · left; norm_num [φ]
        · right; norm_num [φ]
      · rintro ⟨rfl | rfl, hy⟩
        · exact ⟨⟨hy, mem_O_101⟩, 0, ⟨O_sub_S k zero_mem_O, by norm_num [φ]; exact hy⟩,
            by norm_num [φ]⟩
        · exact ⟨⟨hy, mem_O_119⟩, 269, ⟨O_sub_S k mem_O_269, by norm_num [φ]; exact hy⟩,
            by norm_num [φ]⟩
    have hTmem : ∀ q : ℚ, q ∈ O → (q ∈ T ↔ q ∈ I) := fun q hq => by
      simp only [hTdef, Finset.mem_filter, hq, and_true]
    have e0 : (0 : ℤ) ∈ Tz ↔ (0 : ℚ) ∈ I := by
      rw [hmem, Int.cast_zero, hTmem _ zero_mem_O]
    have e269 : (269 : ℤ) ∈ Tz ↔ (269 : ℚ) ∈ I := by
      rw [hmem, Int.cast_ofNat, hTmem _ mem_O_269]
    have e101 : (101 : ℤ) ∈ Tz ↔ (101 : ℚ) ∈ I := by
      rw [hmem, Int.cast_ofNat, hTmem _ mem_O_101]
    have e119 : (119 : ℤ) ∈ Tz ↔ (119 : ℚ) ∈ I := by
      rw [hmem, Int.cast_ofNat, hTmem _ mem_O_119]
    have j0 : (0 : ℚ) ∈ J ↔ (101 : ℚ) ∈ I := by
      simp only [hJdef, Finset.mem_filter, O_sub_S k zero_mem_O, true_and]; norm_num [φ]
    have j269 : (269 : ℚ) ∈ J ↔ (119 : ℚ) ∈ I := by
      simp only [hJdef, Finset.mem_filter, O_sub_S k mem_O_269, true_and]; norm_num [φ]
    have esz : sz Tz = σ I := by simp only [sz, σ, e0, e269]
    have etz : tz Tz = σ J := by simp only [tz, σ, e101, e119, j0, j269]
    have ecz : (({(101 : ℚ), 119} : Finset ℚ).filter (· ∈ I)).card = cz Tz := by
      rw [Finset.card_filter, Finset.sum_pair (by norm_num)]
      simp only [cz, e101, e119]
    have hcu := Finset.card_union_add_card_inter T (J.image φ)
    rw [← hU, hInt, ecz, Finset.card_image_of_injective _ φ_inj] at hcu
    omega


/- ## The (4,5) property from two forbidden patterns -/

/-- `u` completes `{x, y}` to a 3-term progression. -/
def IsComp (x y u : ℚ) : Prop := u + x = 2 * y ∨ u + y = 2 * x ∨ x + y = 2 * u

/-- No relation `a + b = c + d` among four distinct points. -/
def NoA (A : Finset ℚ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → a ≠ b → c ≠ d → a ≠ c → a ≠ d → False

/-- No two different 3-term progressions share two points. -/
def NoAP2 (A : Finset ℚ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ u ∈ A, ∀ v ∈ A, x ≠ y → u ≠ v → IsComp x y u → IsComp x y v → False

def Good (A : Finset ℚ) : Prop := NoA A ∧ NoAP2 A

lemma Good.mono {A B : Finset ℚ} (h : Good A) (hB : B ⊆ A) : Good B :=
  ⟨fun a ha b hb c hc d hd => h.1 a (hB ha) b (hB hb) c (hB hc) d (hB hd),
   fun x hx y hy u hu v hv => h.2 x (hB hx) y (hB hy) u (hB hu) v (hB hv)⟩

lemma length_le_card_sub {B : Finset ℚ} (L : List ℚ) (hL : L.Nodup)
    (hsub : ∀ x ∈ L, x ∈ B - B) : L.length ≤ (B - B).card := by
  classical
  rw [← List.toFinset_card_of_nodup hL]
  exact Finset.card_le_card (fun x hx => hsub x (List.mem_toFinset.1 hx))

lemma card45 {B : Finset ℚ} (hG : Good B) (hc : B.card = 4) : 11 ≤ (B - B).card := by
  classical
  have hlen : (B.sort).length = 4 := by rw [Finset.length_sort, hc]
  have hsort := List.sortedLT_iff_pairwise.1 (Finset.sortedLT_sort B)
  have hmem : ∀ x, x ∈ B.sort ↔ x ∈ B := fun x => Finset.mem_sort _
  generalize B.sort = L at hlen hsort hmem
  obtain ⟨w1, w2, w3, w4, rfl⟩ : ∃ a b c d, L = [a, b, c, d] := by
    match L, hlen with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  have h1 : w1 ∈ B := (hmem w1).1 (by simp)
  have h2 : w2 ∈ B := (hmem w2).1 (by simp)
  have h3 : w3 ∈ B := (hmem w3).1 (by simp)
  have h4 : w4 ∈ B := (hmem w4).1 (by simp)
  have h12 : w1 < w2 := by simp_all
  have h23 : w2 < w3 := by simp_all
  have h34 : w3 < w4 := by simp_all
  have hA : w2 + w3 ≠ w1 + w4 := fun h =>
    hG.1 w2 h2 w3 h3 w1 h1 w4 h4 h (by linarith) (by linarith) (by linarith) (by linarith)
  have hcase : (¬ w1 + w3 = 2 * w2 ∧ ¬ w1 + w4 = 2 * w2) ∨
      (¬ w1 + w4 = 2 * w3 ∧ ¬ w2 + w4 = 2 * w3) := by
    by_contra hne
    simp only [not_or, not_and, not_not] at hne
    obtain ⟨hl, hr⟩ := hne
    by_cases p123 : w1 + w3 = 2 * w2
    · by_cases p134 : w1 + w4 = 2 * w3
      · exact hG.2 w1 h1 w3 h3 w2 h2 w4 h4 (by linarith) (by linarith)
          (Or.inr (Or.inr p123)) (Or.inl (by linarith))
      · exact hG.2 w2 h2 w3 h3 w1 h1 w4 h4 (by linarith) (by linarith)
          (Or.inr (Or.inl (by linarith))) (Or.inl (by linarith [hr p134]))
    · have p124 := hl p123
      by_cases p134 : w1 + w4 = 2 * w3
      · linarith
      · exact hG.2 w2 h2 w4 h4 w1 h1 w3 h3 (by linarith) (by linarith)
          (Or.inr (Or.inl (by linarith))) (Or.inr (Or.inr (by linarith [hr p134])))
  rcases hcase with ⟨p1, p2⟩ | ⟨p1, p2⟩
  · have := length_le_card_sub (B := B)
      [0, w4 - w1, w1 - w4, w3 - w1, w1 - w3, w4 - w2, w2 - w4, w3 - w2, w2 - w3, w2 - w1, w1 - w2]
      (by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          List.nodup_nil, and_true]
        and_intros <;> intro h <;>
          first | contradiction | linarith | exact hA (by linarith) | exact p1 (by linarith) | exact p2 (by linarith))
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
        · rw [← sub_self w1]; exact Finset.sub_mem_sub h1 h1
        all_goals exact Finset.sub_mem_sub (by assumption) (by assumption))
    simpa using this
  · have := length_le_card_sub (B := B)
      [0, w4 - w1, w1 - w4, w3 - w1, w1 - w3, w4 - w2, w2 - w4, w3 - w2, w2 - w3, w4 - w3, w3 - w4]
      (by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          List.nodup_nil, and_true]
        and_intros <;> intro h <;>
          first | contradiction | linarith | exact hA (by linarith) | exact p1 (by linarith) | exact p2 (by linarith))
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
        · rw [← sub_self w1]; exact Finset.sub_mem_sub h1 h1
        all_goals exact Finset.sub_mem_sub (by assumption) (by assumption))
    simpa using this


/- ## No mixing: a relation through a point of `O` stays inside `S 1`

Every point of every `S n` is `φ^[j] o` (`j ≤ 3`, `o ∈ O`) or lies in `φ^[4] [0, 269]`.
Scaled by `269 ^ 4`, the first kind are the integers in `P` (tagged with their depth), and the
second kind lie in `[LO, HI]`. A finite check over these "slots" shows that no additive relation
through a point of `O` can use a point of depth `≥ 2`. -/

/-- The points of `S 3`, scaled by `269 ^ 4`, each with its depth (least `j` with the point in
`φ^[j] O`). -/
def P : List (ℤ × ℕ) := [(0, 0), (256569601729, 0), (392708574075, 0), (434597488643, 0), (513139203458, 0), (528847546421, 0), (612625375557, 0), (623097604199, 0), (633569832841, 0), (832542177039, 0), (1408514752349, 0), (546015772559, 1), (555125443571, 1), (557928419267, 1), (563183998697, 1), (564235114583, 1), (569841065975, 1), (570541809899, 1), (571242553823, 1), (584556688379, 1), (565383917819, 2), (565993486883, 2), (566181046595, 2), (566532721055, 2), (566603055947, 2), (566978175371, 2), (567025065299, 2), (567071955227, 2), (567962863859, 2), (566679927539, 3), (566720716547, 3), (566733267011, 3), (566756799131, 3), (566761505555, 3), (566786606483, 3), (566789744099, 3), (566792881715, 3), (566852496419, 3)]

def LO : ℤ := 566761505555
def HI : ℤ := 566789744099

/-- A slot is a point of `P`, or `none`: an unknown point in `[LO, HI]` (depth `≥ 4`). -/
def slots : List (Option (ℤ × ℕ)) := none :: P.map some
def deep : Option (ℤ × ℕ) → Bool
  | none => true
  | some (_, d) => 2 ≤ d
def lb : Option (ℤ × ℕ) → ℤ
  | none => LO
  | some (v, _) => v
def ub : Option (ℤ × ℕ) → ℤ
  | none => HI
  | some (v, _) => v
def same (a b : Option (ℤ × ℕ)) : Bool :=
  match a, b with
  | some (u, _), some (v, _) => u == v
  | _, _ => false

/-- `x1 + s2 = s3 + s4` with `x1` in `O`: impossible if some slot is deep (unless two known
slots coincide). -/
def okA (x1 : ℤ) (s2 s3 s4 : Option (ℤ × ℕ)) : Bool :=
  let s1 : Option (ℤ × ℕ) := some (x1, 0)
  if !(deep s2 || deep s3 || deep s4) then true
  else if same s1 s2 || same s1 s3 || same s1 s4 || same s2 s3 || same s2 s4 || same s3 s4 then true
  else !(decide (x1 + lb s2 - ub s3 - ub s4 ≤ 0) && decide (0 ≤ x1 + ub s2 - lb s3 - lb s4))

/-- `x1 + s3 = 2 s2` with `x1` in `O`. -/
def okB1 (x1 : ℤ) (s2 s3 : Option (ℤ × ℕ)) : Bool :=
  let s1 : Option (ℤ × ℕ) := some (x1, 0)
  if !(deep s2 || deep s3) then true
  else if same s1 s3 then true
  else !(decide (x1 + lb s3 - 2 * ub s2 ≤ 0) && decide (0 ≤ x1 + ub s3 - 2 * lb s2))

/-- `s1 + s3 = 2 x2` with `x2` in `O`. -/
def okB2 (x2 : ℤ) (s1 s3 : Option (ℤ × ℕ)) : Bool :=
  if !(deep s1 || deep s3) then true
  else if same s1 s3 then true
  else !(decide (lb s1 + lb s3 - 2 * x2 ≤ 0) && decide (0 ≤ ub s1 + ub s3 - 2 * x2))

/- The finite checks are split into many small pieces: one huge `decide` would need far more
memory than the kernel re-check is allowed. -/

/-- The slots, cut into chunks of four. -/
def ch0 : List (Option (ℤ × ℕ)) := [none, some (0, 0), some (256569601729, 0), some (392708574075, 0)]
def ch1 : List (Option (ℤ × ℕ)) := [some (434597488643, 0), some (513139203458, 0), some (528847546421, 0), some (612625375557, 0)]
def ch2 : List (Option (ℤ × ℕ)) := [some (623097604199, 0), some (633569832841, 0), some (832542177039, 0), some (1408514752349, 0)]
def ch3 : List (Option (ℤ × ℕ)) := [some (546015772559, 1), some (555125443571, 1), some (557928419267, 1), some (563183998697, 1)]
def ch4 : List (Option (ℤ × ℕ)) := [some (564235114583, 1), some (569841065975, 1), some (570541809899, 1), some (571242553823, 1)]
def ch5 : List (Option (ℤ × ℕ)) := [some (584556688379, 1), some (565383917819, 2), some (565993486883, 2), some (566181046595, 2)]
def ch6 : List (Option (ℤ × ℕ)) := [some (566532721055, 2), some (566603055947, 2), some (566978175371, 2), some (567025065299, 2)]
def ch7 : List (Option (ℤ × ℕ)) := [some (567071955227, 2), some (567962863859, 2), some (566679927539, 3), some (566720716547, 3)]
def ch8 : List (Option (ℤ × ℕ)) := [some (566733267011, 3), some (566756799131, 3), some (566761505555, 3), some (566786606483, 3)]
def ch9 : List (Option (ℤ × ℕ)) := [some (566789744099, 3), some (566792881715, 3), some (566852496419, 3)]

lemma slots_eq : slots = ch0 ++ (ch1 ++ (ch2 ++ (ch3 ++ (ch4 ++ (ch5 ++ (ch6 ++ (ch7 ++ (ch8 ++ (ch9))))))))) := by decide +kernel

/-- All type-A checks with first point `x1` and second slot `s2`. -/
def rowA (x1 : ℤ) (s2 : Option (ℤ × ℕ)) : Bool :=
  slots.all fun s3 => slots.all fun s4 => okA x1 s2 s3 s4

/-- All progression checks with the point `x` of `O`. -/
def rowB (x : ℤ) : Bool :=
  slots.all fun s2 => slots.all fun s3 => okB1 x s2 s3 && okB2 x s2 s3

theorem cA_0_0 : ch0.all (rowA (0 * 269 ^ 4)) = true := by decide +kernel
theorem cA_0_1 : ch1.all (rowA (0 * 269 ^ 4)) = true := by decide +kernel
theorem cA_0_2 : ch2.all (rowA (0 * 269 ^ 4)) = true := by decide +kernel
theorem cA_0_3 : ch3.all (rowA (0 * 269 ^ 4)) = true := by decide +kernel
theorem cA_0_4 : ch4.all (rowA (0 * 269 ^ 4)) = true := by decide +kernel
theorem cA_0_5 : ch5.all (rowA (0 * 269 ^ 4)) = true := by decide +kernel
theorem cA_0_6 : ch6.all (rowA (0 * 269 ^ 4)) = true := by decide +kernel
theorem cA_0_7 : ch7.all (rowA (0 * 269 ^ 4)) = true := by decide +kernel
theorem cA_0_8 : ch8.all (rowA (0 * 269 ^ 4)) = true := by decide +kernel
theorem cA_0_9 : ch9.all (rowA (0 * 269 ^ 4)) = true := by decide +kernel
theorem cA_1_0 : ch0.all (rowA (49 * 269 ^ 4)) = true := by decide +kernel
theorem cA_1_1 : ch1.all (rowA (49 * 269 ^ 4)) = true := by decide +kernel
theorem cA_1_2 : ch2.all (rowA (49 * 269 ^ 4)) = true := by decide +kernel
theorem cA_1_3 : ch3.all (rowA (49 * 269 ^ 4)) = true := by decide +kernel
theorem cA_1_4 : ch4.all (rowA (49 * 269 ^ 4)) = true := by decide +kernel
theorem cA_1_5 : ch5.all (rowA (49 * 269 ^ 4)) = true := by decide +kernel
theorem cA_1_6 : ch6.all (rowA (49 * 269 ^ 4)) = true := by decide +kernel
theorem cA_1_7 : ch7.all (rowA (49 * 269 ^ 4)) = true := by decide +kernel
theorem cA_1_8 : ch8.all (rowA (49 * 269 ^ 4)) = true := by decide +kernel
theorem cA_1_9 : ch9.all (rowA (49 * 269 ^ 4)) = true := by decide +kernel
theorem cA_2_0 : ch0.all (rowA (75 * 269 ^ 4)) = true := by decide +kernel
theorem cA_2_1 : ch1.all (rowA (75 * 269 ^ 4)) = true := by decide +kernel
theorem cA_2_2 : ch2.all (rowA (75 * 269 ^ 4)) = true := by decide +kernel
theorem cA_2_3 : ch3.all (rowA (75 * 269 ^ 4)) = true := by decide +kernel
theorem cA_2_4 : ch4.all (rowA (75 * 269 ^ 4)) = true := by decide +kernel
theorem cA_2_5 : ch5.all (rowA (75 * 269 ^ 4)) = true := by decide +kernel
theorem cA_2_6 : ch6.all (rowA (75 * 269 ^ 4)) = true := by decide +kernel
theorem cA_2_7 : ch7.all (rowA (75 * 269 ^ 4)) = true := by decide +kernel
theorem cA_2_8 : ch8.all (rowA (75 * 269 ^ 4)) = true := by decide +kernel
theorem cA_2_9 : ch9.all (rowA (75 * 269 ^ 4)) = true := by decide +kernel
theorem cA_3_0 : ch0.all (rowA (83 * 269 ^ 4)) = true := by decide +kernel
theorem cA_3_1 : ch1.all (rowA (83 * 269 ^ 4)) = true := by decide +kernel
theorem cA_3_2 : ch2.all (rowA (83 * 269 ^ 4)) = true := by decide +kernel
theorem cA_3_3 : ch3.all (rowA (83 * 269 ^ 4)) = true := by decide +kernel
theorem cA_3_4 : ch4.all (rowA (83 * 269 ^ 4)) = true := by decide +kernel
theorem cA_3_5 : ch5.all (rowA (83 * 269 ^ 4)) = true := by decide +kernel
theorem cA_3_6 : ch6.all (rowA (83 * 269 ^ 4)) = true := by decide +kernel
theorem cA_3_7 : ch7.all (rowA (83 * 269 ^ 4)) = true := by decide +kernel
theorem cA_3_8 : ch8.all (rowA (83 * 269 ^ 4)) = true := by decide +kernel
theorem cA_3_9 : ch9.all (rowA (83 * 269 ^ 4)) = true := by decide +kernel
theorem cA_4_0 : ch0.all (rowA (98 * 269 ^ 4)) = true := by decide +kernel
theorem cA_4_1 : ch1.all (rowA (98 * 269 ^ 4)) = true := by decide +kernel
theorem cA_4_2 : ch2.all (rowA (98 * 269 ^ 4)) = true := by decide +kernel
theorem cA_4_3 : ch3.all (rowA (98 * 269 ^ 4)) = true := by decide +kernel
theorem cA_4_4 : ch4.all (rowA (98 * 269 ^ 4)) = true := by decide +kernel
theorem cA_4_5 : ch5.all (rowA (98 * 269 ^ 4)) = true := by decide +kernel
theorem cA_4_6 : ch6.all (rowA (98 * 269 ^ 4)) = true := by decide +kernel
theorem cA_4_7 : ch7.all (rowA (98 * 269 ^ 4)) = true := by decide +kernel
theorem cA_4_8 : ch8.all (rowA (98 * 269 ^ 4)) = true := by decide +kernel
theorem cA_4_9 : ch9.all (rowA (98 * 269 ^ 4)) = true := by decide +kernel
theorem cA_5_0 : ch0.all (rowA (101 * 269 ^ 4)) = true := by decide +kernel
theorem cA_5_1 : ch1.all (rowA (101 * 269 ^ 4)) = true := by decide +kernel
theorem cA_5_2 : ch2.all (rowA (101 * 269 ^ 4)) = true := by decide +kernel
theorem cA_5_3 : ch3.all (rowA (101 * 269 ^ 4)) = true := by decide +kernel
theorem cA_5_4 : ch4.all (rowA (101 * 269 ^ 4)) = true := by decide +kernel
theorem cA_5_5 : ch5.all (rowA (101 * 269 ^ 4)) = true := by decide +kernel
theorem cA_5_6 : ch6.all (rowA (101 * 269 ^ 4)) = true := by decide +kernel
theorem cA_5_7 : ch7.all (rowA (101 * 269 ^ 4)) = true := by decide +kernel
theorem cA_5_8 : ch8.all (rowA (101 * 269 ^ 4)) = true := by decide +kernel
theorem cA_5_9 : ch9.all (rowA (101 * 269 ^ 4)) = true := by decide +kernel
theorem cA_6_0 : ch0.all (rowA (117 * 269 ^ 4)) = true := by decide +kernel
theorem cA_6_1 : ch1.all (rowA (117 * 269 ^ 4)) = true := by decide +kernel
theorem cA_6_2 : ch2.all (rowA (117 * 269 ^ 4)) = true := by decide +kernel
theorem cA_6_3 : ch3.all (rowA (117 * 269 ^ 4)) = true := by decide +kernel
theorem cA_6_4 : ch4.all (rowA (117 * 269 ^ 4)) = true := by decide +kernel
theorem cA_6_5 : ch5.all (rowA (117 * 269 ^ 4)) = true := by decide +kernel
theorem cA_6_6 : ch6.all (rowA (117 * 269 ^ 4)) = true := by decide +kernel
theorem cA_6_7 : ch7.all (rowA (117 * 269 ^ 4)) = true := by decide +kernel
theorem cA_6_8 : ch8.all (rowA (117 * 269 ^ 4)) = true := by decide +kernel
theorem cA_6_9 : ch9.all (rowA (117 * 269 ^ 4)) = true := by decide +kernel
theorem cA_7_0 : ch0.all (rowA (119 * 269 ^ 4)) = true := by decide +kernel
theorem cA_7_1 : ch1.all (rowA (119 * 269 ^ 4)) = true := by decide +kernel
theorem cA_7_2 : ch2.all (rowA (119 * 269 ^ 4)) = true := by decide +kernel
theorem cA_7_3 : ch3.all (rowA (119 * 269 ^ 4)) = true := by decide +kernel
theorem cA_7_4 : ch4.all (rowA (119 * 269 ^ 4)) = true := by decide +kernel
theorem cA_7_5 : ch5.all (rowA (119 * 269 ^ 4)) = true := by decide +kernel
theorem cA_7_6 : ch6.all (rowA (119 * 269 ^ 4)) = true := by decide +kernel
theorem cA_7_7 : ch7.all (rowA (119 * 269 ^ 4)) = true := by decide +kernel
theorem cA_7_8 : ch8.all (rowA (119 * 269 ^ 4)) = true := by decide +kernel
theorem cA_7_9 : ch9.all (rowA (119 * 269 ^ 4)) = true := by decide +kernel
theorem cA_8_0 : ch0.all (rowA (121 * 269 ^ 4)) = true := by decide +kernel
theorem cA_8_1 : ch1.all (rowA (121 * 269 ^ 4)) = true := by decide +kernel
theorem cA_8_2 : ch2.all (rowA (121 * 269 ^ 4)) = true := by decide +kernel
theorem cA_8_3 : ch3.all (rowA (121 * 269 ^ 4)) = true := by decide +kernel
theorem cA_8_4 : ch4.all (rowA (121 * 269 ^ 4)) = true := by decide +kernel
theorem cA_8_5 : ch5.all (rowA (121 * 269 ^ 4)) = true := by decide +kernel
theorem cA_8_6 : ch6.all (rowA (121 * 269 ^ 4)) = true := by decide +kernel
theorem cA_8_7 : ch7.all (rowA (121 * 269 ^ 4)) = true := by decide +kernel
theorem cA_8_8 : ch8.all (rowA (121 * 269 ^ 4)) = true := by decide +kernel
theorem cA_8_9 : ch9.all (rowA (121 * 269 ^ 4)) = true := by decide +kernel
theorem cA_9_0 : ch0.all (rowA (159 * 269 ^ 4)) = true := by decide +kernel
theorem cA_9_1 : ch1.all (rowA (159 * 269 ^ 4)) = true := by decide +kernel
theorem cA_9_2 : ch2.all (rowA (159 * 269 ^ 4)) = true := by decide +kernel
theorem cA_9_3 : ch3.all (rowA (159 * 269 ^ 4)) = true := by decide +kernel
theorem cA_9_4 : ch4.all (rowA (159 * 269 ^ 4)) = true := by decide +kernel
theorem cA_9_5 : ch5.all (rowA (159 * 269 ^ 4)) = true := by decide +kernel
theorem cA_9_6 : ch6.all (rowA (159 * 269 ^ 4)) = true := by decide +kernel
theorem cA_9_7 : ch7.all (rowA (159 * 269 ^ 4)) = true := by decide +kernel
theorem cA_9_8 : ch8.all (rowA (159 * 269 ^ 4)) = true := by decide +kernel
theorem cA_9_9 : ch9.all (rowA (159 * 269 ^ 4)) = true := by decide +kernel
theorem cA_10_0 : ch0.all (rowA (269 * 269 ^ 4)) = true := by decide +kernel
theorem cA_10_1 : ch1.all (rowA (269 * 269 ^ 4)) = true := by decide +kernel
theorem cA_10_2 : ch2.all (rowA (269 * 269 ^ 4)) = true := by decide +kernel
theorem cA_10_3 : ch3.all (rowA (269 * 269 ^ 4)) = true := by decide +kernel
theorem cA_10_4 : ch4.all (rowA (269 * 269 ^ 4)) = true := by decide +kernel
theorem cA_10_5 : ch5.all (rowA (269 * 269 ^ 4)) = true := by decide +kernel
theorem cA_10_6 : ch6.all (rowA (269 * 269 ^ 4)) = true := by decide +kernel
theorem cA_10_7 : ch7.all (rowA (269 * 269 ^ 4)) = true := by decide +kernel
theorem cA_10_8 : ch8.all (rowA (269 * 269 ^ 4)) = true := by decide +kernel
theorem cA_10_9 : ch9.all (rowA (269 * 269 ^ 4)) = true := by decide +kernel

theorem cB_0 : rowB (0 * 269 ^ 4) = true := by decide +kernel
theorem cB_1 : rowB (49 * 269 ^ 4) = true := by decide +kernel
theorem cB_2 : rowB (75 * 269 ^ 4) = true := by decide +kernel
theorem cB_3 : rowB (83 * 269 ^ 4) = true := by decide +kernel
theorem cB_4 : rowB (98 * 269 ^ 4) = true := by decide +kernel
theorem cB_5 : rowB (101 * 269 ^ 4) = true := by decide +kernel
theorem cB_6 : rowB (117 * 269 ^ 4) = true := by decide +kernel
theorem cB_7 : rowB (119 * 269 ^ 4) = true := by decide +kernel
theorem cB_8 : rowB (121 * 269 ^ 4) = true := by decide +kernel
theorem cB_9 : rowB (159 * 269 ^ 4) = true := by decide +kernel
theorem cB_10 : rowB (269 * 269 ^ 4) = true := by decide +kernel

lemma rowA_all {o : ℤ} (ho : o ∈ Oz) {s2 : Option (ℤ × ℕ)} (hs2 : s2 ∈ slots) :
    rowA (o * 269 ^ 4) s2 = true := by
  have key : ∀ ch : List (Option (ℤ × ℕ)), ch.all (rowA (o * 269 ^ 4)) = true → s2 ∈ ch →
      rowA (o * 269 ^ 4) s2 = true := fun ch hch hs => List.all_eq_true.1 hch s2 hs
  rw [slots_eq] at hs2
  simp only [List.mem_append] at hs2
  simp only [Oz, Finset.mem_insert, Finset.mem_singleton] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hs2 with h | h | h | h | h | h | h | h | h | h
  · exact key _ cA_0_0 h
  · exact key _ cA_0_1 h
  · exact key _ cA_0_2 h
  · exact key _ cA_0_3 h
  · exact key _ cA_0_4 h
  · exact key _ cA_0_5 h
  · exact key _ cA_0_6 h
  · exact key _ cA_0_7 h
  · exact key _ cA_0_8 h
  · exact key _ cA_0_9 h
  · exact key _ cA_1_0 h
  · exact key _ cA_1_1 h
  · exact key _ cA_1_2 h
  · exact key _ cA_1_3 h
  · exact key _ cA_1_4 h
  · exact key _ cA_1_5 h
  · exact key _ cA_1_6 h
  · exact key _ cA_1_7 h
  · exact key _ cA_1_8 h
  · exact key _ cA_1_9 h
  · exact key _ cA_2_0 h
  · exact key _ cA_2_1 h
  · exact key _ cA_2_2 h
  · exact key _ cA_2_3 h
  · exact key _ cA_2_4 h
  · exact key _ cA_2_5 h
  · exact key _ cA_2_6 h
  · exact key _ cA_2_7 h
  · exact key _ cA_2_8 h
  · exact key _ cA_2_9 h
  · exact key _ cA_3_0 h
  · exact key _ cA_3_1 h
  · exact key _ cA_3_2 h
  · exact key _ cA_3_3 h
  · exact key _ cA_3_4 h
  · exact key _ cA_3_5 h
  · exact key _ cA_3_6 h
  · exact key _ cA_3_7 h
  · exact key _ cA_3_8 h
  · exact key _ cA_3_9 h
  · exact key _ cA_4_0 h
  · exact key _ cA_4_1 h
  · exact key _ cA_4_2 h
  · exact key _ cA_4_3 h
  · exact key _ cA_4_4 h
  · exact key _ cA_4_5 h
  · exact key _ cA_4_6 h
  · exact key _ cA_4_7 h
  · exact key _ cA_4_8 h
  · exact key _ cA_4_9 h
  · exact key _ cA_5_0 h
  · exact key _ cA_5_1 h
  · exact key _ cA_5_2 h
  · exact key _ cA_5_3 h
  · exact key _ cA_5_4 h
  · exact key _ cA_5_5 h
  · exact key _ cA_5_6 h
  · exact key _ cA_5_7 h
  · exact key _ cA_5_8 h
  · exact key _ cA_5_9 h
  · exact key _ cA_6_0 h
  · exact key _ cA_6_1 h
  · exact key _ cA_6_2 h
  · exact key _ cA_6_3 h
  · exact key _ cA_6_4 h
  · exact key _ cA_6_5 h
  · exact key _ cA_6_6 h
  · exact key _ cA_6_7 h
  · exact key _ cA_6_8 h
  · exact key _ cA_6_9 h
  · exact key _ cA_7_0 h
  · exact key _ cA_7_1 h
  · exact key _ cA_7_2 h
  · exact key _ cA_7_3 h
  · exact key _ cA_7_4 h
  · exact key _ cA_7_5 h
  · exact key _ cA_7_6 h
  · exact key _ cA_7_7 h
  · exact key _ cA_7_8 h
  · exact key _ cA_7_9 h
  · exact key _ cA_8_0 h
  · exact key _ cA_8_1 h
  · exact key _ cA_8_2 h
  · exact key _ cA_8_3 h
  · exact key _ cA_8_4 h
  · exact key _ cA_8_5 h
  · exact key _ cA_8_6 h
  · exact key _ cA_8_7 h
  · exact key _ cA_8_8 h
  · exact key _ cA_8_9 h
  · exact key _ cA_9_0 h
  · exact key _ cA_9_1 h
  · exact key _ cA_9_2 h
  · exact key _ cA_9_3 h
  · exact key _ cA_9_4 h
  · exact key _ cA_9_5 h
  · exact key _ cA_9_6 h
  · exact key _ cA_9_7 h
  · exact key _ cA_9_8 h
  · exact key _ cA_9_9 h
  · exact key _ cA_10_0 h
  · exact key _ cA_10_1 h
  · exact key _ cA_10_2 h
  · exact key _ cA_10_3 h
  · exact key _ cA_10_4 h
  · exact key _ cA_10_5 h
  · exact key _ cA_10_6 h
  · exact key _ cA_10_7 h
  · exact key _ cA_10_8 h
  · exact key _ cA_10_9 h

lemma rowB_all {o : ℤ} (ho : o ∈ Oz) : rowB (o * 269 ^ 4) = true := by
  simp only [Oz, Finset.mem_insert, Finset.mem_singleton] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cB_0
  · exact cB_1
  · exact cB_2
  · exact cB_3
  · exact cB_4
  · exact cB_5
  · exact cB_6
  · exact cB_7
  · exact cB_8
  · exact cB_9
  · exact cB_10

/-- `φ^[j] o`, scaled by `269 ^ j`, for an integer `o`. -/
def hz : ℕ → ℤ → ℤ
  | 0, o => o
  | j + 1, o => 101 * 269 ^ (j + 1) + 18 * hz j o

lemma iterate_mul (j : ℕ) (o : ℤ) : φ^[j] (o : ℚ) * 269 ^ j = hz j o := by
  induction j with
  | zero => simp [hz]
  | succ j ih =>
    rw [Function.iterate_succ_apply', hz]
    push_cast
    rw [← ih]
    simp only [φ]
    ring

lemma P_cover : ∀ o ∈ Oz, ∀ j ∈ [0, 1, 2, 3], ∃ p ∈ P, p.1 = hz j o * 269 ^ (4 - j) := by
  decide +kernel

lemma P_low : ∀ p ∈ P, p.2 < 2 → ∃ o ∈ Oz, p.1 = o * 269 ^ 4 ∨ p.1 = hz 1 o * 269 ^ 3 := by
  decide +kernel

lemma iter4 (z : ℚ) : φ^[4] z * 269 ^ 4 = 566761505555 + 104976 * z := by
  simp only [Function.iterate_succ, Function.comp, Function.iterate_zero, id, φ]
  ring

/-- `s` represents the point `y` (scaled by `269 ^ 4`). -/
def Rep : Option (ℤ × ℕ) → ℚ → Prop
  | none, y => (LO : ℚ) ≤ y * 269 ^ 4 ∧ y * 269 ^ 4 ≤ HI
  | some (v, d), y => y * 269 ^ 4 = v ∧ (d < 2 → y ∈ S 1)

lemma Rep.bounds {s : Option (ℤ × ℕ)} {y : ℚ} (h : Rep s y) :
    (lb s : ℚ) ≤ y * 269 ^ 4 ∧ y * 269 ^ 4 ≤ ub s := by
  rcases s with _ | ⟨v, d⟩
  · exact h
  · simp only [Rep] at h
    simp [lb, ub, h.1]

lemma Rep.shallow {s : Option (ℤ × ℕ)} {y : ℚ} (h : Rep s y) (hd : deep s = false) :
    y ∈ S 1 := by
  rcases s with _ | ⟨v, d⟩
  · simp [deep] at hd
  · simp only [deep, decide_eq_false_iff_not, not_le] at hd
    exact h.2 hd

lemma Rep.eq {s t : Option (ℤ × ℕ)} {y z : ℚ} (hs : Rep s y) (ht : Rep t z)
    (h : same s t = true) : y = z := by
  rcases s with _ | ⟨u, d⟩ <;> rcases t with _ | ⟨v, e⟩ <;> simp [same] at h
  simp only [Rep] at hs ht
  have : y * 269 ^ 4 = z * 269 ^ 4 := by rw [hs.1, ht.1, h]
  exact mul_right_cancel₀ (by norm_num) this

lemma mem_S1_of {y : ℚ} {o : ℤ} (ho : o ∈ Oz)
    (h : y * 269 ^ 4 = (o : ℚ) * 269 ^ 4 ∨ y * 269 ^ 4 = (hz 1 o : ℚ) * 269 ^ 3) : y ∈ S 1 := by
  rcases h with h | h
  · have : y = o := mul_right_cancel₀ (by norm_num) h
    exact O_sub_S 1 (this ▸ intCast_mem_O ho)
  · rw [← iterate_mul 1 o] at h
    have h' : y * 269 ^ 4 = φ^[1] (o : ℚ) * 269 ^ 4 := by rw [h]; ring
    have : y = φ^[1] o := mul_right_cancel₀ (show (269 : ℚ) ^ 4 ≠ 0 by norm_num) h'
    exact mem_S_succ.2 (Or.inr ⟨o, intCast_mem_O ho, this.symm⟩)

lemma exists_rep {n : ℕ} {y : ℚ} (hy : y ∈ S n) : ∃ s ∈ slots, Rep s y := by
  rcases decomp 3 n y hy with ⟨j, hj, o, ho, rfl⟩ | ⟨z, h0, h1, rfl⟩
  · obtain ⟨oz, hoz, rfl⟩ := mem_O.1 ho
    have hj' : j ∈ [0, 1, 2, 3] := by interval_cases j <;> simp
    obtain ⟨⟨v, d⟩, hp, hv⟩ := P_cover oz hoz j hj'
    simp only at hv
    have hval : φ^[j] (oz : ℚ) * 269 ^ 4 = v := by
      calc φ^[j] (oz : ℚ) * 269 ^ 4 = (φ^[j] (oz : ℚ) * 269 ^ j) * 269 ^ (4 - j) := by
            rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega : j ≤ 4)]
        _ = v := by rw [iterate_mul, hv]; push_cast; ring
    refine ⟨some (v, d), List.mem_cons_of_mem _ (List.mem_map_of_mem hp), hval, fun hd => ?_⟩
    obtain ⟨o', ho', h'⟩ := P_low (v, d) hp hd
    simp only at h'
    apply mem_S1_of ho'
    rcases h' with h' | h'
    · left; rw [hval, h']; push_cast; ring
    · right; rw [hval, h']; push_cast; ring
  · refine ⟨none, List.mem_cons_self, ?_⟩
    show (LO : ℚ) ≤ φ^[4] z * 269 ^ 4 ∧ φ^[4] z * 269 ^ 4 ≤ HI
    rw [iter4]
    simp only [LO, HI]
    push_cast
    constructor <;> linarith

lemma okA_spec {x1 : ℤ} {s2 s3 s4 : Option (ℤ × ℕ)} (h : okA x1 s2 s3 s4 = true) :
    (deep s2 = false ∧ deep s3 = false ∧ deep s4 = false) ∨
    (same (some (x1, 0)) s2 = true ∨ same (some (x1, 0)) s3 = true ∨
      same (some (x1, 0)) s4 = true ∨ same s2 s3 = true ∨ same s2 s4 = true ∨
      same s3 s4 = true) ∨
    (0 < x1 + lb s2 - ub s3 - ub s4 ∨ x1 + ub s2 - lb s3 - lb s4 < 0) := by
  simp only [okA] at h
  by_cases h1 : (!(deep s2 || deep s3 || deep s4)) = true
  · left; simpa [and_assoc] using h1
  · rw [if_neg h1] at h
    by_cases h2 : (same (some (x1, 0)) s2 || same (some (x1, 0)) s3 || same (some (x1, 0)) s4 ||
        same s2 s3 || same s2 s4 || same s3 s4) = true
    · right; left; simpa [Bool.or_eq_true, or_assoc] using h2
    · rw [if_neg h2] at h
      right; right
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le] at h
      omega

lemma okB1_spec {x1 : ℤ} {s2 s3 : Option (ℤ × ℕ)} (h : okB1 x1 s2 s3 = true) :
    (deep s2 = false ∧ deep s3 = false) ∨ same (some (x1, 0)) s3 = true ∨
    (0 < x1 + lb s3 - 2 * ub s2 ∨ x1 + ub s3 - 2 * lb s2 < 0) := by
  unfold okB1 at h
  cases hd2 : deep s2 <;> cases hd3 : deep s3 <;> cases hs : same (some (x1, 0)) s3 <;> simp_all [not_le]

lemma okB2_spec {x2 : ℤ} {s1 s3 : Option (ℤ × ℕ)} (h : okB2 x2 s1 s3 = true) :
    (deep s1 = false ∧ deep s3 = false) ∨ same s1 s3 = true ∨
    (0 < lb s1 + lb s3 - 2 * x2 ∨ ub s1 + ub s3 - 2 * x2 < 0) := by
  unfold okB2 at h
  cases hd2 : deep s1 <;> cases hd3 : deep s3 <;> cases hs : same s1 s3 <;> simp_all [not_le]

lemma rep_O {o : ℤ} (ho : o ∈ Oz) : Rep (some (o * 269 ^ 4, 0)) (o : ℚ) :=
  ⟨by push_cast; ring, fun _ => O_sub_S 1 (intCast_mem_O ho)⟩

theorem nmA {n : ℕ} {a b c d : ℚ} (ha : a ∈ O) (hb : b ∈ S n) (hc : c ∈ S n) (hd : d ∈ S n)
    (h : a + b = c + d) (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) :
    b ∈ S 1 ∧ c ∈ S 1 ∧ d ∈ S 1 := by
  obtain ⟨oz, hoz, rfl⟩ := mem_O.1 ha
  have r1 := rep_O hoz
  obtain ⟨s2, hs2, r2⟩ := exists_rep hb
  obtain ⟨s3, hs3, r3⟩ := exists_rep hc
  obtain ⟨s4, hs4, r4⟩ := exists_rep hd
  have hchk : okA (oz * 269 ^ 4) s2 s3 s4 = true := by
    have := rowA_all hoz hs2
    simp only [rowA, List.all_eq_true] at this
    exact this s3 hs3 s4 hs4
  rcases okA_spec hchk with ⟨d2, d3, d4⟩ | hsame | hint
  · exact ⟨r2.shallow d2, r3.shallow d3, r4.shallow d4⟩
  · exfalso
    have hbd : b ≠ d := fun e => hac (by linarith)
    have hbc : b ≠ c := fun e => had (by linarith)
    rcases hsame with e | e | e | e | e | e
    · exact hab (r1.eq r2 e)
    · exact hac (r1.eq r3 e)
    · exact had (r1.eq r4 e)
    · exact hbc (r2.eq r3 e)
    · exact hbd (r2.eq r4 e)
    · exact hcd (r3.eq r4 e)
  · exfalso
    have b1 := r1.bounds; have b2 := r2.bounds; have b3 := r3.bounds; have b4 := r4.bounds
    simp only [lb, ub] at b1
    have key : (oz : ℚ) * 269 ^ 4 + b * 269 ^ 4 = c * 269 ^ 4 + d * 269 ^ 4 := by
      rw [← add_mul, ← add_mul, h]
    rcases hint with hi | hi
    · have : ((oz * 269 ^ 4 + lb s2 - ub s3 - ub s4 : ℤ) : ℚ) ≤ 0 := by push_cast; linarith
      have : ((oz * 269 ^ 4 + lb s2 - ub s3 - ub s4 : ℤ) : ℚ) > 0 := by exact_mod_cast hi
      linarith
    · have : ((oz * 269 ^ 4 + ub s2 - lb s3 - lb s4 : ℤ) : ℚ) ≥ 0 := by push_cast; linarith
      have : ((oz * 269 ^ 4 + ub s2 - lb s3 - lb s4 : ℤ) : ℚ) < 0 := by exact_mod_cast hi
      linarith

/-- A progression `a, b, c` (`a + c = 2 b`) with the endpoint `a` in `O` stays in `S 1`. -/
theorem nmB1 {n : ℕ} {a b c : ℚ} (ha : a ∈ O) (hb : b ∈ S n) (hc : c ∈ S n)
    (h : a + c = 2 * b) (hac : a ≠ c) : b ∈ S 1 ∧ c ∈ S 1 := by
  obtain ⟨oz, hoz, rfl⟩ := mem_O.1 ha
  have r1 := rep_O hoz
  obtain ⟨s2, hs2, r2⟩ := exists_rep hb
  obtain ⟨s3, hs3, r3⟩ := exists_rep hc
  have hchk : okB1 (oz * 269 ^ 4) s2 s3 = true := by
    have := rowB_all hoz
    simp only [rowB, List.all_eq_true, Bool.and_eq_true] at this
    exact (this s2 hs2 s3 hs3).1
  rcases okB1_spec hchk with ⟨d2, d3⟩ | e | hint
  · exact ⟨r2.shallow d2, r3.shallow d3⟩
  · exact absurd (r1.eq r3 e) hac
  · exfalso
    have b1 := r1.bounds; have b2 := r2.bounds; have b3 := r3.bounds
    simp only [lb, ub] at b1
    have key : (oz : ℚ) * 269 ^ 4 + c * 269 ^ 4 = 2 * (b * 269 ^ 4) := by
      rw [← add_mul, h]; ring
    rcases hint with hi | hi
    · have : ((oz * 269 ^ 4 + lb s3 - 2 * ub s2 : ℤ) : ℚ) ≤ 0 := by push_cast; linarith
      have : ((oz * 269 ^ 4 + lb s3 - 2 * ub s2 : ℤ) : ℚ) > 0 := by exact_mod_cast hi
      linarith
    · have : ((oz * 269 ^ 4 + ub s3 - 2 * lb s2 : ℤ) : ℚ) ≥ 0 := by push_cast; linarith
      have : ((oz * 269 ^ 4 + ub s3 - 2 * lb s2 : ℤ) : ℚ) < 0 := by exact_mod_cast hi
      linarith

/-- A progression `a, b, c` (`a + c = 2 b`) with the middle `b` in `O` stays in `S 1`. -/
theorem nmB2 {n : ℕ} {a b c : ℚ} (hb : b ∈ O) (ha : a ∈ S n) (hc : c ∈ S n)
    (h : a + c = 2 * b) (hac : a ≠ c) : a ∈ S 1 ∧ c ∈ S 1 := by
  obtain ⟨oz, hoz, rfl⟩ := mem_O.1 hb
  have r2 := rep_O hoz
  obtain ⟨s1, hs1, r1⟩ := exists_rep ha
  obtain ⟨s3, hs3, r3⟩ := exists_rep hc
  have hchk : okB2 (oz * 269 ^ 4) s1 s3 = true := by
    have := rowB_all hoz
    simp only [rowB, List.all_eq_true, Bool.and_eq_true] at this
    exact (this s1 hs1 s3 hs3).2
  rcases okB2_spec hchk with ⟨d1, d3⟩ | e | hint
  · exact ⟨r1.shallow d1, r3.shallow d3⟩
  · exact absurd (r1.eq r3 e) hac
  · exfalso
    have b1 := r1.bounds; have b2 := r2.bounds; have b3 := r3.bounds
    simp only [lb, ub] at b2
    have key : a * 269 ^ 4 + c * 269 ^ 4 = 2 * ((oz : ℚ) * 269 ^ 4) := by
      rw [← add_mul, h]; ring
    rcases hint with hi | hi
    · have : ((lb s1 + lb s3 - 2 * (oz * 269 ^ 4) : ℤ) : ℚ) ≤ 0 := by push_cast; linarith
      have : ((lb s1 + lb s3 - 2 * (oz * 269 ^ 4) : ℤ) : ℚ) > 0 := by exact_mod_cast hi
      linarith
    · have : ((ub s1 + ub s3 - 2 * (oz * 269 ^ 4) : ℤ) : ℚ) ≥ 0 := by push_cast; linarith
      have : ((ub s1 + ub s3 - 2 * (oz * 269 ^ 4) : ℤ) : ℚ) < 0 := by exact_mod_cast hi
      linarith

/-- A 3-term progression through a point of `O` lies in `S 1`. -/
theorem nmT {n : ℕ} {x y u : ℚ} (hx : x ∈ S n) (hy : y ∈ S n) (hu : u ∈ S n) (hxy : x ≠ y)
    (hc : IsComp x y u) (hO : x ∈ O ∨ y ∈ O ∨ u ∈ O) : x ∈ S 1 ∧ y ∈ S 1 ∧ u ∈ S 1 := by
  have hO1 : ∀ {w : ℚ}, w ∈ O → w ∈ S 1 := fun hw => O_sub_S 1 hw
  rcases hc with h | h | h
  · -- endpoints u, x; middle y
    have hux : u ≠ x := fun e => hxy (by linarith)
    rcases hO with h' | h' | h'
    · obtain ⟨h1, h2⟩ := nmB1 h' hy hu (by linarith) (Ne.symm hux)
      exact ⟨hO1 h', h1, h2⟩
    · obtain ⟨h1, h2⟩ := nmB2 h' hu hx h hux
      exact ⟨h2, hO1 h', h1⟩
    · obtain ⟨h1, h2⟩ := nmB1 h' hy hx h hux
      exact ⟨h2, h1, hO1 h'⟩
  · -- endpoints u, y; middle x
    have huy : u ≠ y := fun e => hxy (by linarith)
    rcases hO with h' | h' | h'
    · obtain ⟨h1, h2⟩ := nmB2 h' hu hy h huy
      exact ⟨hO1 h', h2, h1⟩
    · obtain ⟨h1, h2⟩ := nmB1 h' hx hu (by linarith) (Ne.symm huy)
      exact ⟨h1, hO1 h', h2⟩
    · obtain ⟨h1, h2⟩ := nmB1 h' hx hy h huy
      exact ⟨h1, h2, hO1 h'⟩
  · -- endpoints x, y; middle u
    rcases hO with h' | h' | h'
    · obtain ⟨h1, h2⟩ := nmB1 h' hu hy h hxy
      exact ⟨hO1 h', h2, h1⟩
    · obtain ⟨h1, h2⟩ := nmB1 h' hu hx (by linarith) (Ne.symm hxy)
      exact ⟨h2, hO1 h', h1⟩
    · obtain ⟨h1, h2⟩ := nmB2 h' hx hy h hxy
      exact ⟨h1, h2, hO1 h'⟩


/- ## `S 2` (29 points) has neither forbidden pattern: a finite check -/

/-- The points of `S 2`, scaled by `269 ^ 2`. -/
def D2 : List ℤ := [0, 3545689, 5427075, 6005963, 7091378, 7308461, 7545719, 7671611, 7710347, 7782977, 7797503, 7813379, 7821803, 7824395, 7829255, 7830227, 7835411, 7836059, 7836707, 7849019, 7874975, 7884659, 7894343, 8078339, 8466237, 8610959, 8755681, 11505399, 19465109]

lemma D2_cover : ∀ o ∈ Oz, ∀ j ∈ [0, 1, 2], hz j o * 269 ^ (2 - j) ∈ D2 := by decide +kernel

lemma exists_D2 {y : ℚ} (hy : y ∈ S 2) : ∃ v ∈ D2, y * 269 ^ 2 = v := by
  have : ∃ j ∈ [0, 1, 2], ∃ o ∈ Oz, y = φ^[j] (o : ℚ) := by
    rcases mem_S_succ.1 hy with h | ⟨z, hz, rfl⟩
    · obtain ⟨o, ho, rfl⟩ := mem_O.1 h; exact ⟨0, by simp, o, ho, rfl⟩
    · rcases mem_S_succ.1 hz with h | ⟨w, hw, rfl⟩
      · obtain ⟨o, ho, rfl⟩ := mem_O.1 h; exact ⟨1, by simp, o, ho, rfl⟩
      · obtain ⟨o, ho, rfl⟩ := mem_O.1 hw; exact ⟨2, by simp, o, ho, rfl⟩
  obtain ⟨j, hj, o, ho, rfl⟩ := this
  refine ⟨hz j o * 269 ^ (2 - j), D2_cover o ho j hj, ?_⟩
  have hj2 : j ≤ 2 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega
  calc φ^[j] (o : ℚ) * 269 ^ 2 = (φ^[j] (o : ℚ) * 269 ^ j) * 269 ^ (2 - j) := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hj2]
    _ = _ := by rw [iterate_mul]; push_cast; ring

/-- Pairs `a < b` of points of `D2`. -/
def pairs2 : List (ℤ × ℤ) := D2.flatMap fun a => (D2.filter (fun b => decide (a < b))).map (a, ·)

lemma mem_pairs2 {a b : ℤ} (ha : a ∈ D2) (hb : b ∈ D2) (hab : a < b) : (a, b) ∈ pairs2 := by
  simp only [pairs2, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq,
    Prod.mk.injEq]
  exact ⟨a, ha, b, ⟨hb, hab⟩, rfl, rfl⟩

/-- The pairs whose sum lies in `[lo, hi)`. -/
def blk (lo hi : ℤ) : List (ℤ × ℤ) :=
  pairs2.filter (fun p => decide (lo ≤ p.1 + p.2 ∧ p.1 + p.2 < hi))

theorem blk_0 : ((blk 3545689 12011926).map fun p => p.1 + p.2).Nodup := by decide +kernel
theorem blk_1 : ((blk 12011926 14762989).map fun p => p.1 + p.2).Nodup := by decide +kernel
theorem blk_2 : ((blk 14762989 15430378).map fun p => p.1 + p.2).Nodup := by decide +kernel
theorem blk_3 : ((blk 15430378 15637774).map fun p => p.1 + p.2).Nodup := by decide +kernel
theorem blk_4 : ((blk 15637774 15707722).map fun p => p.1 + p.2).Nodup := by decide +kernel
theorem blk_5 : ((blk 15707722 16288040).map fun p => p.1 + p.2).Nodup := by decide +kernel
theorem blk_6 : ((blk 16288040 18596777).map fun p => p.1 + p.2).Nodup := by decide +kernel
theorem blk_7 : ((blk 18596777 30970509).map fun p => p.1 + p.2).Nodup := by decide +kernel

lemma pairs2_range : ∀ p ∈ pairs2, 3545689 ≤ p.1 + p.2 ∧ p.1 + p.2 < 30970509 := by decide +kernel

/-- Different pairs of points of `S 2` have different sums. -/
lemma pair_inj {p q : ℤ × ℤ} (hp : p ∈ pairs2) (hq : q ∈ pairs2) (h : p.1 + p.2 = q.1 + q.2) :
    p = q := by
  have key : ∀ lo hi : ℤ, ((blk lo hi).map fun p => p.1 + p.2).Nodup → lo ≤ p.1 + p.2 →
      p.1 + p.2 < hi → p = q := by
    intro lo hi hn h1 h2
    refine List.inj_on_of_nodup_map hn ?_ ?_ h
    · exact List.mem_filter.2 ⟨hp, by simp [h1, h2]⟩
    · exact List.mem_filter.2 ⟨hq, by simp [← h, h1, h2]⟩
  obtain ⟨r1, r2⟩ := pairs2_range p hp
  have : (3545689 ≤ p.1 + p.2 ∧ p.1 + p.2 < 12011926) ∨ (12011926 ≤ p.1 + p.2 ∧ p.1 + p.2 < 14762989) ∨ (14762989 ≤ p.1 + p.2 ∧ p.1 + p.2 < 15430378) ∨ (15430378 ≤ p.1 + p.2 ∧ p.1 + p.2 < 15637774) ∨ (15637774 ≤ p.1 + p.2 ∧ p.1 + p.2 < 15707722) ∨ (15707722 ≤ p.1 + p.2 ∧ p.1 + p.2 < 16288040) ∨ (16288040 ≤ p.1 + p.2 ∧ p.1 + p.2 < 18596777) ∨ (18596777 ≤ p.1 + p.2 ∧ p.1 + p.2 < 30970509) := by omega
  rcases this with h | h | h | h | h | h | h | h
  · exact key _ _ blk_0 h.1 h.2
  · exact key _ _ blk_1 h.1 h.2
  · exact key _ _ blk_2 h.1 h.2
  · exact key _ _ blk_3 h.1 h.2
  · exact key _ _ blk_4 h.1 h.2
  · exact key _ _ blk_5 h.1 h.2
  · exact key _ _ blk_6 h.1 h.2
  · exact key _ _ blk_7 h.1 h.2

/-- If `a + b = c + d` for points of `D2` with `a < b` and `c < d`, then `a = c`. -/
lemma sum_inj {a b c d : ℤ} (ha : a ∈ D2) (hb : b ∈ D2) (hc : c ∈ D2) (hd : d ∈ D2)
    (h : a + b = c + d) (hab : a < b) (hcd : c < d) : a = c := by
  have := pair_inj (mem_pairs2 ha hb hab) (mem_pairs2 hc hd hcd) h
  simp only [Prod.mk.injEq] at this
  exact this.1

def chkP2 : Bool := D2.all fun x => D2.all fun y =>
  x == y || decide ((D2.filter (fun u => u + x == 2 * y || u + y == 2 * x || x + y == 2 * u)).length ≤ 1)

theorem chkP2_ok : chkP2 = true := by decide +kernel

lemma two_le_length {l : List ℤ} {a b : ℤ} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    2 ≤ l.length := by
  classical
  have hsub : ({a, b} : Finset ℤ) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa
  calc 2 = ({a, b} : Finset ℤ).card := (Finset.card_pair hab).symm
    _ ≤ l.toFinset.card := Finset.card_le_card hsub
    _ ≤ l.length := List.toFinset_card_le l

lemma ne_of_scaled {y z : ℚ} {v w : ℤ} (hy : y * 269 ^ 2 = v) (hz : z * 269 ^ 2 = w)
    (h : y ≠ z) : v ≠ w := by
  intro e
  apply h
  have : y * 269 ^ 2 = z * 269 ^ 2 := by rw [hy, hz, e]
  exact mul_right_cancel₀ (by norm_num) this

theorem good_S2 : Good (S 2) := by
  constructor
  · intro a ha b hb c hc d hd h hab hcd hac had
    obtain ⟨va, hva, ea⟩ := exists_D2 ha
    obtain ⟨vb, hvb, eb⟩ := exists_D2 hb
    obtain ⟨vc, hvc, ec⟩ := exists_D2 hc
    obtain ⟨vd, hvd, ed⟩ := exists_D2 hd
    have hv : va + vb = vc + vd := by
      have : ((va + vb : ℤ) : ℚ) = ((vc + vd : ℤ) : ℚ) := by
        push_cast; rw [← ea, ← eb, ← ec, ← ed]; linear_combination (269 ^ 2 : ℚ) * h
      exact_mod_cast this
    have nab := ne_of_scaled ea eb hab
    have ncd := ne_of_scaled ec ed hcd
    have nac := ne_of_scaled ea ec hac
    have nad := ne_of_scaled ea ed had
    rcases lt_or_gt_of_ne nab with h1 | h1 <;> rcases lt_or_gt_of_ne ncd with h2 | h2
    · exact nac (sum_inj hva hvb hvc hvd hv h1 h2)
    · exact nad (sum_inj hva hvb hvd hvc (by linarith) h1 h2)
    · exact nad (by linarith [sum_inj hvb hva hvc hvd (by linarith) h1 h2])
    · exact nac (by linarith [sum_inj hvb hva hvd hvc (by linarith) h1 h2])
  · intro x hx y hy u hu v hv hxy huv hcu hcv
    obtain ⟨vx, hvx, ex⟩ := exists_D2 hx
    obtain ⟨vy, hvy, ey⟩ := exists_D2 hy
    obtain ⟨vu, hvu, eu⟩ := exists_D2 hu
    obtain ⟨vv, hvv, ev⟩ := exists_D2 hv
    have hchk := chkP2_ok
    simp only [chkP2, List.all_eq_true] at hchk
    have h1 := hchk vx hvx vy hvy
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    rcases h1 with e | hlen
    · exact ne_of_scaled ex ey hxy e
    · have hcomp : ∀ {w : ℚ} {vw : ℤ}, w * 269 ^ 2 = vw → IsComp x y w →
          vw ∈ D2 → vw ∈ D2.filter
            (fun u => u + vx == 2 * vy || u + vy == 2 * vx || vx + vy == 2 * u) := by
        intro w vw ew hc hvw
        rw [List.mem_filter]
        refine ⟨hvw, ?_⟩
        simp only [Bool.or_eq_true, beq_iff_eq]
        rcases hc with hc | hc | hc
        · left; left
          have : ((vw + vx : ℤ) : ℚ) = ((2 * vy : ℤ) : ℚ) := by
            push_cast; rw [← ew, ← ex, ← ey]; linear_combination (269 ^ 2 : ℚ) * hc
          exact_mod_cast this
        · left; right
          have : ((vw + vy : ℤ) : ℚ) = ((2 * vx : ℤ) : ℚ) := by
            push_cast; rw [← ew, ← ex, ← ey]; linear_combination (269 ^ 2 : ℚ) * hc
          exact_mod_cast this
        · right
          have : ((vx + vy : ℤ) : ℚ) = ((2 * vw : ℤ) : ℚ) := by
            push_cast; rw [← ew, ← ex, ← ey]; linear_combination (269 ^ 2 : ℚ) * hc
          exact_mod_cast this
      have := two_le_length (hcomp eu hcu hvu) (hcomp ev hcv hvv) (ne_of_scaled eu ev huv)
      omega

/- ## Every `S k` has neither forbidden pattern -/

lemma S_mono : ∀ k, S k ⊆ S (k + 1)
  | 0 => Finset.subset_union_left
  | k + 1 => Finset.union_subset_union (subset_refl _) (Finset.image_subset_image (S_mono k))

lemma φ_mem_S2 {z : ℚ} (hz : z ∈ S 1) : φ z ∈ S 2 := mem_S_succ.2 (Or.inr ⟨z, hz, rfl⟩)

/-- A point of `S 1` of the form `φ z` with `z ∈ S k` has `z ∈ O`. -/
lemma pre_S1 {k : ℕ} {x z : ℚ} (hx : x ∈ S 1) (hz : z ∈ S k) (h : φ z = x) : z ∈ O := by
  rcases mem_S_succ.1 hx with hxO | ⟨w, hw, rfl⟩
  · rcases O_inter hxO hz h with rfl | rfl
    exacts [zero_mem_O, mem_O_269]
  · rw [φ_inj h]; exact hw

lemma comp_pull {x y u : ℚ} (h : IsComp (φ x) (φ y) (φ u)) : IsComp x y u := by
  simp only [IsComp, φ] at h ⊢
  rcases h with h | h | h
  · left; linarith
  · right; left; linarith
  · right; right; linarith

theorem good_S : ∀ k, Good (S k)
  | 0 => good_S2.mono (fun _ hx => S_mono 1 (S_mono 0 hx))
  | k + 1 => by
    have ih := good_S k
    have hsplit : ∀ y ∈ S (k + 1), y ∈ O ∨ ∃ z ∈ S k, φ z = y := fun y hy => mem_S_succ.1 hy
    have hS1 : ∀ {y : ℚ}, y ∈ S 1 → y ∈ S 2 := fun hy => S_mono 1 hy
    have hO1 : ∀ {y : ℚ}, y ∈ O → y ∈ S 1 := fun hy => O_sub_S 1 hy
    constructor
    · intro a ha b hb c hc d hd h hab hcd hac had
      have hbc : b ≠ c := fun e => had (by linarith)
      have hbd : b ≠ d := fun e => hac (by linarith)
      by_cases hO : a ∈ O ∨ b ∈ O ∨ c ∈ O ∨ d ∈ O
      · have hall : a ∈ S 1 ∧ b ∈ S 1 ∧ c ∈ S 1 ∧ d ∈ S 1 := by
          rcases hO with h' | h' | h' | h'
          · obtain ⟨h2, h3, h4⟩ := nmA h' hb hc hd h hab hcd hac had
            exact ⟨hO1 h', h2, h3, h4⟩
          · obtain ⟨h2, h3, h4⟩ := nmA h' ha hc hd (by linarith) (Ne.symm hab) hcd hbc hbd
            exact ⟨h2, hO1 h', h3, h4⟩
          · obtain ⟨h2, h3, h4⟩ := nmA h' hd ha hb h.symm hcd hab (Ne.symm hac) (Ne.symm hbc)
            exact ⟨h3, h4, hO1 h', h2⟩
          · obtain ⟨h2, h3, h4⟩ := nmA h' hc ha hb (by linarith) (Ne.symm hcd) hab
              (Ne.symm had) (Ne.symm hbd)
            exact ⟨h3, h4, h2, hO1 h'⟩
        exact good_S2.1 a (hS1 hall.1) b (hS1 hall.2.1) c (hS1 hall.2.2.1) d (hS1 hall.2.2.2)
          h hab hcd hac had
      · simp only [not_or] at hO
        obtain ⟨a', ha', rfl⟩ := (hsplit a ha).resolve_left hO.1
        obtain ⟨b', hb', rfl⟩ := (hsplit b hb).resolve_left hO.2.1
        obtain ⟨c', hc', rfl⟩ := (hsplit c hc).resolve_left hO.2.2.1
        obtain ⟨d', hd', rfl⟩ := (hsplit d hd).resolve_left hO.2.2.2
        exact ih.1 a' ha' b' hb' c' hc' d' hd' (by simp only [φ] at h; linarith)
          (fun e => hab (by rw [e])) (fun e => hcd (by rw [e])) (fun e => hac (by rw [e]))
          (fun e => had (by rw [e]))
    · intro x hx y hy u hu v hv hxy huv hcu hcv
      have hG2 := good_S2.2
      by_cases hOu : x ∈ O ∨ y ∈ O ∨ u ∈ O
      · obtain ⟨hx1, hy1, hu1⟩ := nmT hx hy hu hxy hcu hOu
        by_cases hOv : x ∈ O ∨ y ∈ O ∨ v ∈ O
        · obtain ⟨-, -, hv1⟩ := nmT hx hy hv hxy hcv hOv
          exact hG2 x (hS1 hx1) y (hS1 hy1) u (hS1 hu1) v (hS1 hv1) hxy huv hcu hcv
        · simp only [not_or] at hOv
          obtain ⟨x', hx', rfl⟩ := (hsplit x hx).resolve_left hOv.1
          obtain ⟨y', hy', rfl⟩ := (hsplit y hy).resolve_left hOv.2.1
          obtain ⟨v', hv', rfl⟩ := (hsplit v hv).resolve_left hOv.2.2
          obtain ⟨-, -, hv1⟩ := nmT hx' hy' hv' (fun e => hxy (by rw [e])) (comp_pull hcv)
            (Or.inl (pre_S1 hx1 hx' rfl))
          exact hG2 _ (hS1 hx1) _ (hS1 hy1) _ (hS1 hu1) _ (φ_mem_S2 hv1) hxy huv hcu hcv
      · simp only [not_or] at hOu
        obtain ⟨x', hx', rfl⟩ := (hsplit x hx).resolve_left hOu.1
        obtain ⟨y', hy', rfl⟩ := (hsplit y hy).resolve_left hOu.2.1
        obtain ⟨u', hu', rfl⟩ := (hsplit u hu).resolve_left hOu.2.2
        by_cases hOv : v ∈ O
        · obtain ⟨hx1, hy1, hv1⟩ := nmT hx hy hv hxy hcv (Or.inr (Or.inr hOv))
          obtain ⟨-, -, hu1⟩ := nmT hx' hy' hu' (fun e => hxy (by rw [e])) (comp_pull hcu)
            (Or.inl (pre_S1 hx1 hx' rfl))
          exact hG2 _ (hS1 hx1) _ (hS1 hy1) _ (φ_mem_S2 hu1) _ (hS1 hv1) hxy huv hcu hcv
        · obtain ⟨v', hv', rfl⟩ := (hsplit v hv).resolve_left hOv
          exact ih.2 x' hx' y' hy' u' hu' v' hv' (fun e => hxy (by rw [e]))
            (fun e => huv (by rw [e])) (comp_pull hcu) (comp_pull hcv)

/- ## The bound -/

/-- The cast `ℚ → ℝ` as an additive monoid hom. -/
noncomputable abbrev ι : ℚ →+ ℝ := (Rat.castHom ℝ).toAddMonoidHom

lemma ι_injective : Function.Injective ι := Rat.cast_injective

/-- The `k`-th set of the family, inside `ℝ`. -/
def A (k : ℕ) : Set ℝ := ι '' (S k : Set ℚ)

lemma A_finite (k : ℕ) : (A k).Finite := (S k).finite_toSet.image _

lemma ncard_A (k : ℕ) : (A k).ncard = 11 + 9 * k := by
  rw [A, Set.ncard_image_of_injective _ ι_injective, Set.ncard_coe_finset, card_S]

lemma exists_preimage {k : ℕ} {B : Set ℝ} (hB : B ⊆ A k) :
    ∃ B₀ : Finset ℚ, B₀ ⊆ S k ∧ B = ι '' (B₀ : Set ℚ) := by
  classical
  refine ⟨(S k).filter (fun z => ι z ∈ B), Finset.filter_subset _ _, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := hB hx
    exact ⟨z, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_coe.1 hz, hx⟩), rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 hz)).2

lemma is45 (k : ℕ) : ∀ B ⊆ A k, B.ncard = 4 → 11 ≤ (B - B).ncard := by
  intro B hB hcard
  obtain ⟨B₀, hB₀, rfl⟩ := exists_preimage hB
  rw [Set.ncard_image_of_injective _ ι_injective, Set.ncard_coe_finset] at hcard
  rw [← Set.image_sub, Set.ncard_image_of_injective _ ι_injective, ← Finset.coe_sub,
    Set.ncard_coe_finset]
  exact card45 ((good_S k).mono hB₀) hcard

lemma isSidon_preimage {S₀ : Finset ℚ} (h : IsSidon (ι '' (S₀ : Set ℚ))) :
    IsSidon (S₀ : Set ℚ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  have := h (ι i₁) ⟨i₁, hi₁, rfl⟩ (ι j₁) ⟨j₁, hj₁, rfl⟩ (ι i₂) ⟨i₂, hi₂, rfl⟩
    (ι j₂) ⟨j₂, hj₂, rfl⟩ (by rw [← map_add, ← map_add, hsum])
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨ι_injective h1, ι_injective h2⟩
  · exact Or.inr ⟨ι_injective h1, ι_injective h2⟩

lemma sidon_le (k : ℕ) {T : Set ℝ} (hT : T ⊆ A k) (hSid : IsSidon T) :
    T.ncard ≤ 7 + 5 * k := by
  obtain ⟨T₀, hT₀, rfl⟩ := exists_preimage hT
  rw [Set.ncard_image_of_injective _ ι_injective, Set.ncard_coe_finset]
  have := sidon_bound k T₀ hT₀ (isSidon_preimage hSid)
  omega

lemma admissible_le {c : ℝ} (hc : IsAdmissible c) : c ≤ 5 / 9 := by
  have key : ∀ k : ℕ, c * (11 + 9 * k) ≤ 7 + 5 * k := by
    intro k
    obtain ⟨T, hTA, hSid, hle⟩ := hc (A_finite k) (is45 k)
    have : (T.ncard : ℝ) ≤ 7 + 5 * k := by exact_mod_cast sidon_le k hTA hSid
    rw [ncard_A] at hle
    push_cast at hle
    linarith
  by_contra hlt
  push Not at hlt
  have hpos : 0 < 9 * c - 5 := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (9 * c - 5))
  have hk' : 1 < (k : ℝ) * (9 * c - 5) := (div_lt_iff₀ hpos).1 hk
  nlinarith [key k]

/-- **Erdős #757**: `sSup ≤ 5/9`, via the self-similar family `S k` (sizes `11 + 9 k`, largest
Sidon subsets at most `7 + 5 k`). -/
theorem sSup_le_five_ninths : sSup {c : ℝ | IsAdmissible c} ≤ 5 / 9 :=
  Real.sSup_le (fun c hc => admissible_le hc) (by norm_num)

end OpenProblemsLab.E757.FiveNinths
