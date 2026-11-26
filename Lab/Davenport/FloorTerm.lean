import Mathlib
import Lab.Davenport.GeneralFamily

/-!
# The full GGWZ Theorem 1.1: `D(C_n^r) ≥ r(n-1) + 1 + ⌊(r-1)/(5k-1)⌋`

Gao, Geroldinger, Wang and Zeng (arXiv:2611.24775 v3, Theorem 1.1) prove that for `n = 2k`,
`k ≥ 3` odd, and every positive integer `r`,
`D(C_n^r) ≥ r(n-1) + 1 + ⌊(r-1)/(5k-1)⌋`.
`Lab/Davenport/GeneralFamily.lean` formalizes the base construction (one extra term from rank
`5k` on). This file formalizes the *replacement step* that chains copies of it, and so the whole
theorem: for every `r` there is a zero-sumfree sequence of length `r(n-1) + ⌊(r-1)/(5k-1)⌋`
over `C_n^r` (`ggwz_floor`). Since `D(G) = 1 + d(G)`, this is exactly their bound.

## The replacement step (paper, end of §3)

Delete the `n - 2` copies of `F₁` from the base sequence `S` (rank `R = 5k`) and call the rest
`P`. Write the group as `K ⊕ ⟨F₁⟩` with `K ≅ C_n^{R-1}`. Every nonempty subsequence of `P` whose
`K`-part sums to zero has sum exactly `F₁` (`P_key`). Given a zero-sumfree `A` over `H` and a
term `g` of `A`, replace one `g` by the image of `P` under `w + jF₁ ↦ (w, j g)` in `K ⊕ H`: the
result is zero-sumfree (`replace`), with `R - 1` more ranks and `|P| - 1 = (R-1)(n-1) + 1` more
terms. Starting from basis sequences and replacing `j = ⌊(r-1)/(5k-1)⌋` times gives the bound.
-/

namespace OpenProblemsLab.Davenport.Floor

open Finset OpenProblemsLab.Davenport.Family

/-! ### Generic multiset facts -/

/-- A sub-multiset of an image is the image of a sub-multiset. -/
theorem le_map_preimage {α β : Type*} [DecidableEq β] (f : α → β) :
    ∀ (s : Multiset α) (T : Multiset β), T ≤ s.map f → ∃ s' ≤ s, s'.map f = T := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    intro T hT
    exact ⟨0, le_rfl, by simpa using (Multiset.le_zero.mp (by simpa using hT)).symm⟩
  | cons a s ih =>
    intro T hT
    rw [Multiset.map_cons] at hT
    by_cases h : f a ∈ T
    · have h2 : T.erase (f a) ≤ s.map f := Multiset.erase_le_iff_le_cons.mpr hT
      obtain ⟨s', hs', hm⟩ := ih _ h2
      refine ⟨a ::ₘ s', Multiset.cons_le_cons a hs', ?_⟩
      rw [Multiset.map_cons, hm, Multiset.cons_erase h]
    · obtain ⟨s', hs', hm⟩ := ih _ ((Multiset.le_cons_of_notMem h).mp hT)
      exact ⟨s', hs'.trans (Multiset.le_cons_self s a), hm⟩

/-- A sub-multiset of a sum splits as a sum of sub-multisets. -/
theorem le_add_decomp {α : Type*} [DecidableEq α] (A B T : Multiset α) (hT : T ≤ A + B) :
    ∃ U ≤ A, ∃ V ≤ B, T = U + V := by
  refine ⟨T ∩ A, Multiset.inter_le_right, T - T ∩ A, ?_, ?_⟩
  · rw [Multiset.le_iff_count] at hT ⊢
    intro x
    have := hT x
    rw [Multiset.count_add] at this
    rw [Multiset.count_sub, Multiset.count_inter]
    omega
  · exact (add_tsub_cancel_of_le Multiset.inter_le_left).symm

/-- Zero-sumfreeness is preserved by injective additive maps. -/
theorem zeroSumFree_map_inj {H K : Type*} [AddCommMonoid H] [AddCommMonoid K] [DecidableEq K]
    (φ : H →+ K) (hφ : Function.Injective φ) (T : Multiset H) (hT : ZeroSumFree T) :
    ZeroSumFree (T.map φ) := by
  intro U hU hne hsum
  obtain ⟨U', hU', rfl⟩ := le_map_preimage φ T U hU
  refine hT U' hU' (by rintro rfl; simp at hne) ?_
  apply hφ
  rw [map_zero, ← hsum, map_multiset_sum]

/-! ### The replacement lemma -/

/-- **Replacement step.** Let `P` be a sequence over `K × ZMod n` such that every nonempty
subsequence whose `K`-part sums to zero has `ZMod n`-part summing to `1`. If `A` is zero-sumfree
over a `ZMod n`-module `H` and `g ∈ A`, then replacing one copy of `g` by the image of `P` under
`(w, j) ↦ (w, j • g)` gives a zero-sumfree sequence over `K × H`. -/
theorem replace {n : ℕ} {K H : Type*} [AddCommGroup K] [AddCommGroup H] [Module (ZMod n) H]
    [DecidableEq K] [DecidableEq H]
    (P : Multiset (K × ZMod n))
    (hP : ∀ Q ≤ P, Q ≠ 0 → Q.sum.1 = 0 → Q.sum.2 = 1)
    (A : Multiset H) (hA : ZeroSumFree A) (g : H) (hg : g ∈ A) :
    ZeroSumFree ((A.erase g).map (fun a => ((0 : K), a)) + P.map (fun p => (p.1, p.2 • g))) := by
  intro U hU hne hsum
  obtain ⟨U1, hU1, U2, hU2, rfl⟩ := le_add_decomp _ _ _ hU
  obtain ⟨V1, hV1, rfl⟩ := le_map_preimage _ _ _ hU1
  obtain ⟨V2, hV2, rfl⟩ := le_map_preimage _ _ _ hU2
  have s1 : ∀ V : Multiset H, (V.map (fun a => ((0 : K), a))).sum = (0, V.sum) := by
    intro V
    induction V using Multiset.induction_on with
    | empty => simp [Prod.zero_eq_mk]
    | cons a V ih => simp [ih]
  have s2 : ∀ V : Multiset (K × ZMod n), (V.map (fun p => (p.1, p.2 • g))).sum =
      (V.sum.1, V.sum.2 • g) := by
    intro V
    induction V using Multiset.induction_on with
    | empty => simp [Prod.zero_eq_mk]
    | cons a V ih => simp [ih, add_smul]
  rw [Multiset.sum_add, s1, s2] at hsum
  have h1 : V2.sum.1 = 0 := by simpa using congrArg Prod.fst hsum
  have h2 : V1.sum + V2.sum.2 • g = 0 := by simpa using congrArg Prod.snd hsum
  have hV1A : V1 ≤ A := hV1.trans (Multiset.erase_le g A)
  by_cases hV20 : V2 = 0
  · subst hV20
    refine hA V1 hV1A (by rintro rfl; simp at hne) ?_
    simpa using h2
  · rw [hP V2 hV2 hV20 h1, one_smul] at h2
    refine hA (g ::ₘ V1) ?_ (Multiset.cons_ne_zero) ?_
    · rw [← Multiset.cons_erase hg]; exact Multiset.cons_le_cons g hV1
    · rw [Multiset.sum_cons, add_comm]; exact h2

theorem card_replace {n : ℕ} {K H : Type*} [AddCommGroup K] [AddCommGroup H] [Module (ZMod n) H]
    [DecidableEq H] (P : Multiset (K × ZMod n)) (A : Multiset H) (g : H) (hg : g ∈ A) :
    ((A.erase g).map (fun a => ((0 : K), a)) + P.map (fun p => (p.1, p.2 • g))).card =
      A.card - 1 + P.card := by
  simp [Multiset.card_erase_of_mem hg]

/-! ### Basis sequences -/

/-- `n - 1` copies of each basis vector of `C_n^m`. -/
theorem basis_seq (n m : ℕ) [NeZero n] :
    ∃ T : Multiset (Fin m → ZMod n), T.card = m * (n - 1) ∧ ZeroSumFree T := by
  refine ⟨∑ i : Fin m, Multiset.replicate (n - 1) (Pi.single i 1), by simp, ?_⟩
  refine zeroSumFree_of_core (fun i : Fin m => (Pi.single i 1 : Fin m → ZMod n))
    (fun _ => n - 1) ?_
  intro c hc h i
  have hi := congrFun h i
  simp [Finset.sum_apply, Pi.single_apply] at hi
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hi
  have := hc i
  have hn := NeZero.pos n
  obtain ⟨q, hq⟩ := hd
  rcases q with _ | q
  · simpa using hq
  · exfalso; have : n ≤ c i := by rw [hq]; exact Nat.le_mul_of_pos_right _ (by omega)
    omega

/-! ### The sequence `P` and its key property -/

variable {t : ℕ}

/-- The coordinate of `F₁` (Lean index `0` of the `F`-coordinates). -/
def F0 (ht : 1 ≤ t) : Idx t 0 := .inr (.inl ⟨0, by omega⟩)

/-- The kind of the element `F₁`. -/
def kF0 (ht : 1 ≤ t) : Kind t 0 := .inr (.inl ⟨0, by omega⟩)

theorem v_kF0 (ht : 1 ≤ t) (x : Idx t 0) :
    Family.v t 0 (kF0 ht) x = if x = F0 ht then 1 else 0 := by
  rcases x with ⟨i, j⟩ | i | ⟨⟩ | i
  · simp [Family.v, vZ, kF0, F0]
  · by_cases h : (⟨0, by omega⟩ : Fin (2 * t)) = i
    · subst h; simp [Family.v, vZ, kF0, F0]
    · simp [Family.v, vZ, kF0, F0, h, Ne.symm h]
  · simp [Family.v, vZ, kF0, F0]
  · exact i.elim0

theorem mult_kF0 (ht : 1 ≤ t) : Family.mult t 0 (kF0 ht) = 4 * t := rfl

/-- The `n - 2` copies of `F₁`. -/
abbrev RF (ht : 1 ≤ t) : Multiset (Grp t 0) := Multiset.replicate (4 * t) (Family.v t 0 (kF0 ht))

theorem RF_le (ht : 1 ≤ t) : RF ht ≤ Family.S t 0 := by
  unfold RF Family.S
  rw [← mult_kF0 ht]
  exact Finset.single_le_sum (f := fun k => Multiset.replicate (Family.mult t 0 k) (Family.v t 0 k))
    (fun _ _ => Multiset.zero_le _) (Finset.mem_univ _)

/-- `P`: the base sequence with the `n - 2` copies of `F₁` deleted. -/
abbrev P0 (ht : 1 ≤ t) : Multiset (Grp t 0) := Family.S t 0 - RF ht

theorem card_P0 (ht : 1 ≤ t) : (P0 ht).card = (10 * t + 4) * (4 * t + 1) + 2 := by
  rw [Multiset.card_sub (RF_le ht), Family.card_S ht, Multiset.card_replicate]
  have : (10 * t + 5 + 0) * (4 * t + 1) + 1 = (10 * t + 4) * (4 * t + 1) + 2 + 4 * t := by ring
  omega

/-- **Key property of `P`.** A nonempty subsequence of `P` vanishing off `F₁` sums to `F₁`. -/
theorem P_key (ht : 1 ≤ t) (Q : Multiset (Grp t 0)) (hQ : Q ≤ P0 ht) (hne : Q ≠ 0)
    (hoff : ∀ x, x ≠ F0 ht → Q.sum x = 0) : Q.sum (F0 ht) = 1 := by
  have hS := Family.zeroSumFree_S (b := 0) ht
  have hQS : Q ≤ Family.S t 0 := hQ.trans (Multiset.sub_le_self _ _)
  set j := Q.sum (F0 ht) with hj
  have hn : 1 < 4 * t + 2 := by omega
  have hjlt : j.val < 4 * t + 2 := ZMod.val_lt j
  -- `j ≠ 0`
  have hj0 : j.val ≠ 0 := by
    intro h0
    rw [ZMod.val_eq_zero] at h0
    refine hS Q hQS hne ?_
    funext x
    by_cases hx : x = F0 ht
    · subst hx; rw [← hj, h0]; rfl
    · exact hoff x hx
  -- `j` is not `2, …, n-1`
  have hj1 : j.val = 1 := by
    by_contra h1
    have hc : 4 * t + 2 - j.val ≤ 4 * t := by omega
    refine hS (Q + Multiset.replicate (4 * t + 2 - j.val) (Family.v t 0 (kF0 ht))) ?_ (by simp [hne]) ?_
    · calc Q + Multiset.replicate (4 * t + 2 - j.val) (Family.v t 0 (kF0 ht))
          ≤ P0 ht + RF ht := add_le_add hQ (Multiset.replicate_le_replicate _ |>.mpr hc)
        _ = Family.S t 0 := tsub_add_cancel_of_le (RF_le ht)
    · rw [Multiset.sum_add, Multiset.sum_replicate]
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, v_kF0, Pi.zero_apply]
      by_cases hx : x = F0 ht
      · subst hx
        simp only [if_true, nsmul_eq_mul, mul_one]
        rw [← hj, Nat.cast_sub hjlt.le, ZMod.natCast_val, ZMod.cast_id', id]
        push_cast
        have h0 : ((4 * t + 2 : ℕ) : ZMod (4 * t + 2)) = 0 := ZMod.natCast_self _
        push_cast at h0
        linear_combination h0
      · simp [hx, hoff x hx]
  exact (ZMod.val_eq_one hn j).mp hj1

/-! ### Splitting off the `F₁` coordinate -/

theorem card_ne_F0 (ht : 1 ≤ t) : Fintype.card {x : Idx t 0 // x ≠ F0 ht} = 10 * t + 4 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, card_Idx]
  omega

/-- The remaining coordinates, numbered. -/
noncomputable def ι (ht : 1 ≤ t) : Fin (10 * t + 4) ≃ {x : Idx t 0 // x ≠ F0 ht} :=
  (Fintype.equivFinOfCardEq (card_ne_F0 ht)).symm

/-- `w ↦ (K-part, F₁-coefficient)`. -/
noncomputable def split (ht : 1 ≤ t) :
    Grp t 0 →+ (Fin (10 * t + 4) → ZMod (4 * t + 2)) × ZMod (4 * t + 2) where
  toFun w := (fun i => w (ι ht i), w (F0 ht))
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `P`, split as a sequence over `C_n^{R-1} × C_n`. -/
noncomputable def Psplit (ht : 1 ≤ t) :
    Multiset ((Fin (10 * t + 4) → ZMod (4 * t + 2)) × ZMod (4 * t + 2)) :=
  (P0 ht).map (split ht)

theorem card_Psplit (ht : 1 ≤ t) : (Psplit ht).card = (10 * t + 4) * (4 * t + 1) + 2 := by
  rw [Psplit, Multiset.card_map, card_P0]

theorem Psplit_key (ht : 1 ≤ t) :
    ∀ Q ≤ Psplit ht, Q ≠ 0 → Q.sum.1 = 0 → Q.sum.2 = 1 := by
  intro Q hQ hne h1
  obtain ⟨Q0, hQ0, rfl⟩ := le_map_preimage _ _ _ hQ
  rw [← map_multiset_sum] at h1 ⊢
  refine P_key ht Q0 hQ0 (by rintro rfl; simp at hne) ?_
  intro x hx
  have := congrFun h1 ((ι ht).symm ⟨x, hx⟩)
  simpa [split] using this

/-! ### Gluing `K × H` back into `C_n^{N+M}` -/

/-- `(k, h) ↦ (k, h)` as a function on `Fin (N + M)`. -/
def glue (n N M : ℕ) : (Fin N → ZMod n) × (Fin M → ZMod n) →+ (Fin (N + M) → ZMod n) where
  toFun p := fun i => Fin.addCases p.1 p.2 i
  map_zero' := by funext i; refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp
  map_add' _ _ := by funext i; refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp

theorem glue_injective (n N M : ℕ) : Function.Injective (glue n N M) := by
  intro p q h
  have h' := congrFun h
  ext i
  · simpa [glue] using h' (Fin.castAdd M i)
  · simpa [glue] using h' (Fin.natAdd N i)

/-! ### Iterating the replacement -/

theorem iterate (ht : 1 ≤ t) (j : ℕ) :
    ∀ m, 1 ≤ m → ∀ r, r = m + j * (10 * t + 4) →
      ∃ T : Multiset (Fin r → ZMod (4 * t + 2)),
        T.card = r * (4 * t + 1) + j ∧ ZeroSumFree T := by
  induction j with
  | zero =>
    intro m _ r hr
    obtain ⟨T, hT, hz⟩ := basis_seq (4 * t + 2) r
    exact ⟨T, by rw [hT]; simp, hz⟩
  | succ j ih =>
    intro m hm r hr
    obtain ⟨A, hAc, hA⟩ := ih m hm (m + j * (10 * t + 4)) rfl
    have hM : 1 ≤ (m + j * (10 * t + 4)) * (4 * t + 1) + j := by
      have : m ≤ (m + j * (10 * t + 4)) * (4 * t + 1) :=
        le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_right _ (by omega))
      omega
    obtain ⟨g, hg⟩ : ∃ g, g ∈ A := Multiset.card_pos_iff_exists_mem.mp (by omega)
    have hz := replace (Psplit ht) (Psplit_key ht) A hA g hg
    have hc := card_replace (Psplit ht) A g hg
    have hr' : r = 10 * t + 4 + (m + j * (10 * t + 4)) := by rw [hr]; ring
    subst hr'
    refine ⟨_, ?_, zeroSumFree_map_inj _ (glue_injective _ _ _) _ hz⟩
    rw [Multiset.card_map, hc, hAc, card_Psplit]
    zify [hM]
    ring

/-- **Theorem 1.1 of GGWZ, in full, in Lean.** Let `n ≡ 2 (mod 4)`, `n ≥ 6`, so `n = 2k` with
`k ≥ 3` odd. For every `r` there is a zero-sumfree sequence over `C_n^r` of length
`r(n-1) + ⌊(r-1)/(5k-1)⌋`. Equivalently `D(C_n^r) ≥ r(n-1) + 1 + ⌊(r-1)/(5k-1)⌋`. -/
theorem ggwz_floor (n r : ℕ) (hn : n % 4 = 2) (h6 : 6 ≤ n) :
    ∃ T : Multiset (Fin r → ZMod n),
      T.card = r * (n - 1) + (r - 1) / (5 * (n / 2) - 1) ∧ ZeroSumFree T := by
  obtain ⟨t, rfl⟩ : ∃ t, n = 4 * t + 2 := ⟨n / 4, by omega⟩
  have ht : 1 ≤ t := by omega
  have hk : 5 * ((4 * t + 2) / 2) - 1 = 10 * t + 4 := by omega
  rw [hk, show 4 * t + 2 - 1 = 4 * t + 1 by omega]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨0, by simp, fun U hU hne _ => hne (Multiset.le_zero.mp hU)⟩
  set j := (r - 1) / (10 * t + 4)
  have hj : j * (10 * t + 4) ≤ r - 1 := Nat.div_mul_le_self _ _
  exact iterate ht j (r - j * (10 * t + 4)) (by omega) r (by omega)

/-- The same bound, stated as "no nonempty sub-multiset sums to zero" with the length as a lower
bound. For `r ≥ 5k` the extra term is at least `1` (this recovers `Family.vEBK_fails`), and it
grows by one every `5k - 1` ranks: for `r ≥ 10k - 1` the sequence beats `r(n-1)` by at least 2. -/
theorem ggwz_floor' (n r : ℕ) (hn : n % 4 = 2) (h6 : 6 ≤ n) :
    ∃ T : Multiset (Fin r → ZMod n), r * (n - 1) + (r - 1) / (5 * (n / 2) - 1) ≤ T.card ∧
      ∀ U ≤ T, U ≠ 0 → U.sum ≠ 0 := by
  obtain ⟨T, hc, hT⟩ := ggwz_floor n r hn h6
  exact ⟨T, hc.ge, hT⟩

end OpenProblemsLab.Davenport.Floor
