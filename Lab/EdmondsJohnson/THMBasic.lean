import Lab.EdmondsJohnson.Basic

/-!
# Total half-modularity: definition and a certificate checker

An integral matrix is *totally half-modular* (THM) if `S⁻¹` is half-integral for every nonsingular
square submatrix `S`. For a matrix with 5 rows, `isTHM_of_certs` reduces this to one certificate
for each square submatrix with increasing row and column indices (one table `T k` per size
`k`): either
an integral matrix `N` with `S N = 2I` (then `S⁻¹ = N / 2`), or a nonzero integral vector `v` with
`S v = 0` (then `S` is singular). Any other square submatrix is one of these with its rows and
columns permuted, and permuting rows and columns only permutes the entries of the inverse.
-/

namespace EdmondsJohnson

open Matrix

/-- `A` is totally half-modular: for every square submatrix `S` (rows `r`, columns `c`, both
injective) with `det S ≠ 0`, every entry of `2 S⁻¹` is an integer. -/
def IsTHM {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∀ (k : ℕ) (r : Fin k → Fin m) (c : Fin k → Fin n), Function.Injective r →
    Function.Injective c → ((A.map (Int.cast : ℤ → ℚ)).submatrix r c).det ≠ 0 →
    ∀ i j, ∃ t : ℤ, 2 * ((A.map (Int.cast : ℤ → ℚ)).submatrix r c)⁻¹ i j = t

/-- The function `Fin k → Fin m` listed by `l`. -/
def ofList {m : ℕ} [NeZero m] (l : List (Fin m)) (k : ℕ) : Fin k → Fin m :=
  fun i => l.getD i 0

/-- A `k × k` integer matrix from a list of rows. -/
def toMat (k : ℕ) (L : List (List ℤ)) : Matrix (Fin k) (Fin k) ℤ :=
  fun i j => (L.getD i []).getD j 0

/-- A vector from a list. -/
def toVec (k : ℕ) (L : List ℤ) : Fin k → ℤ := fun i => L.getD i 0

/-- A certificate table, keyed by the (increasing) row and column index lists. -/
abbrev CertTable := List ((List ℕ × List ℕ) × (List (List ℤ) ⊕ List ℤ))

variable {n : ℕ} [NeZero n]

/-- The certificate in `T` for the submatrix of `A` with rows `lr` and columns `lc` is correct. -/
def certOK (A : Matrix (Fin 5) (Fin n) ℤ) (T : CertTable) (k : ℕ) (lr : List (Fin 5))
    (lc : List (Fin n)) : Prop :=
  match T.lookup (lr.map Fin.val, lc.map Fin.val) with
  | some (Sum.inl N) => ∀ i j, (A.submatrix (ofList lr k) (ofList lc k) * toMat k N) i j =
      if i = j then 2 else 0
  | some (Sum.inr v) => toVec k v ≠ 0 ∧ A.submatrix (ofList lr k) (ofList lc k) *ᵥ toVec k v = 0
  | none => False

instance (A : Matrix (Fin 5) (Fin n) ℤ) (T : CertTable) (k : ℕ) (lr : List (Fin 5))
    (lc : List (Fin n)) : Decidable (certOK A T k lr lc) := by
  unfold certOK; split <;> infer_instance

omit [NeZero n] in
lemma map_submatrix_cast (A : Matrix (Fin 5) (Fin n) ℤ) {k : ℕ} (r : Fin k → Fin 5)
    (c : Fin k → Fin n) :
    (A.submatrix r c).map (Int.cast : ℤ → ℚ) = (A.map (Int.cast : ℤ → ℚ)).submatrix r c := by
  ext i j; simp

/-- A correct certificate gives a half-integral inverse. -/
lemma half_integral_of_certOK {A : Matrix (Fin 5) (Fin n) ℤ} {T : CertTable} {k : ℕ}
    {lr : List (Fin 5)} {lc : List (Fin n)} (h : certOK A T k lr lc) (i j : Fin k) :
    ∃ t : ℤ, 2 * ((A.map (Int.cast : ℤ → ℚ)).submatrix (ofList lr k) (ofList lc k))⁻¹ i j = t := by
  set S := A.submatrix (ofList lr k) (ofList lc k) with hSdef
  rw [← map_submatrix_cast A, ← hSdef]
  unfold certOK at h
  split at h
  · rename_i N _
    have hmul : S * toMat k N = Matrix.of (fun a b => if a = b then (2 : ℤ) else 0) := by
      ext a b; rw [h a b]; simp
    have hq : S.map (Int.cast : ℤ → ℚ) * ((1/2 : ℚ) • (toMat k N).map (Int.cast : ℤ → ℚ)) = 1 := by
      have hcast : S.map (Int.cast : ℤ → ℚ) * (toMat k N).map Int.cast =
          (S * toMat k N).map Int.cast := by
        ext a b; simp [Matrix.mul_apply]
      rw [Matrix.mul_smul, hcast, hmul]
      ext a b; simp [Matrix.one_apply]
    refine ⟨toMat k N i j, ?_⟩
    rw [Matrix.inv_eq_right_inv hq]; simp
  · rename_i v _
    obtain ⟨hv0, hv⟩ := h
    have hdet : (S.map (Int.cast : ℤ → ℚ)).det = 0 := by
      apply Matrix.exists_mulVec_eq_zero_iff.mp
      refine ⟨fun a => (toVec k v a : ℚ), ?_, ?_⟩
      · intro h0; apply hv0; funext a; have := congrFun h0 a; simpa using this
      · funext a
        have := congrFun hv a
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at this ⊢
        exact_mod_cast this
    refine ⟨0, ?_⟩
    rw [Matrix.nonsing_inv_apply_not_isUnit _ (by simp [hdet])]; simp
  · exact h.elim

omit [NeZero n] in
/-- A strictly increasing `r : Fin k → Fin m` is listed by an increasing sublist of `[0, …, m-1]`. -/
lemma exists_list_of_strictMono {m k : ℕ} [NeZero m] (r : Fin k → Fin m) (hr : StrictMono r) :
    ∃ l ∈ (List.finRange m).sublistsLen k, r = ofList l k := by
  refine ⟨List.ofFn r, ?_, ?_⟩
  · rw [List.mem_sublistsLen]
    refine ⟨?_, List.length_ofFn⟩
    have hs : (List.ofFn r).SortedLT := List.sortedLT_ofFn_iff.mpr hr
    exact List.sublist_of_subperm_of_sortedLE
      (List.Nodup.subperm hs.nodup (fun x _ => List.mem_finRange x)) hs.sortedLE
      (List.sortedLT_finRange m).sortedLE
  · funext i
    simp [ofList, List.getD_eq_getElem?_getD]

/-- A 5-row matrix with a correct certificate for every increasing square submatrix is THM. -/
theorem isTHM_of_certs (A : Matrix (Fin 5) (Fin n) ℤ) (T : ℕ → CertTable)
    (hT : ∀ k, 1 ≤ k → k ≤ 5 → ∀ lr ∈ (List.finRange 5).sublistsLen k,
      ∀ lc ∈ (List.finRange n).sublistsLen k, certOK A (T k) k lr lc) : IsTHM A := by
  intro k r c hr hc _ i j
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact i.elim0
  have hk5 : k ≤ 5 := by simpa using Fintype.card_le_of_injective r hr
  set σ := Tuple.sort r
  set τ := Tuple.sort c
  have hr' : StrictMono (r ∘ σ) :=
    (Tuple.monotone_sort r).strictMono_of_injective (hr.comp σ.injective)
  have hc' : StrictMono (c ∘ τ) :=
    (Tuple.monotone_sort c).strictMono_of_injective (hc.comp τ.injective)
  have hsub : (A.map (Int.cast : ℤ → ℚ)).submatrix r c =
      ((A.map (Int.cast : ℤ → ℚ)).submatrix (r ∘ σ) (c ∘ τ)).submatrix σ.symm τ.symm := by
    ext a b; simp
  rw [hsub, Matrix.inv_submatrix_equiv]
  obtain ⟨lr, hlr, hreq⟩ := exists_list_of_strictMono _ hr'
  obtain ⟨lc, hlc, hceq⟩ := exists_list_of_strictMono _ hc'
  rw [hreq, hceq]
  exact half_integral_of_certOK (hT k hk1 hk5 lr hlr lc hlc) _ _

end EdmondsJohnson
