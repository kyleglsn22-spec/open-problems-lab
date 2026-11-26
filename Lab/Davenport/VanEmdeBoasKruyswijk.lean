import Mathlib

/-!
# The van Emde Boas–Kruyswijk conjecture fails for `C_6^15`

The Davenport constant `D(G)` of a finite abelian group `G` is the least `ℓ` such that every
sequence of `ℓ` elements of `G` has a nonempty subsequence summing to `0`. In 1969 van Emde Boas
and Kruyswijk conjectured `D(C_n^r) = r(n-1) + 1` for all `n, r ≥ 1`.

Gao, Geroldinger, Wang and Zeng (arXiv:2611.24775, v3, 24 Nov 2026, Theorem 1.1 and its proof)
build, for `n = 2k` with `k ≥ 3` odd, a zero-sumfree sequence of length `5k(n-1) + 1` over
`C_n^{5k}`. We formalize their construction for `k = 3`: a sequence of `76` elements of
`(ZMod 6)^15` with no nonempty zero-sum subsequence. Since `15 · (6 - 1) + 1 = 76`, this sequence
has the length at which the conjecture predicts a zero-sum subsequence, so the conjecture is false.

Sequences are `Multiset`s and subsequences are sub-multisets.

## Layout of the sequence (coordinates `0..14`)

* Blocks `P_i` (`i = 0,1,2`) use coordinates `4i, 4i+1, 4i+2, 4i+3` (basis `e₁, e₂, e₃, f`).
  Each carries the sequence `W = z · f³ · ∏_j e_j² (e_j + f)³` with `z = e₁ + e₂ + e₃ + 4f`.
* Coordinates `12, 13` carry `F₀, F₁`, four copies each; coordinate `14` is `u`.
* The center is `u + 5f₀ + 5f₁ + 5f₂ + 5F₀ + 5F₁`, and the leaves are
  `u + aᵢ + 3Fᵢ`, `u + dᵢ + 3Fᵢ`, `(u + 2Fᵢ)²` for `i = 0, 1` and `u + a₂`, `u + d₂`,
  where `aᵢ = -e₁ + e₂ + 5f` and `dᵢ = -e₂ + e₃ + 5f` in block `i`.

The 35 distinct elements are the rows of `M` (entries are residues mod 6) and `mult` gives their
multiplicities. Rows `8i .. 8i+7` are `z, f, e₁, e₁+f, e₂, e₂+f, e₃, e₃+f` of block `i`;
row 24, 25 are `F₀, F₁`; row 26 is the center; rows 27–34 are the leaves.

## Proof

Following the paper: a zero-sum subsequence restricted to block `i` forces the number of chosen
elements among {center, `aᵢ`-leaf, `dᵢ`-leaf} to be `0`, `1` or `3` (`block`), the `F`- and
`u`-coordinates then force no leaf and no center (`leaves`), and then each block and each `Fᵢ`
contributes nothing. All case analysis is done by `interval_cases` and `omega`.
-/

namespace OpenProblemsLab.Davenport

open Finset

def M : Fin 35 → Fin 15 → ℕ := ![
    ![1, 1, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 1, 4, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 4, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 5, 0, 0, 0, 5, 0, 0, 0, 5, 5, 5, 1],
    ![5, 1, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1],
    ![0, 5, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1],
    ![0, 0, 0, 0, 5, 1, 0, 5, 0, 0, 0, 0, 0, 3, 1],
    ![0, 0, 0, 0, 0, 5, 1, 5, 0, 0, 0, 0, 0, 3, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 5, 1, 0, 5, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 1, 5, 0, 0, 1]]

def mult : Fin 35 → ℕ := ![1, 3, 2, 3, 2, 3, 2, 3, 1, 3, 2, 3, 2, 3, 2, 3, 1, 3, 2, 3, 2, 3, 2, 3, 4, 4, 1, 1, 1, 2, 1, 1, 2, 1, 1]

/-- The group `C_6^15`. -/
abbrev G := Fin 15 → ZMod 6

/-- The 35 distinct elements of the sequence. -/
def v (i : Fin 35) : G := fun j => (M i j : ZMod 6)

/-- The GGWZ sequence for `n = 6`: element `v i` with multiplicity `mult i`. -/
def S : Multiset G := ∑ i, Multiset.replicate (mult i) (v i)

/-- A sequence is zero-sumfree if no nonempty subsequence sums to zero. -/
def ZeroSumFree {H : Type*} [AddCommMonoid H] (T : Multiset H) : Prop :=
  ∀ U ≤ T, U ≠ 0 → U.sum ≠ 0

/-! ### The arithmetic core -/

/-- One block (`W` together with the center and the two leaves touching it).
Counts: `z ≤ 1`, `f ≤ 3`, `eⱼ ≤ 2`, `gⱼ = #(eⱼ+f) ≤ 3`; `x, α, δ ≤ 1` are the center and the
two leaves. -/
theorem block (z f e1 e2 e3 g1 g2 g3 x α δ : ℕ)
    (hz : z ≤ 1) (hf : f ≤ 3) (he1 : e1 ≤ 2) (he2 : e2 ≤ 2) (he3 : e3 ≤ 2)
    (hg1 : g1 ≤ 3) (hg2 : g2 ≤ 3) (hg3 : g3 ≤ 3) (hx : x ≤ 1) (hα : α ≤ 1) (hδ : δ ≤ 1)
    (h1 : (z + e1 + g1 + 5 * α) % 6 = 0)
    (h2 : (z + e2 + g2 + α + 5 * δ) % 6 = 0)
    (h3 : (z + e3 + g3 + δ) % 6 = 0)
    (h4 : (4 * z + f + g1 + g2 + g3 + 5 * x + 5 * α + 5 * δ) % 6 = 0) :
    x + α + δ ≠ 2 ∧ (x + α + δ = 0 → z = 0 ∧ f = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ e3 = 0 ∧
      g1 = 0 ∧ g2 = 0 ∧ g3 = 0) := by
  interval_cases x <;> interval_cases α <;> interval_cases δ <;> interval_cases z <;> omega

/-- The center, the leaves and the `Fᵢ`: `x` center, `αᵢ, δᵢ` the `a`- and `d`-leaves,
`Aᵢ ≤ 2` copies of `u + 2Fᵢ`, `Fᵢ ≤ 4` copies of `Fᵢ`. -/
theorem leaves (x α0 δ0 A0 α1 δ1 A1 α2 δ2 F0 F1 : ℕ)
    (hx : x ≤ 1) (hα0 : α0 ≤ 1) (hδ0 : δ0 ≤ 1) (hA0 : A0 ≤ 2)
    (hα1 : α1 ≤ 1) (hδ1 : δ1 ≤ 1) (hA1 : A1 ≤ 2) (hα2 : α2 ≤ 1) (hδ2 : δ2 ≤ 1)
    (hF0 : F0 ≤ 4) (hF1 : F1 ≤ 4)
    (b0 : x + α0 + δ0 ≠ 2) (b1 : x + α1 + δ1 ≠ 2) (b2 : x + α2 + δ2 ≠ 2)
    (h12 : (F0 + 5 * x + 3 * α0 + 3 * δ0 + 2 * A0) % 6 = 0)
    (h13 : (F1 + 5 * x + 3 * α1 + 3 * δ1 + 2 * A1) % 6 = 0)
    (h14 : (x + α0 + δ0 + A0 + α1 + δ1 + A1 + α2 + δ2) % 6 = 0) :
    x = 0 ∧ α0 = 0 ∧ δ0 = 0 ∧ A0 = 0 ∧ α1 = 0 ∧ δ1 = 0 ∧ A1 = 0 ∧ α2 = 0 ∧ δ2 = 0 ∧
      F0 = 0 ∧ F1 = 0 := by
  interval_cases x <;> interval_cases α0 <;> interval_cases δ0 <;> interval_cases α1 <;>
    interval_cases δ1 <;> interval_cases α2 <;> interval_cases δ2 <;> omega

set_option maxHeartbeats 4000000 in
/-- The core statement in coordinates: bounded counts whose weighted row sum vanishes mod 6 in
every coordinate are all zero. -/
theorem core (c : Fin 35 → ℕ) (hc : ∀ i, c i ≤ mult i)
    (h : ∀ j, (∑ i, c i * M i j) % 6 = 0) : ∀ i, c i = 0 := by
  have e : ∀ j : Fin 15, (∑ i, c i * M i j) % 6 = 0 := h
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4
  have e5 := e 5; have e6 := e 6; have e7 := e 7; have e8 := e 8; have e9 := e 9
  have e10 := e 10; have e11 := e 11; have e12 := e 12; have e13 := e 13; have e14 := e 14
  simp [Fin.sum_univ_succ, M] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
  have hb : ∀ i, c i ≤ mult i := hc
  have k0 := hb 0; have k1 := hb 1; have k2 := hb 2; have k3 := hb 3; have k4 := hb 4
  have k5 := hb 5; have k6 := hb 6; have k7 := hb 7; have k8 := hb 8; have k9 := hb 9
  have k10 := hb 10; have k11 := hb 11; have k12 := hb 12; have k13 := hb 13
  have k14 := hb 14; have k15 := hb 15; have k16 := hb 16; have k17 := hb 17
  have k18 := hb 18; have k19 := hb 19; have k20 := hb 20; have k21 := hb 21
  have k22 := hb 22; have k23 := hb 23; have k24 := hb 24; have k25 := hb 25
  have k26 := hb 26; have k27 := hb 27; have k28 := hb 28; have k29 := hb 29
  have k30 := hb 30; have k31 := hb 31; have k32 := hb 32; have k33 := hb 33
  have k34 := hb 34
  simp [mult] at k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15 k16 k17
  simp [mult] at k18 k19 k20 k21 k22 k23 k24 k25 k26 k27 k28 k29 k30 k31 k32 k33 k34
  -- block i: rows 8i + (0: z, 1: f, 2: e₁, 3: e₁+f, 4: e₂, 5: e₂+f, 6: e₃, 7: e₃+f)
  have B0 := block (c 0) (c 1) (c 2) (c 4) (c 6) (c 3) (c 5) (c 7) (c 26) (c 27) (c 28)
    k0 k1 k2 k4 k6 k3 k5 k7 k26 k27 k28 (by omega) (by omega) (by omega) (by omega)
  have B1 := block (c 8) (c 9) (c 10) (c 12) (c 14) (c 11) (c 13) (c 15) (c 26) (c 30) (c 31)
    k8 k9 k10 k12 k14 k11 k13 k15 k26 k30 k31 (by omega) (by omega) (by omega) (by omega)
  have B2 := block (c 16) (c 17) (c 18) (c 20) (c 22) (c 19) (c 21) (c 23) (c 26) (c 33) (c 34)
    k16 k17 k18 k20 k22 k19 k21 k23 k26 k33 k34 (by omega) (by omega) (by omega) (by omega)
  have L := leaves (c 26) (c 27) (c 28) (c 29) (c 30) (c 31) (c 32) (c 33) (c 34) (c 24) (c 25)
    k26 k27 k28 k29 k30 k31 k32 k33 k34 k24 k25 B0.1 B1.1 B2.1 (by omega) (by omega) (by omega)
  obtain ⟨l26, l27, l28, l29, l30, l31, l32, l33, l34, l24, l25⟩ := L
  have Z0 := B0.2 (by omega)
  have Z1 := B1.2 (by omega)
  have Z2 := B2.2 (by omega)
  intro i
  fin_cases i <;> simp <;> omega

/-! ### From multisets to counts -/

theorem M_lt : ∀ i j, M i j < 6 := by decide

theorem M_injective : ∀ a b : Fin 35, (∀ j, M a j = M b j) → a = b := by decide

theorem v_injective : Function.Injective v := by
  intro a b hab
  apply M_injective
  intro j
  have h := congrArg ZMod.val (congrFun hab j)
  simp only [v, ZMod.val_natCast] at h
  rwa [Nat.mod_eq_of_lt (M_lt a j), Nat.mod_eq_of_lt (M_lt b j)] at h

theorem count_S (i : Fin 35) : S.count (v i) = mult i := by
  classical
  simp only [S, Multiset.count_sum', Multiset.count_replicate]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [v_injective.ne hb]
  · simp

theorem count_S_of_not_mem (g : G) (hg : ∀ i, v i ≠ g) : S.count g = 0 := by
  classical
  simp [S, Multiset.count_sum', Multiset.count_replicate, hg]

theorem card_S : S.card = 76 := by
  simp [S, Fin.sum_univ_succ, mult]

/-- The GGWZ sequence over `C_6^15` is zero-sumfree. -/
theorem zeroSumFree_S : ZeroSumFree S := by
  classical
  intro T hT hne hsum
  set c : Fin 35 → ℕ := fun i => T.count (v i) with hc
  have hcle : ∀ i, c i ≤ mult i := fun i => by
    rw [← count_S i]; exact Multiset.le_iff_count.mp hT _
  have hTeq : T = ∑ i, Multiset.replicate (c i) (v i) := by
    ext g
    simp only [Multiset.count_sum', Multiset.count_replicate]
    by_cases hg : ∃ i, v i = g
    · obtain ⟨i, rfl⟩ := hg
      rw [Finset.sum_eq_single i]
      · simp [hc]
      · intro b _ hb
        simp [v_injective.ne hb]
      · simp
    · simp only [not_exists] at hg
      have h0 : T.count g = 0 :=
        Nat.eq_zero_of_le_zero ((Multiset.le_iff_count.mp hT g).trans
          (count_S_of_not_mem g hg).le)
      rw [h0]
      symm
      apply Finset.sum_eq_zero
      intro i _
      simp [hg i]
  have hsum' : ∑ i, c i • v i = 0 := by
    rw [hTeq, Multiset.sum_sum] at hsum
    simpa [Multiset.sum_replicate] using hsum
  have hcoord : ∀ j, (∑ i, c i * M i j) % 6 = 0 := by
    intro j
    have := congrFun hsum' j
    simp only [Finset.sum_apply, nsmul_eq_mul] at this
    have h' : ((∑ i, c i * M i j : ℕ) : ZMod 6) = 0 := by
      push_cast; exact this
    exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp h')
  have hz := core c hcle hcoord
  apply hne
  rw [hTeq]
  simp [hz]

/-! ### Main results -/

/-- There is a zero-sumfree sequence of length `76 = 15 · (6 - 1) + 1` over `C_6^15`, so
`D(C_6^15) ≥ 77 > 15 · (6 - 1) + 1`. -/
theorem exists_zeroSumFree_C6_15 :
    ∃ T : Multiset (Fin 15 → ZMod 6), T.card = 15 * (6 - 1) + 1 ∧ ZeroSumFree T :=
  ⟨S, card_S, zeroSumFree_S⟩

/-- The van Emde Boas–Kruyswijk conjecture (1969), in the direction `D(C_n^r) ≤ r(n-1) + 1`:
every sequence of `r(n-1) + 1` elements of `C_n^r` has a nonempty zero-sum subsequence.
(The other direction `D(C_n^r) ≥ r(n-1) + 1` is classical.) -/
def VanEmdeBoasKruyswijk : Prop :=
  ∀ n r : ℕ, 0 < n → ∀ T : Multiset (Fin r → ZMod n), r * (n - 1) + 1 ≤ T.card →
    ∃ U ≤ T, U ≠ 0 ∧ U.sum = 0

/-- **The van Emde Boas–Kruyswijk conjecture is false** (counterexample `n = 6`, `r = 15`,
following Gao–Geroldinger–Wang–Zeng). -/
theorem not_vanEmdeBoasKruyswijk : ¬ VanEmdeBoasKruyswijk := by
  intro h
  obtain ⟨U, hU, hne, hsum⟩ := h 6 15 (by norm_num) S (by rw [card_S])
  exact zeroSumFree_S U hU hne hsum

end OpenProblemsLab.Davenport
