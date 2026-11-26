import Lab.Erdos757.LowerBound
import Lab.HenningYeo.Theorem6

/-!
# Erdős #757: reducing the `9/17` hypothesis to Henning–Yeo Theorem 6

`LowerBound.lean` proves `9/17 ≤ sSup` assuming `HenningYeoBound` (Henning–Yeo Theorem 7).
Here we show `HenningYeoBound` follows from Henning–Yeo Theorem 6 (`Theorem6Bound`), which is
proved in `Lab/HenningYeo/` (`OpenProblemsLab.HY.theorem6`). So the `9/17` bound is unconditional.
-/

namespace OpenProblemsLab.E757.LowerBound

open OpenProblemsLab.HY

theorem henningYeoBound_of_theorem6 (h6 : Theorem6Bound ℝ) : HenningYeoBound := by
  intro V E hE hlin hF7
  have hL : IsL3 E := ⟨fun e he => (hE e he).2, hlin⟩
  obtain ⟨T, hTv, hT, hTw⟩ := theorem7_of_theorem6 h6 E hL hF7
  have hvV : verts E ⊆ V := by
    intro x hx
    obtain ⟨e, he, hxe⟩ := mem_verts.1 hx
    exact (hE e he).1 hxe
  refine ⟨T, hTv.trans hvV, fun e he => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hT e he
    exact ⟨x, (Finset.mem_inter.1 hx).2, (Finset.mem_inter.1 hx).1⟩
  · have := Finset.card_le_card hvV
    omega

/-- `9/17 ≤ sSup`, assuming only Henning–Yeo Theorem 6. -/
theorem nine_seventeenths_le_sSup_of_theorem6 (h6 : Theorem6Bound ℝ) :
    9 / 17 ≤ sSup {c : ℝ | Erdos757.IsAdmissible c} :=
  nine_seventeenths_le_sSup (henningYeoBound_of_theorem6 h6)

/-- Henning–Yeo Theorem 7, as used by Ma–Tang: proved, no hypothesis. -/
theorem henningYeoBound : HenningYeoBound := henningYeoBound_of_theorem6 theorem6

/-- **Erdős #757, best known lower bound** (Ma–Tang): `9/17 ≤ sSup`, unconditionally. -/
theorem nine_seventeenths_le_sSup_unconditional :
    9 / 17 ≤ sSup {c : ℝ | Erdos757.IsAdmissible c} :=
  nine_seventeenths_le_sSup henningYeoBound

/-- The upstream statement `erdos_757.variants.lowerBound` (`1/2 < sSup`), unconditionally. -/
theorem erdos_757_lowerBound {_A : Set ℝ} :
    1 / (2 : ℝ) < sSup {c | Erdos757.IsAdmissible c} :=
  erdos_757_lowerBound_of_henningYeo henningYeoBound (_A := _A)

/-- The wrapper has exactly the upstream type of `erdos_757.variants.lowerBound`. -/
example : type_of% @Erdos757.erdos_757.variants.lowerBound := @erdos_757_lowerBound

end OpenProblemsLab.E757.LowerBound
