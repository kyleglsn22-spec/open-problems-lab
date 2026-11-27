import Lab.ClawFree2.ChromCount7

/-! Colouring counts of `G`: assembling the pieces `ChromCount0` to `ChromCount7`. -/

namespace OpenProblemsLab.ClawFree.Second

open MvPolynomial Finset OpenProblemsLab.ClawFree

theorem summ_gen : summ (Enum.gen colR 12) = (24, 176, 440, 1056, true) := by
  rw [show (12 : ℕ) = 4 + 8 from rfl, Enum.gen_add, gen4]
  simp only [Enum.genFrom_append, summ_append, part_0, part_1, part_2, part_3, part_4, part_5, part_6, part_7]
  rfl

theorem chrom_5322 : coeff e5322 (chromSym G 4) = 24 := by
  have h := congrArg (·.1) summ_gen
  simp only [summ] at h
  unfold contentIs at h
  rw [coeff_chromSym_eq_gen e5322 ![5, 3, 2, 2] (fun _ => rfl), h]
  rfl

theorem chrom_4422 : coeff e4422 (chromSym G 4) = 176 := by
  have h := congrArg (·.2.1) summ_gen
  simp only [summ] at h
  unfold contentIs at h
  rw [coeff_chromSym_eq_gen e4422 ![4, 4, 2, 2] (fun _ => rfl), h]
  rfl

theorem chrom_4332 : coeff e4332 (chromSym G 4) = 440 := by
  have h := congrArg (·.2.2.1) summ_gen
  simp only [summ] at h
  unfold contentIs at h
  rw [coeff_chromSym_eq_gen e4332 ![4, 3, 3, 2] (fun _ => rfl), h]
  rfl

theorem chrom_3333 : coeff e3333 (chromSym G 4) = 1056 := by
  have h := congrArg (·.2.2.2.1) summ_gen
  simp only [summ] at h
  unfold contentIs at h
  rw [coeff_chromSym_eq_gen e3333 ![3, 3, 3, 3] (fun _ => rfl), h]
  rfl

end OpenProblemsLab.ClawFree.Second
