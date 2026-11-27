import Lab.ClawFree.ChromCount5

/-! Colouring counts of `G`: assembling the pieces `ChromCount0` to `ChromCount5`. -/

namespace OpenProblemsLab.ClawFree.Counterexample

open MvPolynomial Finset OpenProblemsLab.ClawFree

theorem genFrom_cons2 (p q : List (Fin 4)) (L : List (List (Fin 4))) (j : ℕ) :
    Enum.genFrom colR (p :: q :: L) j = Enum.genFrom colR [p] j ++ Enum.genFrom colR (q :: L) j :=
  Enum.genFrom_cons colR p (q :: L) j

theorem summ_gen : summ (Enum.gen colR 12) = (128, 320, 768, true) := by
  rw [show (12 : ℕ) = 4 + 8 from rfl, Enum.gen_add, gen4]
  simp only [genFrom_cons2, summ_append, pref_0, pref_1, pref_2, pref_3, pref_4, pref_5, pref_6, pref_7, pref_8, pref_9, pref_10, pref_11, pref_12, pref_13, pref_14, pref_15, pref_16, pref_17, pref_18, pref_19, pref_20, pref_21, pref_22, pref_23, pref_24, pref_25, pref_26, pref_27, pref_28, pref_29, pref_30, pref_31, pref_32, pref_33, pref_34, pref_35, pref_36, pref_37, pref_38, pref_39, pref_40, pref_41, pref_42, pref_43, pref_44, pref_45, pref_46, pref_47, pref_48, pref_49, pref_50, pref_51, pref_52, pref_53, pref_54, pref_55, pref_56, pref_57, pref_58, pref_59, pref_60, pref_61, pref_62, pref_63, pref_64, pref_65, pref_66, pref_67, pref_68, pref_69, pref_70, pref_71, pref_72, pref_73, pref_74, pref_75, pref_76, pref_77, pref_78, pref_79, pref_80, pref_81, pref_82, pref_83]
  rfl

theorem chrom_4422 : coeff e4422 (chromSym G 4) = 128 := by
  have h := congrArg (·.1) summ_gen
  simp only [summ] at h
  unfold contentIs at h
  rw [coeff_chromSym_eq_gen e4422 ![4, 4, 2, 2] (fun _ => rfl), h]
  rfl

theorem chrom_4332 : coeff e4332 (chromSym G 4) = 320 := by
  have h := congrArg (·.2.1) summ_gen
  simp only [summ] at h
  unfold contentIs at h
  rw [coeff_chromSym_eq_gen e4332 ![4, 3, 3, 2] (fun _ => rfl), h]
  rfl

theorem chrom_3333 : coeff e3333 (chromSym G 4) = 768 := by
  have h := congrArg (·.2.2.1) summ_gen
  simp only [summ] at h
  unfold contentIs at h
  rw [coeff_chromSym_eq_gen e3333 ![3, 3, 3, 3] (fun _ => rfl), h]
  rfl

end OpenProblemsLab.ClawFree.Counterexample
