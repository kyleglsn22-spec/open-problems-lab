import Mathlib

/-!
# A verified backtracking counter

Counting the functions `f : Fin m → Fin k` that satisfy a family of pairwise constraints
`R a b (f a) (f b)` (for all `a < b`) by brute force is hopeless when `k ^ m` is in the millions,
because the Lean kernel would have to look at every function. Instead we build the list of all
*valid* assignments one position at a time, discarding a partial assignment as soon as it breaks a
constraint (`gen`). This file proves that the list is exactly the set of valid assignments
(`mem_gen`), without repetitions (`nodup_gen`), so counting valid functions with any extra
property reduces to filtering and measuring a list the kernel can compute (`card_filter_eq`).
-/

namespace OpenProblemsLab.ClawFree.Enum

variable {k : ℕ}

/-- Adding the colour `c` as the next position (index `l.length`) is compatible with every earlier
position. -/
def okB (R : ℕ → ℕ → Fin k → Fin k → Bool) (l : List (Fin k)) (c : Fin k) : Bool :=
  (List.range l.length).all fun i => R i l.length (l.getD i c) c

/-- One backtracking step: extend every partial assignment by every compatible colour. -/
def ext (R : ℕ → ℕ → Fin k → Fin k → Bool) (L : List (List (Fin k))) : List (List (Fin k)) :=
  L.flatMap fun l => ((List.finRange k).filter (okB R l)).map fun c => l ++ [c]

/-- All valid assignments of length `j`, built by backtracking. -/
def gen (R : ℕ → ℕ → Fin k → Fin k → Bool) : ℕ → List (List (Fin k))
  | 0 => [[]]
  | j + 1 => ext R (gen R j)

/-- `j` backtracking steps starting from the partial assignments `L`. -/
def genFrom (R : ℕ → ℕ → Fin k → Fin k → Bool) (L : List (List (Fin k))) :
    ℕ → List (List (Fin k))
  | 0 => L
  | j + 1 => ext R (genFrom R L j)

theorem gen_add (R : ℕ → ℕ → Fin k → Fin k → Bool) (i j : ℕ) :
    gen R (i + j) = genFrom R (gen R i) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [← Nat.add_assoc, gen, ih, genFrom]

theorem genFrom_append (R : ℕ → ℕ → Fin k → Fin k → Bool) (L₁ L₂ : List (List (Fin k)))
    (j : ℕ) : genFrom R (L₁ ++ L₂) j = genFrom R L₁ j ++ genFrom R L₂ j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [genFrom, ih, ext, List.flatMap_append]

theorem genFrom_cons (R : ℕ → ℕ → Fin k → Fin k → Bool) (p : List (Fin k))
    (L : List (List (Fin k))) (j : ℕ) :
    genFrom R (p :: L) j = genFrom R [p] j ++ genFrom R L j := by
  rw [← genFrom_append]; rfl

/-- A list is valid if every pair of positions `a < b` satisfies `R`. -/
def Valid (R : ℕ → ℕ → Fin k → Fin k → Bool) (l : List (Fin k)) : Prop :=
  ∀ a b (hab : a < b) (hb : b < l.length), R a b (l[a]'(by omega)) l[b] = true

theorem valid_append (R : ℕ → ℕ → Fin k → Fin k → Bool) (l : List (Fin k)) (c : Fin k) :
    Valid R (l ++ [c]) ↔ Valid R l ∧ okB R l c = true := by
  constructor
  · intro h
    refine ⟨fun a b hab hb => ?_, ?_⟩
    · have := h a b hab (by simp; omega)
      simpa [List.getElem_append_left (show a < l.length by omega),
        List.getElem_append_left hb] using this
    · simp only [okB, List.all_eq_true, List.mem_range]
      intro i hi
      have := h i l.length hi (by simp)
      rw [List.getD_eq_getElem _ _ hi]
      simpa [List.getElem_append_left hi] using this
  · rintro ⟨h1, h2⟩ a b hab hb
    simp only [List.length_append, List.length_singleton] at hb
    rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | hb
    · have := h1 a b hab hb
      simpa [List.getElem_append_left (show a < l.length by omega),
        List.getElem_append_left hb] using this
    · subst hb
      simp only [okB, List.all_eq_true, List.mem_range] at h2
      have := h2 a hab
      rw [List.getD_eq_getElem _ _ hab] at this
      simpa [List.getElem_append_left hab] using this

theorem mem_gen (R : ℕ → ℕ → Fin k → Fin k → Bool) (j : ℕ) (l : List (Fin k)) :
    l ∈ gen R j ↔ l.length = j ∧ Valid R l := by
  induction j generalizing l with
  | zero =>
    simp only [gen, List.mem_singleton, List.length_eq_zero_iff, iff_self_and]
    rintro rfl a b hab hb
    simp at hb
  | succ j ih =>
    simp only [gen, ext, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
    constructor
    · rintro ⟨l', hl', c, hc, rfl⟩
      obtain ⟨hlen, hv⟩ := (ih l').mp hl'
      exact ⟨by simp [hlen], (valid_append R l' c).mpr ⟨hv, hc⟩⟩
    · rintro ⟨hlen, hv⟩
      have hne : l ≠ [] := by rintro rfl; simp at hlen
      have hl := List.dropLast_append_getLast hne
      rw [← hl] at hv
      obtain ⟨hv1, hv2⟩ := (valid_append R _ _).mp hv
      refine ⟨l.dropLast, (ih _).mpr ⟨by simp [hlen], hv1⟩, l.getLast hne, hv2, hl⟩

theorem nodup_gen (R : ℕ → ℕ → Fin k → Fin k → Bool) (j : ℕ) : (gen R j).Nodup := by
  induction j with
  | zero => simp [gen]
  | succ j ih =>
    simp only [gen, ext]
    rw [List.nodup_flatMap]
    refine ⟨fun l _ => ?_, ih.imp fun {l₁ l₂} hne => ?_⟩
    · refine List.Nodup.map (fun c d h => ?_) ((List.nodup_finRange k).filter _)
      simpa using h
    · intro x h1 h2
      simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and] at h1 h2
      obtain ⟨c, -, rfl⟩ := h1
      obtain ⟨d, -, h⟩ := h2
      exact hne (List.append_inj' h rfl).1.symm

theorem valid_ofFn_iff (R : ℕ → ℕ → Fin k → Fin k → Bool) {m : ℕ} (f : Fin m → Fin k) :
    Valid R (List.ofFn f) ↔ ∀ a b : Fin m, a < b → R a b (f a) (f b) = true := by
  constructor
  · intro h a b hab
    have := h a b hab (by simp)
    simpa using this
  · intro h a b hab hb
    simp only [List.length_ofFn] at hb
    simpa using h ⟨a, by omega⟩ ⟨b, hb⟩ hab

theorem count_ofFn {m : ℕ} (f : Fin m → Fin k) (i : Fin k) :
    (List.ofFn f).count i = (Finset.univ.filter fun d => f d = i).card := by
  rw [← Multiset.coe_count, ← Fin.univ_val_map, Multiset.count_map, Finset.card_def,
    Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun d _ => eq_comm)

/-- Counting valid functions with a property `Q` reduces to filtering the backtracking list. -/
theorem card_filter_eq (R : ℕ → ℕ → Fin k → Fin k → Bool) {m : ℕ}
    (P Q : (Fin m → Fin k) → Prop) [DecidablePred P] [DecidablePred Q]
    (q : List (Fin k) → Bool)
    (hP : ∀ f, P f ↔ ∀ a b : Fin m, a < b → R a b (f a) (f b) = true)
    (hQ : ∀ f, Q f ↔ q (List.ofFn f) = true) :
    (Finset.univ.filter fun f => P f ∧ Q f).card = ((gen R m).filter q).length := by
  rw [← List.toFinset_card_of_nodup ((nodup_gen R m).filter q),
    ← Finset.card_image_of_injective _ List.ofFn_injective]
  congr 1
  ext l
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset,
    List.mem_filter, mem_gen]
  constructor
  · rintro ⟨f, ⟨hp, hq⟩, rfl⟩
    exact ⟨⟨by simp, (valid_ofFn_iff R f).mpr ((hP f).mp hp)⟩, (hQ f).mp hq⟩
  · rintro ⟨⟨hlen, hv⟩, hq⟩
    subst hlen
    have e : List.ofFn (fun i : Fin l.length => l[i]) = l := by
      apply List.ext_getElem <;> simp
    refine ⟨fun i => l[i], ⟨(hP _).mpr ?_, (hQ _).mpr ?_⟩, e⟩
    · rw [← valid_ofFn_iff, e]; exact hv
    · rw [e]; exact hq

end OpenProblemsLab.ClawFree.Enum
