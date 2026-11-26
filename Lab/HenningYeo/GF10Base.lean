import Lab.HenningYeo.Claim9

/-!
# Template facts for Claim 10 (by `decide`, on bitmasks)

The seven edges of the template `gadget l a b` are encoded as bitmasks `EM l a b k`. For a set of
template vertices `n` (those adjacent to the deleted vertex `x`), `tD` is the resulting degree in
`H`. `P10` collects the constraints that Claims 4–8 impose; `no_P10` checks that none survives.
-/

namespace OpenProblemsLab.HY

/-- Bitmasks of the lines of `F₇`. -/
def lm : Fin 5 → ℕ := ![7, 25, 97, 42, 84]

/-- The seven edges of `gadget l a b`, as bitmasks. -/
def ems (l : Fin 5) (a b : Fin 7) : List ℕ :=
  ((List.finRange 5).filter (· ≠ l)).map lm ++
    [896, 256 + lm l - 2 ^ (b : ℕ), 512 + lm l - 2 ^ (a : ℕ)]

def EM (l : Fin 5) (a b : Fin 7) (k : Fin 7) : ℕ := (ems l a b).getD k 0

/-- Template vertex `i` lies in template edge `k`. -/
def tmem (l : Fin 5) (a b : Fin 7) (k : Fin 7) (i : Fin 10) : Bool := (EM l a b k).testBit i

def tdg (l : Fin 5) (a b : Fin 7) (i : Fin 10) : ℕ :=
  ((List.finRange 7).filter (fun k => tmem l a b k i)).length

def tadj (l : Fin 5) (a b : Fin 7) (v p : Fin 10) : Prop := v ≠ p ∧ ∃ k, tmem l a b k v ∧ tmem l a b k p

instance (l : Fin 5) (a b : Fin 7) (v p : Fin 10) : Decidable (tadj l a b v p) := by
  unfold tadj; infer_instance

def tD (l : Fin 5) (a b : Fin 7) (n : Fin 10 → Bool) (i : Fin 10) : ℕ :=
  tdg l a b i + if n i then 1 else 0

/-- The constraints of Claim 10. -/
def P10 (l : Fin 5) (a b : Fin 7) (n : Fin 10 → Bool) : Prop :=
  (∀ i, 2 ≤ tD l a b n i ∧ tD l a b n i ≤ 3) ∧ n 7 = true ∧
  ((List.finRange 10).filter n).length ≤ 6 ∧
  (∀ k, (∀ i, tmem l a b k i → n i) → ∀ i, tmem l a b k i → tD l a b n i = 3) ∧
  (∀ v k, (∀ i, tmem l a b k i → tadj l a b v i) → ∀ i, tmem l a b k i → tD l a b n i = 3) ∧
  (∀ v, n v = false → tD l a b n v = 3 → ∀ z, tadj l a b v z → n z = false → tdg l a b z = 2 →
    ∀ k, tmem l a b k z → tmem l a b k v = false → ∀ p, tmem l a b k p → p ≠ z →
      tD l a b n p = 2 + if tadj l a b v p then 1 else 0)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1000 in
instance (l : Fin 5) (a b : Fin 7) (n : Fin 10 → Bool) : Decidable (P10 l a b n) := by
  unfold P10; infer_instance

end OpenProblemsLab.HY
