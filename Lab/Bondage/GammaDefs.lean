import Lab.Bondage.Basic

/-!
# No five vertices dominate Yavari's graph: definitions

`checkGa a` tests every sorted 5-tuple starting with `a` (the closed neighbourhoods of the five
vertices must miss some vertex). The checks themselves are split over `GPart*.lean` to keep the
kernel's memory use low.
-/

namespace OpenProblemsLab.Bondage

open Finset

/-- The closed neighbourhoods of `l` cover every vertex. -/
def domB (l : List (Fin 18)) : Bool :=
  (List.finRange 18).all fun v => l.any fun u => (nb u).contains v

/-- No sorted 5-tuple starting with `a` dominates. -/
def checkGa (a : Fin 18) : Bool :=
  (List.finRange 18).all fun b => !(decide (a ≤ b)) ||
    (List.finRange 18).all fun c => !(decide (b ≤ c)) ||
      (List.finRange 18).all fun d => !(decide (c ≤ d)) ||
        (List.finRange 18).all fun e => !(decide (d ≤ e)) || !(domB [a, b, c, d, e])

end OpenProblemsLab.Bondage
