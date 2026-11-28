import Lab.EdmondsJohnson.THMBasic
import Lab.EdmondsJohnson.THM6.Size4

/-! Certificates for the 5 × 5 submatrices of `A6` (6 of them). -/

namespace EdmondsJohnson

set_option maxHeartbeats 0 in
/-- Certificates for the 5 × 5 submatrices of `A6`. -/
def tableA6_5 : CertTable :=
[
  (([0, 1, 2, 3, 4], [0, 1, 2, 3, 4]), Sum.inr [-1, -1, 1, 1, 0]),
  (([0, 1, 2, 3, 4], [0, 1, 2, 3, 5]), Sum.inr [-1, -1, 1, 1, 0]),
  (([0, 1, 2, 3, 4], [0, 1, 2, 4, 5]), Sum.inr [-2, -2, 0, 1, 1]),
  (([0, 1, 2, 3, 4], [0, 1, 3, 4, 5]), Sum.inr [-2, -2, 0, 1, 1]),
  (([0, 1, 2, 3, 4], [0, 2, 3, 4, 5]), Sum.inr [0, -2, -2, 1, 1]),
  (([0, 1, 2, 3, 4], [1, 2, 3, 4, 5]), Sum.inr [0, -2, -2, 1, 1])]

set_option maxHeartbeats 0 in
lemma certsA6_5 : ∀ lr ∈ (List.finRange 5).sublistsLen 5,
    ∀ lc ∈ (List.finRange 6).sublistsLen 5, certOK A6 tableA6_5 5 lr lc := by
  decide +kernel

end EdmondsJohnson
