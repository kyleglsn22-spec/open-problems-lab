import Lab.EdmondsJohnson.THMBasic
import Lab.EdmondsJohnson.THM7.Size4

/-! Certificates for the 5 × 5 submatrices of `A7` (21 of them). -/

namespace EdmondsJohnson

set_option maxHeartbeats 0 in
/-- Certificates for the 5 × 5 submatrices of `A7`. -/
def tableA7_5 : CertTable :=
[
  (([0, 1, 2, 3, 4], [0, 1, 2, 3, 4]), Sum.inr [-1, -1, 1, 1, 0]),
  (([0, 1, 2, 3, 4], [0, 1, 2, 3, 5]), Sum.inr [-1, -1, 1, 1, 0]),
  (([0, 1, 2, 3, 4], [0, 1, 2, 3, 6]), Sum.inr [-1, -1, 1, 1, 0]),
  (([0, 1, 2, 3, 4], [0, 1, 2, 4, 5]), Sum.inr [0, 0, -2, 1, 0]),
  (([0, 1, 2, 3, 4], [0, 1, 2, 4, 6]), Sum.inr [0, 0, -2, 1, 0]),
  (([0, 1, 2, 3, 4], [0, 1, 2, 5, 6]), Sum.inr [-2, -2, 2, 1, 0]),
  (([0, 1, 2, 3, 4], [0, 1, 3, 4, 5]), Sum.inr [-2, -2, 2, 1, 0]),
  (([0, 1, 2, 3, 4], [0, 1, 3, 4, 6]), Sum.inr [-2, -2, 2, 1, 0]),
  (([0, 1, 2, 3, 4], [0, 1, 3, 5, 6]), Sum.inr [0, 0, -2, 1, 0]),
  (([0, 1, 2, 3, 4], [0, 1, 4, 5, 6]), Sum.inr [-2, -2, 1, 1, 0]),
  (([0, 1, 2, 3, 4], [0, 2, 3, 4, 5]), Sum.inr [0, -2, 0, 1, 0]),
  (([0, 1, 2, 3, 4], [0, 2, 3, 4, 6]), Sum.inr [0, -2, 0, 1, 0]),
  (([0, 1, 2, 3, 4], [0, 2, 3, 5, 6]), Sum.inr [0, 0, -2, 1, 0]),
  (([0, 1, 2, 3, 4], [0, 2, 4, 5, 6]), Sum.inr [0, -2, 1, 0, 0]),
  (([0, 1, 2, 3, 4], [0, 3, 4, 5, 6]), Sum.inr [0, -2, 0, 1, 0]),
  (([0, 1, 2, 3, 4], [1, 2, 3, 4, 5]), Sum.inr [0, -2, 0, 1, 0]),
  (([0, 1, 2, 3, 4], [1, 2, 3, 4, 6]), Sum.inr [0, -2, 0, 1, 0]),
  (([0, 1, 2, 3, 4], [1, 2, 3, 5, 6]), Sum.inr [0, 0, -2, 1, 0]),
  (([0, 1, 2, 3, 4], [1, 2, 4, 5, 6]), Sum.inr [0, -2, 1, 0, 0]),
  (([0, 1, 2, 3, 4], [1, 3, 4, 5, 6]), Sum.inr [0, -2, 0, 1, 0]),
  (([0, 1, 2, 3, 4], [2, 3, 4, 5, 6]), Sum.inr [-2, 0, 1, 0, 0])]

set_option maxHeartbeats 0 in
lemma certsA7_5 : ∀ lr ∈ (List.finRange 5).sublistsLen 5,
    ∀ lc ∈ (List.finRange 7).sublistsLen 5, certOK A7 tableA7_5 5 lr lc := by
  decide +kernel

end EdmondsJohnson
