import Lab.EdmondsJohnson.THMBasic
import Lab.EdmondsJohnson.A7
import Lab.EdmondsJohnson.THM6plus.Main

/-! Certificates for the 1 × 1 submatrices of `A7` (35 of them). -/

namespace EdmondsJohnson

set_option maxHeartbeats 0 in
/-- Certificates for the 1 × 1 submatrices of `A7`. -/
def tableA7_1 : CertTable :=
[
  (([0], [0]), Sum.inr [1]),
  (([0], [1]), Sum.inr [1]),
  (([0], [2]), Sum.inl [[2]]),
  (([0], [3]), Sum.inl [[-2]]),
  (([0], [4]), Sum.inl [[1]]),
  (([0], [5]), Sum.inl [[-1]]),
  (([0], [6]), Sum.inl [[1]]),
  (([1], [0]), Sum.inr [1]),
  (([1], [1]), Sum.inl [[2]]),
  (([1], [2]), Sum.inl [[2]]),
  (([1], [3]), Sum.inr [1]),
  (([1], [4]), Sum.inl [[1]]),
  (([1], [5]), Sum.inr [1]),
  (([1], [6]), Sum.inr [1]),
  (([2], [0]), Sum.inr [1]),
  (([2], [1]), Sum.inl [[2]]),
  (([2], [2]), Sum.inr [1]),
  (([2], [3]), Sum.inl [[2]]),
  (([2], [4]), Sum.inr [1]),
  (([2], [5]), Sum.inl [[1]]),
  (([2], [6]), Sum.inr [1]),
  (([3], [0]), Sum.inl [[2]]),
  (([3], [1]), Sum.inr [1]),
  (([3], [2]), Sum.inl [[2]]),
  (([3], [3]), Sum.inr [1]),
  (([3], [4]), Sum.inl [[1]]),
  (([3], [5]), Sum.inr [1]),
  (([3], [6]), Sum.inr [1]),
  (([4], [0]), Sum.inl [[2]]),
  (([4], [1]), Sum.inr [1]),
  (([4], [2]), Sum.inr [1]),
  (([4], [3]), Sum.inl [[2]]),
  (([4], [4]), Sum.inr [1]),
  (([4], [5]), Sum.inl [[1]]),
  (([4], [6]), Sum.inr [1])]

set_option maxHeartbeats 0 in
lemma certsA7_1 : ∀ lr ∈ (List.finRange 5).sublistsLen 1,
    ∀ lc ∈ (List.finRange 7).sublistsLen 1, certOK A7 tableA7_1 1 lr lc := by
  decide +kernel

end EdmondsJohnson
