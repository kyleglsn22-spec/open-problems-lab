import Lab.AlbertsonBerman.Forest

/-! Part of claim AB-1, see `Lab/AlbertsonBerman/Basic.lean`. -/

namespace OpenProblemsLab.AlbertsonBerman

open SimpleGraph

/-! ## The straight-line drawing -/

/-- Integer coordinates (a rounded Tutte embedding of a triangulation containing `G₂₉`). -/
def P : Fin 29 → ℤ × ℤ :=
  ![(0, 0), (53388, 31394), (53376, 31420), (53363, 31400), (53398, 31421), (50000, 90000), (100000, 0), (53388, 31356), (53352, 31435), (53415, 31372), (53379, 31451), (36665, 37705), (49754, 14149), (36498, 21900), (63818, 38285), (50988, 30552), (53468, 31220), (53335, 31508), (53432, 31469), (53309, 31396), (51737, 34012), (54190, 29645), (50730, 44318), (62299, 23504), (46098, 32305), (49971, 25343), (56062, 33602), (52946, 31454), (53596, 31844)]

lemma P_inj : ∀ i j : Fin 29, P i = P j → i = j := by decide +kernel

/-- Twice the signed area of the triangle `a b c`. -/
def orient (a b c : ℤ × ℤ) : ℤ := (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Two edges `ab`, `cd` are drawn correctly: if they share an endpoint the other two ends are not
collinear with it; otherwise one segment lies strictly on one side of the other's line. -/
def goodPair (a b c d : Fin 29) : Bool :=
  if a = c then orient (P a) (P b) (P d) ≠ 0
  else if a = d then orient (P a) (P b) (P c) ≠ 0
  else if b = c then orient (P b) (P a) (P d) ≠ 0
  else if b = d then orient (P b) (P a) (P c) ≠ 0
  else 0 < orient (P a) (P b) (P c) * orient (P a) (P b) (P d) ||
    0 < orient (P c) (P d) (P a) * orient (P c) (P d) (P b)

def edges0 : List (Fin 29 × Fin 29) :=
  [(0, 5), (0, 6), (0, 11), (0, 12), (0, 13), (1, 2), (1, 3), (1, 4), (1, 7), (1, 9), (2, 3), (2, 4), (2, 8), (2, 10), (3, 7), (3, 8), (3, 19), (4, 9), (4, 10), (4, 18)]

def edges1 : List (Fin 29 × Fin 29) :=
  [(5, 6), (5, 11), (5, 14), (5, 22), (6, 12), (6, 14), (6, 23), (7, 9), (7, 16), (7, 19), (8, 10), (8, 17), (8, 19), (9, 16), (9, 18), (10, 17), (10, 18), (11, 13), (11, 22), (11, 24)]

def edges2 : List (Fin 29 × Fin 29) :=
  [(12, 13), (12, 23), (12, 25), (13, 24), (13, 25), (14, 22), (14, 23), (14, 26), (15, 20), (15, 21), (15, 24), (15, 25), (15, 27), (16, 18), (16, 19), (16, 27), (16, 28), (17, 18), (17, 19), (17, 27)]

def edges3 : List (Fin 29 × Fin 29) :=
  [(17, 28), (18, 28), (19, 27), (20, 22), (20, 24), (20, 26), (20, 27), (20, 28), (21, 23), (21, 25), (21, 26), (21, 27), (21, 28), (22, 24), (22, 26), (23, 25), (23, 26), (24, 25), (26, 28), (27, 28)]

lemma edges_split : edges = edges0 ++ edges1 ++ edges2 ++ edges3 := by decide +kernel

end OpenProblemsLab.AlbertsonBerman
