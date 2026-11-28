import Lab.TotalDomination.NoPartner

/-! Part of claim GHT-1, see `Lab/TotalDomination/Basic.lean`. -/

namespace OpenProblemsLab.TotalDomination

open SimpleGraph

/-- Integer coordinates of a straight-line drawing of `B` (a rounded Tutte embedding with outer face
`a b z₁`), indexed by vertex number. -/
def Pl : List (ℤ × ℤ) :=
  [(0, 0), (10000, 0), (4993, 900), (2698, 919), (2301, 1247), (2181, 1700), (3294, 3467), (5000, 10000), (6204, 2431), (6573, 4239), (4368, 2490), (3498, 1528), (3128, 2086), (5088, 4525), (7292, 410), (7688, 278), (7805, 201), (6679, 212), (4925, 96), (3775, 347), (3394, 173), (5611, 414), (6488, 463), (6854, 314), (4877, 248), (4782, 4), (3490, 7), (2806, 10), (3508, 20), (3597, 41), (6033, 41), (4821, 53), (5689, 19), (5637, 9), (4226, 13), (4730, 35)]

/-- The coordinates of vertex `i`. -/
def P (i : ℕ) : ℤ × ℤ := Pl.getD i (0, 0)

lemma P_inj : ∀ i j : Fin 36, P i.val = P j.val → i = j := by decide +kernel

/-- Two edges `ab`, `cd` (vertex numbers) are drawn correctly: if they share an endpoint the other
two ends are not collinear with it; otherwise one segment lies strictly on one side of the other's
line. -/
def goodPair (a b c d : ℕ) : Bool :=
  if a = c then AlbertsonBerman.orient (P a) (P b) (P d) ≠ 0
  else if a = d then AlbertsonBerman.orient (P a) (P b) (P c) ≠ 0
  else if b = c then AlbertsonBerman.orient (P b) (P a) (P d) ≠ 0
  else if b = d then AlbertsonBerman.orient (P b) (P a) (P c) ≠ 0
  else 0 < AlbertsonBerman.orient (P a) (P b) (P c) * AlbertsonBerman.orient (P a) (P b) (P d) ||
    0 < AlbertsonBerman.orient (P c) (P d) (P a) * AlbertsonBerman.orient (P c) (P d) (P b)

def edges0 : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 18), (0, 19), (0, 20), (0, 25), (0, 26), (0, 27), (0, 28), (0, 29), (1, 2), (1, 7)]

def edges1 : List (ℕ × ℕ) :=
  [(1, 8), (1, 9), (1, 14), (1, 15), (1, 16), (1, 17), (1, 18), (1, 25), (1, 30), (1, 32), (1, 33), (2, 3), (2, 8), (2, 10), (2, 11), (2, 14), (2, 19)]

def edges2 : List (ℕ × ℕ) :=
  [(2, 21), (2, 22), (3, 4), (3, 11), (4, 5), (4, 11), (4, 12), (5, 6), (5, 12), (6, 7), (6, 10), (6, 12), (6, 13), (7, 9), (7, 13), (8, 9), (8, 10)]

def edges3 : List (ℕ × ℕ) :=
  [(8, 13), (9, 13), (10, 11), (10, 12), (10, 13), (11, 12), (14, 15), (14, 22), (15, 16), (15, 22), (15, 23), (16, 17), (16, 23), (17, 18), (17, 21), (17, 23), (17, 24)]

def edges4 : List (ℕ × ℕ) :=
  [(18, 20), (18, 24), (18, 29), (18, 30), (18, 31), (19, 20), (19, 21), (19, 24), (20, 24), (21, 22), (21, 23), (21, 24), (22, 23), (25, 26), (25, 33), (26, 27), (26, 33)]

def edges5 : List (ℕ × ℕ) :=
  [(26, 34), (27, 28), (27, 34), (28, 29), (28, 32), (28, 34), (28, 35), (29, 31), (29, 35), (30, 31), (30, 32), (30, 35), (31, 35), (32, 33), (32, 34), (32, 35), (33, 34)]

lemma edges_split : edges = edges0 ++ edges1 ++ edges2 ++ edges3 ++ edges4 ++ edges5 := by decide +kernel

end OpenProblemsLab.TotalDomination
