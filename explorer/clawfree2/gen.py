# Generates Lab/ClawFree2/Graph.lean and ChromCount*.lean (run from open-problems-lab/).
# Second minimal claw-free counterexample (graph6 K?`CR@`bAbRB, 12 vertices, 21 edges).
from collections import Counter
g6 = 'K?`CR@`bAbRB'
d = [ord(c) - 63 for c in g6]; n = d[0]; bits = []
for x in d[1:]:
    bits += [(x >> (5 - i)) & 1 for i in range(6)]
A = [[False] * n for _ in range(n)]; k = 0
for j in range(1, n):
    for i in range(j):
        A[i][j] = A[j][i] = bool(bits[k]); k += 1
E = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i][j]]
adjBits = sum(1 << (12 * b + a) for a in range(n) for b in range(n) if A[a][b])
SH = [(5, 3, 2, 2), (4, 4, 2, 2), (4, 3, 3, 2), (3, 3, 3, 3)]
def ext(L):
    out = []
    for l in L:
        j = len(l)
        for c in range(4):
            if all(not A[i][j] or l[i] != c for i in range(j)): out.append(l + [c])
    return out
def gf(L, j):
    for _ in range(j): L = ext(L)
    return L
def summ(L):
    cs = Counter(tuple(l.count(i) for i in range(4)) for l in L)
    ok = all(list(c) != sorted(c, reverse=True) or c in SH for c in cs)
    return tuple(cs[s] for s in SH), ok
lit = lambda l: '[' + ', '.join(map(str, l)) + ']'
NS = 'OpenProblemsLab.ClawFree.Second'
graph = '''import Lab.ClawFree.Tools
import Lab.ClawFree.Enum

/-!
# The second minimal counterexample: the graph and its colourings

See `Lab/ClawFree2/Counterexample.lean` for the overview. Here: the graph (given by its edge list,
from the graph6 code ``K?`CR@`bAbRB``), its claw-freeness, and the reduction of monomial
coefficients of `X_G` to counting lists of colourings (the same method as `Lab/ClawFree/Graph.lean`).
-/

namespace %(NS)s

open MvPolynomial Finset OpenProblemsLab.ClawFree

/-! ### The graph -/

/-- The 21 edges of `G` on the vertices `0 … 11`. -/
def edgesG : List (ℕ × ℕ) :=
  %(E)s

/-- Adjacency: `i ~ j` iff `(i, j)` or `(j, i)` is an edge. -/
def adjN (i j : ℕ) : Bool := edgesG.contains (i, j) || edgesG.contains (j, i)

theorem adjN_symm : ∀ i j : Fin 12, adjN i j = true → adjN j i = true := by decide

theorem adjN_irrefl : ∀ i : Fin 12, adjN i i = false := by decide

/-- The graph `G` on vertex set `Fin 12`. -/
def G : SimpleGraph (Fin 12) where
  Adj i j := adjN i j = true
  symm := ⟨fun i j h => adjN_symm i j h⟩
  loopless := ⟨fun i h => by simp [adjN_irrefl i] at h⟩

theorem G_adj {i j : Fin 12} : G.Adj i j ↔ adjN i j = true := Iff.rfl

instance : DecidableRel G.Adj := fun _ _ => decidable_of_iff _ G_adj.symm

/-- Boolean form of "no claw centred at `v` with leaves `a, b, c`". -/
def clawB (v a b c : Fin 12) : Bool :=
  !(adjN v a && adjN v b && adjN v c && a != b && a != c && b != c) ||
    (adjN a b || adjN a c || adjN b c)

theorem clawB_all : ∀ v a b c : Fin 12, clawB v a b c = true := by decide

theorem G_isClawFree : IsClawFree G := by
  intro v a b c hva hvb hvc hab hac hbc
  have := clawB_all v a b c
  rw [clawB, G_adj.mp hva, G_adj.mp hvb, G_adj.mp hvc, bne_iff_ne.mpr hab, bne_iff_ne.mpr hac,
    bne_iff_ne.mpr hbc] at this
  simp only [G_adj]
  simpa [or_assoc] using this

/-! ### Monomial coefficients of `X_G` -/

/-- The adjacency matrix of `G` packed into one number: bit `12 b + a` is set iff `a ~ b`.
This is only a faster lookup table for the kernel; `adjB_eq` checks it against `adjN`. -/
def adjBits : ℕ := %(adjBits)d

/-- Fast adjacency lookup. -/
def adjB (a b : ℕ) : Bool := (adjBits >>> (12 * b + a)) %% 2 == 1

theorem adjB_eq : ∀ a b : Fin 12, adjB a b = adjN a b := by decide

/-- The colouring constraint between vertices `a < b`. -/
def colR (a b : ℕ) (x y : Fin 4) : Bool := !(adjB a b) || (x != y)

theorem proper_iff (κ : Fin 12 → Fin 4) :
    (∀ u v, G.Adj u v → κ u ≠ κ v) ↔ ∀ a b : Fin 12, a < b → colR a b (κ a) (κ b) = true := by
  constructor
  · intro h a b _
    simp only [colR, adjB_eq, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq]
    by_cases hab : adjN a b = true
    · exact Or.inr (h a b (G_adj.mpr hab))
    · exact Or.inl (by simpa using hab)
  · intro h u v huv
    have hne : u ≠ v := G.ne_of_adj huv
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := h u v hlt
      simp only [colR, adjB_eq, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne] at this
      exact this.resolve_left (by simp [G_adj.mp huv])
    · have := h v u hlt
      simp only [colR, adjB_eq, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne] at this
      exact (this.resolve_left (by simp [adjN_symm u v (G_adj.mp huv)])).symm

theorem coeff_chromSym_eq_gen (α : Fin 4 →₀ ℕ) (w : Fin 4 → ℕ) (hw : ∀ i, α i = w i) :
    coeff α (chromSym G 4) =
      (((Enum.gen colR 12).filter
        fun l => (List.finRange 4).all fun i => l.count i == w i).length : ℤ) := by
  rw [chromSym, coeff_sum_prod_X, Finset.filter_filter,
    ← card_content_eq colR (fun κ : Fin 12 → Fin 4 => ∀ u v, G.Adj u v → κ u ≠ κ v) α w hw
      proper_iff]
  exact_mod_cast Finset.card_bij (fun a _ => a) (fun a ha => by simpa using ha)
    (fun _ _ _ _ h => h) (fun b hb => ⟨b, by simpa using hb, rfl⟩)

/-- `x^{5322}`, `x^{4422}`, `x^{4332}`, `x^{3333}` as exponent vectors. -/
noncomputable def e5322 : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![5, 3, 2, 2]
noncomputable def e4422 : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![4, 4, 2, 2]
noncomputable def e4332 : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![4, 3, 3, 2]
noncomputable def e3333 : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![3, 3, 3, 3]

/-- Every proper 4-colouring whose class sizes are non-increasing has class sizes `5322`, `4422`,
`4332` or `3333`. -/
def antiOK (l : List (Fin 4)) : Bool :=
  !(decide (l.count 1 ≤ l.count 0) && decide (l.count 2 ≤ l.count 1) &&
      decide (l.count 3 ≤ l.count 2)) ||
    ([l.count 0, l.count 1, l.count 2, l.count 3] == [5, 3, 2, 2] ||
     [l.count 0, l.count 1, l.count 2, l.count 3] == [4, 4, 2, 2] ||
     [l.count 0, l.count 1, l.count 2, l.count 3] == [4, 3, 3, 2] ||
     [l.count 0, l.count 1, l.count 2, l.count 3] == [3, 3, 3, 3])

/-- The content test "class sizes equal `w`" used for counting. -/
def contentIs (w : Fin 4 → ℕ) (l : List (Fin 4)) : Bool :=
  (List.finRange 4).all fun i => l.count i == w i

/-- All facts about a list of colourings that we need, gathered so that the kernel computes them
in one pass: the numbers with class sizes `5322`, `4422`, `4332`, `3333`, and `antiOK` for all. -/
def summ (L : List (List (Fin 4))) : ℕ × ℕ × ℕ × ℕ × Bool :=
  ((L.filter (contentIs ![5, 3, 2, 2])).length, (L.filter (contentIs ![4, 4, 2, 2])).length,
    (L.filter (contentIs ![4, 3, 3, 2])).length, (L.filter (contentIs ![3, 3, 3, 3])).length,
    L.all antiOK)

/-- Componentwise combination of two summaries. -/
def summAdd (x y : ℕ × ℕ × ℕ × ℕ × Bool) : ℕ × ℕ × ℕ × ℕ × Bool :=
  (x.1 + y.1, x.2.1 + y.2.1, x.2.2.1 + y.2.2.1, x.2.2.2.1 + y.2.2.2.1, x.2.2.2.2 && y.2.2.2.2)

theorem summ_append (L₁ L₂ : List (List (Fin 4))) :
    summ (L₁ ++ L₂) = summAdd (summ L₁) (summ L₂) := by
  simp [summ, summAdd, List.filter_append, List.all_append]

end %(NS)s
''' % dict(NS=NS, E='[' + ', '.join('(%d, %d)' % e for e in E) + ']', adjBits=adjBits)
open('Lab/ClawFree2/Graph.lean', 'w').write(graph)

import sys
D = int(sys.argv[1]) if len(sys.argv) > 1 else 4
NCH = int(sys.argv[2]) if len(sys.argv) > 2 else 8
P = gf([[]], D)
hdr = 'namespace %s\n\nopen MvPolynomial Finset OpenProblemsLab.ClawFree\n\n' % NS
prefs = []; pt = []; tot = [0] * 4
for i, p in enumerate(P):
    s, ok = summ(gf([p], 12 - D)); assert ok
    tot = [a + b for a, b in zip(tot, s)]; pt.append(s)
    prefs.append('theorem pref_%d : summ (Enum.genFrom colR [%s] %d) = (%d, %d, %d, %d, true) := by\n  decide +kernel\n' % (i, lit(p), 12 - D, *s))
print('prefixes', len(P), 'totals', tot)
per = (len(prefs) + NCH - 1) // NCH
chunks = [P[c * per:(c + 1) * per] for c in range(NCH)]
genthm = ''.join('/-- Prefixes handled in part %d. -/\ndef L%d : List (List (Fin 4)) := [\n' % (c, c) + ',\n'.join('    ' + lit(p) for p in ch) + ']\n\n' for c, ch in enumerate(chunks))
genthm += 'theorem gen%d : Enum.gen colR %d = %s := by\n  decide +kernel\n\n' % (D, D, ' ++ '.join('L%d' % c for c in range(NCH)))
genthm += """theorem genFrom_cons2 (p q : List (Fin 4)) (L : List (List (Fin 4))) (j : ℕ) :
    Enum.genFrom colR (p :: q :: L) j = Enum.genFrom colR [p] j ++ Enum.genFrom colR (q :: L) j :=
  Enum.genFrom_cons colR p (q :: L) j

"""
prev = 'Lab.ClawFree2.Graph'
for c in range(NCH):
    doc = ("""/-!
# Counting the proper 4-colourings of `G` by class sizes

As in `Lab/ClawFree/ChromCount0.lean`: the kernel enumerates the proper colourings with the verified
backtracking list, split by the colours of the first %d vertices (`gen%d` lists the %d valid
prefixes in %d parts `L0 … L%d`; each `pref_i` handles one prefix in its own declaration, and
`part_c` adds up part `c`). `summ_gen` in `ChromCount` adds the parts up.
-/""" % (D, D, len(P), NCH, NCH - 1)) if c == 0 else '/-! Colouring counts of `G`, part %d of %d (see `ChromCount0`). -/' % (c, NCH)
    idx = range(c * per, min((c + 1) * per, len(P)))
    ptot = [sum(x) for x in zip(*[pt[i] for i in idx])]
    part = 'theorem part_%d : summ (Enum.genFrom colR L%d %d) = (%d, %d, %d, %d, true) := by\n  simp only [L%d, genFrom_cons2, summ_append, %s]\n  rfl\n' % (c, c, 12 - D, *ptot, c, ', '.join('pref_%d' % i for i in idx))
    body = (genthm if c == 0 else '') + '\n'.join(prefs[i] for i in idx) + '\n' + part
    open('Lab/ClawFree2/ChromCount%d.lean' % c, 'w').write('import %s\n\n%s\n\n%s%s\nend %s\n' % (prev, doc, hdr, body, NS))
    prev = 'Lab.ClawFree2.ChromCount%d' % c
apps = ' ++ '.join('L%d' % c for c in range(NCH))
tail = """theorem summ_gen : summ (Enum.gen colR 12) = (%d, %d, %d, %d, true) := by
  rw [show (12 : ℕ) = %d + %d from rfl, Enum.gen_add, gen%d]
  simp only [Enum.genFrom_append, summ_append, %s]
  rfl

""" % (*tot, D, 12 - D, D, ', '.join('part_%d' % c for c in range(NCH)))
for nm, w, v, k in [('5322', '![5, 3, 2, 2]', tot[0], '1'), ('4422', '![4, 4, 2, 2]', tot[1], '2.1'),
                    ('4332', '![4, 3, 3, 2]', tot[2], '2.2.1'), ('3333', '![3, 3, 3, 3]', tot[3], '2.2.2.1')]:
    tail += '''theorem chrom_%s : coeff e%s (chromSym G 4) = %d := by
  have h := congrArg (·.%s) summ_gen
  simp only [summ] at h
  unfold contentIs at h
  rw [coeff_chromSym_eq_gen e%s %s (fun _ => rfl), h]
  rfl

''' % (nm, nm, v, k, nm, w)
open('Lab/ClawFree2/ChromCount.lean', 'w').write('import %s\n\n/-! Colouring counts of `G`: assembling the pieces `ChromCount0` to `ChromCount%d`. -/\n\n%s%send %s\n' % (prev, NCH - 1, hdr, tail, NS))
