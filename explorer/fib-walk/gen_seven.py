"""Generate Lab/FibWalk/Seven/{Patterns,Main}.lean: a Lean proof that 17 ∈ D₇ \\ U₇.

For up-integers u_k ≥ 105 the seven consecutive gaps s_1..s_7 lie in [1,5] (gap_le_five_U).
We search the tree of gap prefixes. A prefix is cut when some window
[u_{k+i}, u_{k+d}] of it is infeasible for the threshold and up-shift constraints. Each cut
uses a lemma `cpat_U_*` about that minimal window. Python finds the tree with floating point;
Lean re-proves every cut with exact arithmetic (linarith).
"""
import math, sys
phi = (1 + 5 ** .5) / 2
rho = (2 + phi) / 5; eta = (3 - phi) / 5
fibs = [0, 1, 1, 2, 3, 5, 8, 13, 21]
JS = [2, 3, 4, 5, 6]
th = {j: (phi ** (j - 2) + 1) / (5 ** .5 * phi ** (j - 1)) for j in JS}
sdown = {j: (-1) ** j * fibs[j] for j in JS}
L_STEPS, GAP = 7, 17
floor = [math.floor(j * phi) for j in range(40)]

def feasible_D(D):
    g = len(D) - 1
    bps = sorted({0.0, 1.0} | {(1 - (j * phi) % 1) % 1 for j in range(g + 1)})
    for lo, hi in zip(bps, bps[1:]):
        if hi - lo < 1e-12: continue
        mid = (lo + hi) / 2
        L, H = lo, hi
        c = [(j * phi) % 1 - (1 if (mid + (j * phi) % 1) >= 1 else 0) for j in range(g + 1)]
        for j in range(g + 1):
            if D[j]: H = min(H, rho - c[j])
            else: L = max(L, eta - c[j])
        for p in range(g + 1):
            if not D[p]: continue
            for jj in JS:
                q = p + sdown[jj]
                if 0 <= q <= g and not D[q]: H = min(H, th[jj] - c[p])
        if L < H - 1e-9: return True   # conservative: tiny slivers count as feasible
    return False

def feas_U(V):  # U-pattern (left to right) = mirror of a D-pattern
    return feasible_D(list(V)[::-1])

def offsets(V): return [i for i, x in enumerate(V) if x]

lemmas = {}
def build(prefix, tot, d):
    """Return proof-tree node for gap prefix (list of gaps)."""
    if d == L_STEPS:
        return ('leaf',)
    kids = []
    for s in range(1, 6):
        rem = L_STEPS - d - 1
        if tot + s + rem > GAP or tot + s + 5 * rem < GAP:
            kids.append(('arith',)); continue
        gaps = prefix + [s]
        V = [True]
        for x in gaps: V += [False] * (x - 1) + [True]
        if feas_U(V):
            kids.append(build(gaps, tot + s, d + 1)); continue
        mem = offsets(V)
        cut = None
        for i in reversed(range(len(mem) - 1)):
            W = V[mem[i]:]
            if not feas_U(W):
                cut = (i, tuple(m - mem[i] for m in mem[i:])); break
        assert cut
        lemmas[cut[1]] = True
        kids.append(('cut', cut[0], cut[1]))
    return ('node', kids)

tree = build([], 0, 0)
name = lambda offs: 'w' + '_'.join(map(str, offs))
print(len(lemmas), 'window lemmas')

UP = [(-1, 'θ₂'), (2, 'θ₃'), (-3, 'θ₄'), (5, 'θ₅'), (-8, 'θ₆')]
def dv(j): return 'x' if j == 0 else f'd{j}'
def pos(j): return 'n' if j == 0 else f'(n + {j})'
def posr(j): return 'n' if j == 0 else f'n + {j}'
LEM = {-1: 'up_minus1', 2: 'up_plus2', -3: 'up_minus3', 5: 'up_plus5', -8: 'up_minus8'}

def gen_window(offs):
    g = offs[-1]; M = set(offs); nm = name(offs)
    hyps, terms = [], []
    hyps.append('(x ' + ' '.join(dv(j) for j in range(1, g + 1)) + ' : ℝ)')
    hyps.append('(hx0 : 0 ≤ x) (hx1 : x < 1)')
    terms.append(' '.join(f'(δ {pos(j)})' for j in range(g + 1)))
    terms.append('(Int.fract_nonneg _) (Int.fract_lt_one _)')
    for j in range(1, g + 1):
        al = f'({j} * φ - {floor[j]})'
        hyps.append(f'(e{j} : d{j} = x + {al} ∨ d{j} = x + {al} - 1) (b{j} : 0 ≤ d{j} ∧ d{j} < 1)')
        terms.append(f'(by have := delta_add n {j} {floor[j]} (by norm_num; linarith) (by norm_num; linarith); '
                     f'push_cast at this; exact this)')
        terms.append('⟨Int.fract_nonneg _, Int.fract_lt_one _⟩')
    for j in range(g + 1):
        if j in M:
            hyps.append(f'(t{j} : η < {dv(j)})'); terms.append(f'M{j}.lt_delta')
        else:
            hyps.append(f'(t{j} : {dv(j)} < ρ)'); terms.append(f'(isDown_of_not_isUp (by omega) N{j}).delta_lt')
    for p in offs:
        for s, thn in UP:
            q = p + s
            if 0 <= q <= g and q not in M:
                hyps.append(f'(s{p}_{q} : 1 - {thn} < {dv(p)})')
                lhs = f'{posr(p)} + {s}' if s > 0 else f'{posr(p)} - {-s}'
                terms.append(f'(lt_of_not_ge fun hθ => N{q} (by have hh := {LEM[s]} (N := {posr(p)}) (by omega) M{p} hθ; '
                             f'rwa [show {lhs} = {posr(q)} by omega] at hh))')
    L = []
    L.append(f'/-- Real-arithmetic core of the up window with members at offsets `{list(offs)}`. -/')
    L.append(f'theorem core_{nm} ' + '\n    '.join(hyps) + ' : False := by')
    L.append('  have hp := phi_bounds')
    L.append('  simp only [ρ, η, θ₂, θ₃, θ₄, θ₅, θ₆] at *')
    L.append('  obtain ⟨hp1, hp2⟩ := hp')
    for j in range(1, g + 1):
        L.append(f'  obtain ⟨b{j}l, b{j}r⟩ := b{j}')
    L.append('  ' + ' <;>\n    '.join(f'rcases e{j} with e{j} | e{j} <;> subst e{j} <;> (try linarith)' for j in range(1, g + 1)))
    L.append('')
    r = len(offs) - 1
    ks = ' '.join(f'k{i}' for i in range(r + 1))
    args = [f'{{{ks} : ℕ}}'] + [f'(hk{i} : k{i} = k{i-1} + 1)' for i in range(1, r + 1)]
    args += ['(n : ℕ) (hn : 105 ≤ n)', '(e0 : nth IsUp k0 = n)'] + [f'(e{i} : nth IsUp k{i} = n + {offs[i]})' for i in range(1, r + 1)]
    L.append(f'/-- No `r + 1 = {r + 1}` consecutive up-integers `≥ 105` sit at offsets `{list(offs)}`. -/')
    L.append(f'theorem {nm} ' + '\n    '.join(args) + ' : False := by')
    L.append('  have hinf := up_infinite')
    L.append('  have hp := phi_bounds')
    L.append('  have M0 : IsUp n := e0 ▸ Nat.nth_mem_of_infinite hinf k0')
    for i in range(1, r + 1):
        L.append(f'  have M{offs[i]} : IsUp (n + {offs[i]}) := e{i} ▸ Nat.nth_mem_of_infinite hinf k{i}')
    for i in range(r):
        for j in range(offs[i] + 1, offs[i + 1]):
            L.append(f'  have N{j} : ¬ IsUp (n + {j}) := not_mem_between\' hinf (k := k{i}) (k\' := k{i+1}) hk{i+1} (by omega) (by omega)')
    L.append(f'  exact core_{nm}\n    ' + '\n    '.join(terms))
    L.append('')
    return '\n'.join(L)

P = ['import Lab.FibWalk.Three.Main', '', '/-!', '# Window lemmas behind `17 ∉ U₇`', '',
     'Generated by `explorer/fib-walk/gen_seven.py`. Each `w*` lemma says that no run of consecutive',
     'up-integers `≥ 105` sits at the given offsets. The proof is the same real-arithmetic method as',
     '`Three/PatternsU.lean`: threshold facts, up-shift facts, and an interval split of `x = δ n`.',
     '-/', '',
     '-- Generated proofs: silence style linters (unused hypotheses, unreachable tactic branches).',
     'set_option linter.unusedVariables false', 'set_option linter.unusedSimpArgs false',
     'set_option linter.unnecessarySeqFocus false', 'set_option linter.unusedTactic false',
     'set_option linter.unreachableTactic false', '',
     'namespace OpenProblemsLab.FibWalk', '', 'open Nat (nth)', 'open Real', 'open scoped goldenRatio Classical', '']
for offs in sorted(lemmas):
    P.append(gen_window(offs))
P.append('end OpenProblemsLab.FibWalk')
open('/home/user/open-problems-lab/Lab/FibWalk/Seven/Patterns.lean', 'w').write('\n'.join(P) + '\n')

# main tree
out = []
def emit(node, d, prefix_sum_vars, ind):
    sp = ' ' * ind
    if node[0] == 'leaf':
        out.append(sp + 'omega'); return
    if node[0] == 'arith':
        out.append(sp + 'omega'); return
    if node[0] == 'cut':
        _, i0, offs = node
        r = len(offs) - 1
        ks = ' '.join(f'(k + {i0 + i})' for i in range(r + 1))
        hks = ' '.join('rfl' for _ in range(r))
        es = ' '.join('rfl' if i == 0 else '(by omega)' for i in range(r + 1))
        kk = lambda i: 'k' if i == 0 else f'k + {i}'
        out.append(sp + f'exact ({name(offs)} (k0 := {kk(i0)}) {" ".join(f"(k{i} := k + {i0 + i})" for i in range(1, r + 1))} '
                   f'{hks} (nth IsUp ({kk(i0)})) (by omega) {es}).elim')
        return
    # internal node at depth d: split s_{d+1}
    out.append(sp + f'interval_cases s{d + 1}')
    for kid in node[1]:
        out.append(sp + '· ' + '')
        start = len(out) - 1
        emit(kid, d + 1, None, ind + 2)
        # merge bullet with first line
        first = out[start + 1].lstrip()
        out[start] = sp + '· ' + first
        del out[start + 1]

emit(tree, 0, None, 2)
M = []
M.append('''import Lab.FibWalk.Seven.Patterns

/-!
# `17 ∈ D₇ \\ U₇`: the 7-step gap sets differ

Aliabadi (arXiv:2609.04473) and Mao–Zhao (arXiv:2608.19886) show `D₄ ≠ U₄`, and Mao–Zhao show
`D₃ = U₃`. Here we prove `D₇ ≠ U₇`:
* `17 ∈ D₇`: the down-integers `9, 10, 12, 13, 15, 18, 23, 26` are consecutive (`9 + 17 = 26`).
* `17 ∉ U₇`: for `u_k < 105` this is a table check. For `u_k ≥ 105` the seven gaps `s_i` lie in
  `[1, 5]`, and a generated case tree rules out every sequence with sum `17`. Each branch is cut either
  by arithmetic or by a window lemma from `Seven/Patterns.lean`.
-/

namespace OpenProblemsLab.FibWalk

open Nat (count nth)
open scoped Classical

/-- A window from a member `N` to a member `N + g`, with exactly `ℓ - 1` members strictly between,
gives `nth p (count p N + ℓ) = N + g`. -/
lemma nth_add_of_window {p : ℕ → Prop} [DecidablePred p] {N g ℓ : ℕ} (hg : 1 ≤ g) (hℓ : 1 ≤ ℓ)
    (hN : p N) (hM : p (N + g)) (hw : count (fun i => p (N + 1 + i)) (g - 1) = ℓ - 1) :
    nth p (count p N + ℓ) = N + g := by
  have h1 : count p (N + 1) = count p N + 1 := by rw [Nat.count_succ, if_pos hN]
  have h2 : count p (N + g) = count p N + ℓ := by
    have := Nat.count_add p (N + 1) (g - 1)
    rw [show N + 1 + (g - 1) = N + g by omega, h1, hw] at this
    omega
  rw [← h2, Nat.nth_count hM]

lemma dt_wit7 : (dt 9 && dt (9 + 17) && (count (fun i => dt (9 + 1 + i) = true) 16 == 6)) = true := by
  decide +kernel

/-- **`17 ∈ D₇`**. -/
theorem seventeen_mem_down : 17 ∈ gapSet IsDown 7 := by
  have h := dt_wit7
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have hN := (isDown_iff_dt (by norm_num)).2 h0
  have hM := (isDown_iff_dt (by norm_num)).2 h1
  have hw : count (fun i => IsDown (9 + 1 + i)) (17 - 1) = 7 - 1 := by
    rw [count_congr_lt (q := fun i => dt (9 + 1 + i) = true)
      (fun i hi => isDown_iff_dt (by omega))]
    exact h2
  refine ⟨count IsDown 9, ?_⟩
  rw [nth_add_of_window (by norm_num) (by norm_num) hN hM hw, Nat.nth_count hN]

lemma ut_small7 : ∀ N < 105, ut N = true →
    ¬ (ut (N + 17) = true ∧ count (fun i => ut (N + 1 + i) = true) 16 = 6) := by
  decide +kernel

/-- **`17 ∉ U₇`**. -/
theorem seventeen_not_mem_up : 17 ∉ gapSet IsUp 7 := by
  rintro ⟨k, hk⟩
  have hinf := up_infinite
  have hmono := Nat.nth_strictMono hinf
  have hT0 : IsUp (nth IsUp k) := Nat.nth_mem_of_infinite hinf k
  have hc0 : count IsUp (nth IsUp k) = k := Nat.count_nth_of_infinite hinf k
  rcases lt_or_ge (nth IsUp k) 105 with hs | hn
  · have h7 : nth IsUp (k + 7) = nth IsUp k + 17 := by
      have := hmono (show k < k + 7 by omega); omega
    have hM : IsUp (nth IsUp k + 17) := h7 ▸ Nat.nth_mem_of_infinite hinf (k + 7)
    have hc7 : count IsUp (nth IsUp k + 17) = k + 7 := h7 ▸ Nat.count_nth_of_infinite hinf (k + 7)
    have hc1 : count IsUp (nth IsUp k + 1) = k + 1 := by rw [Nat.count_succ, hc0, if_pos hT0]
    have hw : count (fun i => IsUp (nth IsUp k + 1 + i)) 16 = 6 := by
      have := Nat.count_add IsUp (nth IsUp k + 1) 16
      rw [show nth IsUp k + 1 + 16 = nth IsUp k + 17 by omega, hc7, hc1] at this
      omega
    rw [count_congr_lt (q := fun i => ut (nth IsUp k + 1 + i) = true)
      (fun i hi => isUp_iff_ut (by omega))] at hw
    exact ut_small7 _ hs ((isUp_iff_ut (by omega)).1 hT0) ⟨(isUp_iff_ut (by omega)).1 hM, hw⟩''')
for i in range(1, 8):
    prev = 'nth IsUp k' if i == 1 else f'nth IsUp (k + {i - 1})'
    cur = f'nth IsUp (k + {i})'
    M.append(f'  have l{i} : {prev} < {cur} := hmono (by omega)')
    M.append(f'  have g{i} : {cur} ≤ {prev} + 5 := gap_le_five_U {"k" if i == 1 else f"(k + {i - 1})"} (by omega)')
    M.append(f'  obtain ⟨s{i}, E{i}⟩ : ∃ s, {cur} = {prev} + s := ⟨_, (Nat.add_sub_cancel\' l{i}.le).symm⟩')
    M.append(f'  have s{i}l : 1 ≤ s{i} := by omega')
    M.append(f'  have s{i}u : s{i} ≤ 5 := by omega')
M.append('\n'.join(out))
M.append('''
/-- **The 7-step gap sets of down- and up-integers differ**: `17 ∈ D₇ \\ U₇`. -/
theorem gapSet_seven_ne : gapSet IsDown 7 ≠ gapSet IsUp 7 := fun h =>
  seventeen_not_mem_up (h ▸ seventeen_mem_down)

end OpenProblemsLab.FibWalk''')
open('/home/user/open-problems-lab/Lab/FibWalk/Seven/Main.lean', 'w').write('\n'.join(M) + '\n')
print('main lines', len(out))
