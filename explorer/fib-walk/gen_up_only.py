"""Usage: gen_up_only.py L GAP W. Generate Lab/FibWalk/UpOnly/L{L}{Patterns,Main}.lean: a Lean proof that
GAP ∈ U_L \\ D_L, with witness window of up-integers starting at W (W + GAP < 310).
First used for L = 8, GAP = 17, W = 25.

For down-integers d_k ≥ 105 the L consecutive gaps s_1..s_L lie in [1,5] (gap_le_five_D).
We search the tree of gap prefixes. A prefix is cut when some window
[d_{k+i}, d_{k+d}] of it is infeasible for the threshold and down-shift constraints. Each cut
uses a lemma `uo{L}w*` about that minimal window. Down shifts f_2..f_7 (the shift -13, from Lab/FibWalk/UpOnly/Shift13.lean:
down-integers >= 105 have parameter t >= 8, so the shift lemma applies with j = 7). Python finds the tree with floating point;
Lean re-proves every cut with exact arithmetic (linarith).
"""
import math, sys
phi = (1 + 5 ** .5) / 2
rho = (2 + phi) / 5; eta = (3 - phi) / 5
fibs = [0, 1, 1, 2, 3, 5, 8, 13, 21]
JS = [2, 3, 4, 5, 6, 7]
th = {j: (phi ** (j - 2) + 1) / (5 ** .5 * phi ** (j - 1)) for j in JS}
sdown = {j: (-1) ** j * fibs[j] for j in JS}
L_STEPS, GAP, WST = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
PFX = f'uo{L_STEPS}w'
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

def feas_U(V):  # here: the down pattern itself
    return feasible_D(list(V))

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
fibl = [0, 1]
while len(fibl) < 30: fibl.append(fibl[-1] + fibl[-2])
UPSET = [False] * 400
for t in range(2, 14):
    for a in range(1, fibl[t] + 1):
        for b in range(a, fibl[t] + 1):
            n = a * fibl[t] + b * fibl[t - 1]
            if n < 400: UPSET[n] = (t % 2 == 1)
assert UPSET[WST] and UPSET[WST + GAP] and sum(UPSET[WST + 1:WST + GAP]) == L_STEPS - 1
name = lambda offs: PFX + '_'.join(map(str, offs))
print(len(lemmas), 'window lemmas')

TH = {'θ₂': th[2], 'θ₃': th[3], 'θ₄': th[4], 'θ₅': th[5], 'θ₆': th[6], 'θ₇': th[7]}
UP = [(1, 'θ₂'), (-2, 'θ₃'), (3, 'θ₄'), (-5, 'θ₅'), (8, 'θ₆'), (-13, 'θ₇')]
def dv(j): return 'x' if j == 0 else f'd{j}'
def pos(j): return 'n' if j == 0 else f'(n + {j})'
def posr(j): return 'n' if j == 0 else f'n + {j}'
LEM = {1: 'shift_plus1', -2: 'shift_minus2', 3: 'shift_plus3', -5: 'shift_minus5', 8: 'shift_plus8', -13: 'shift_minus13'}

def gen_window(offs):
    g = offs[-1]; M = set(offs); nm = name(offs)
    hyps, terms, cons = [], [], []   # cons: (name, 'L'/'U', j, c) meaning d_j > c or d_j < c
    hyps.append('(x ' + ' '.join(dv(j) for j in range(1, g + 1)) + ' : ℝ)')
    hyps.append('(hx0 : 0 ≤ x) (hx1 : x < 1)')
    terms.append(' '.join(f'(δ {pos(j)})' for j in range(g + 1)))
    terms.append('(Int.fract_nonneg _) (Int.fract_lt_one _)')
    for j in range(1, g + 1):
        al = f'({j} * φ - {floor[j]})'
        hyps.append(f'(e{j} : d{j} = x + {al} ∨ d{j} = x + {al} - 1) (b{j} : 0 ≤ d{j} ∧ d{j} < 1)')
        terms.append(f'(by have := delta_add n {j} {floor[j]} (by norm_num; linarith only [hp.1, hp.2]) (by norm_num; linarith only [hp.1, hp.2]); '
                     f'push_cast at this; exact this)')
        terms.append('⟨Int.fract_nonneg _, Int.fract_lt_one _⟩')
    for j in range(g + 1):
        if j in M:
            hyps.append(f'(t{j} : {dv(j)} < ρ)'); terms.append(f'M{j}.delta_lt'); cons.append((f't{j}', 'U', j, rho))
        else:
            hyps.append(f'(t{j} : η < {dv(j)})'); terms.append(f'(isUp_of_not_isDown (by clear * - hn; omega) N{j}).lt_delta'); cons.append((f't{j}', 'L', j, eta))
    for p in offs:
        for s, thn in UP:
            q = p + s
            if 0 <= q <= g and q not in M:
                hyps.append(f'(s{p}_{q} : {dv(p)} < {thn})'); cons.append((f's{p}_{q}', 'U', p, TH[thn]))
                lhs = f'{posr(p)} + {s}' if s > 0 else f'{posr(p)} - {-s}'
                terms.append(f'(sf_{LEM[s].split("_")[1]} (n := n) (p := {p}) (q := {q}) (by clear * - hn; omega) (by clear * - hn; omega) M{p} N{q})')
    L = []
    if g >= 14: L.append('set_option maxHeartbeats 8000000 in')  # long windows: many small linarith calls
    L.append(f'/-- Real-arithmetic core of the down window with members at offsets `{list(offs)}`. -/')
    L.append(f'theorem core_{nm} ' + '\n    '.join(hyps) + ' : False := by')
    L.append('  have hp := phi_bounds')
    L.append('  simp only [ρ, η, θ₂, θ₃, θ₄, θ₅, θ₆, θ₇] at *')
    L.append('  obtain ⟨hp1, hp2⟩ := hp')
    for j in range(1, g + 1):
        L.append(f'  obtain ⟨b{j}l, b{j}r⟩ := b{j}')
    # Split x = δ n at the breakpoints β_j = (⌊jφ⌋ + 1) - jφ. On each piece every d_j is a fixed affine
    # function of x (fixed with small `linarith only` calls). Python then picks the strongest lower and upper
    # bound on x in the piece; `linarith only` with just those two facts closes it.
    alpha = {j: j * phi - floor[j] for j in range(1, g + 1)}
    alpha[0] = 0.0
    bps = sorted(range(1, g + 1), key=lambda j: 1 - alpha[j])
    beta = lambda j: f'(({floor[j] + 1} : ℝ) - {j} * φ)'
    for k in range(g + 1):
        lo = 'hx0' if k == 0 else f'hL{k}'
        lov = 0.0 if k == 0 else 1 - alpha[bps[k - 1]]
        if k < g:
            L.append(f'  rcases lt_or_ge x {beta(bps[k])} with hU{k} | hL{k + 1}')
            hi = f'hU{k}'; hiv = 1 - alpha[bps[k]]
        else:
            hi = 'hx1'; hiv = 1.0
        ind = '  · ' if k < g else '  '
        sub = '    ' if k < g else '  '
        wrapped = set(bps[:k])
        w = {j: (1 if j in wrapped else 0) for j in range(1, g + 1)}; w[0] = 0
        # bounds on x: d_j = x + alpha_j - w_j
        lows = [(lov, lo, None)]; ups = [(hiv, hi, None)]
        for (cn, kind, j, c) in cons:
            v = c - alpha[j] + w[j]
            (lows if kind == 'L' else ups).append((v, cn, j))
        lb = max(lows, key=lambda z: z[0]); ub = min(ups, key=lambda z: z[0])
        assert lb[0] >= ub[0] - 1e-12, (offs, k, lb, ub)
        if abs(lb[0] - ub[0]) < 1e-9: print('touching piece', offs, k, lb, ub)
        deps = sorted({z[2] for z in (lb, ub) if z[2]})
        first = True
        for j in deps:
            al = f'({j} * φ - {floor[j]})'
            rhs = f'x + {al} - 1' if w[j] else f'x + {al}'
            line = (f'have f{j} : d{j} = {rhs} := by rcases e{j} with e | e <;> '
                    f'linarith only [e, b{j}l, b{j}r, {lo}, {hi}, hp1, hp2]')
            L.append((ind if first else sub) + line); first = False
        fin = 'linarith only [' + ', '.join([lb[1], ub[1]] + [f'f{j}' for j in deps] + ['hp1', 'hp2']) + ']'
        L.append((ind if first else sub) + fin)
    L.append('')
    r = len(offs) - 1
    ks = ' '.join(f'k{i}' for i in range(r + 1))
    args = [f'{{{ks} : ℕ}}'] + [f'(hk{i} : k{i} = k{i-1} + 1)' for i in range(1, r + 1)]
    args += ['(n : ℕ) (hn : 105 ≤ n)', '(e0 : nth IsDown k0 = n)'] + [f'(e{i} : nth IsDown k{i} = n + {offs[i]})' for i in range(1, r + 1)]
    if g >= 14: L.append('set_option maxHeartbeats 8000000 in')
    L.append(f'/-- No `r + 1 = {r + 1}` consecutive down-integers `≥ 105` sit at offsets `{list(offs)}`. -/')
    L.append(f'theorem {nm} ' + '\n    '.join(args) + ' : False := by')
    L.append('  have hinf := down_infinite')
    L.append('  have hp := phi_bounds')
    L.append('  have M0 : IsDown n := e0 ▸ Nat.nth_mem_of_infinite hinf k0')
    for i in range(1, r + 1):
        L.append(f'  have M{offs[i]} : IsDown (n + {offs[i]}) := e{i} ▸ Nat.nth_mem_of_infinite hinf k{i}')
    for i in range(r):
        for j in range(offs[i] + 1, offs[i + 1]):
            L.append(f'  have N{j} : ¬ IsDown (n + {j}) := not_mem_between\' hinf (k := k{i}) (k\' := k{i+1}) hk{i+1} (by omega) (by omega)')
    # Elaborate each argument as its own goal (one big application term used ~6 GB on long windows).
    rest = ['Int.fract_nonneg _', 'Int.fract_lt_one _'] + terms[2:]
    L.append(f'  refine core_{nm}\n    {terms[0]}' + ' ?_' * len(rest))
    for t in rest:
        L.append(f'  · exact {t}')
    L.append('')
    return '\n'.join(L)

P = [f'import {sys.argv[4] if len(sys.argv) > 4 else "Lab.FibWalk.UpOnly.Shift13"}', '', '/-!', f'# Window lemmas behind `{GAP} ∉ D_{L_STEPS}`', '',
     f'Generated by `explorer/fib-walk/gen_up_only.py {L_STEPS} {GAP} {WST}`. Each `{PFX}*` lemma says that no run of',
     'consecutive down-integers `≥ 105` sits at the given offsets. The proof is the same real-arithmetic method as',
     '`Three/PatternsD.lean`: threshold facts, down-shift facts (now including `-13`), and an interval split of `x = δ n`.',
     '-/', '',
     '-- Generated proofs: silence style linters (unused hypotheses, unreachable tactic branches).',
     'set_option linter.unusedVariables false', 'set_option linter.unusedSimpArgs false',
     'set_option linter.unnecessarySeqFocus false', 'set_option linter.unusedTactic false',
     'set_option linter.unreachableTactic false', '',
     'namespace OpenProblemsLab.FibWalk', '', 'open Nat (nth)', 'open Real', 'open scoped goldenRatio Classical', '']
# Split the window lemmas into a chain of files (about CHUNK windows of total length each) so that no single
# Lean process gets too big; file i imports file i-1.
import glob, os
for f in glob.glob(f'/home/user/open-problems-lab/Lab/FibWalk/UpOnly/L{L_STEPS}Patterns*.lean'): os.remove(f)
CHUNK = 160
chunks, cur, size = [], [], 0
for offs in sorted(lemmas):
    cur.append(offs); size += offs[-1]
    if size >= CHUNK: chunks.append(cur); cur, size = [], 0
if cur: chunks.append(cur)
for ci, ch in enumerate(chunks):
    PP = list(P)
    if ci > 0: PP[0] = f'import Lab.FibWalk.UpOnly.L{L_STEPS}Patterns{ci - 1}'
    PP[3] = PP[3] + f' (part {ci + 1} of {len(chunks)})'
    for offs in ch: PP.append(gen_window(offs))
    PP.append('end OpenProblemsLab.FibWalk')
    open(f'/home/user/open-problems-lab/Lab/FibWalk/UpOnly/L{L_STEPS}Patterns{ci}.lean', 'w').write('\n'.join(PP) + '\n')
NCH = len(chunks)

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
                   f'{hks} (nth IsDown ({kk(i0)})) (by omega) {es}).elim')
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
import math as _m
fl = '`' + ', '.join(str(n) for n in range(WST, WST + GAP + 1) if UPSET[n]) + '`'
G, LL, W = GAP, L_STEPS, WST
M.append(f"""import Lab.FibWalk.UpOnly.L{LL}Patterns{NCH - 1}

/-!
# `{G} ∈ U_{LL} \\ D_{LL}`: the {LL}-step gap sets differ

Generated by `explorer/fib-walk/gen_up_only.py {LL} {G} {W}`.
* `{G} ∈ U_{LL}`: the up-integers {fl} are consecutive (`{W} + {G} = {W + G}`).
* `{G} ∉ D_{LL}`: for `d_k < 105` this is a table check. For `d_k ≥ 105` the {LL} gaps `s_i` lie in
  `[1, 5]`, and a generated case tree rules out every sequence with sum `{G}`. Each branch is cut either
  by arithmetic or by a window lemma from `UpOnly/L{LL}Patterns*.lean`.
-/

namespace OpenProblemsLab.FibWalk

open Nat (count nth)
open scoped Classical

lemma ut_wit_uo{LL} : (ut {W} && ut ({W} + {G}) && (count (fun i => ut ({W} + 1 + i) = true) {G - 1} == {LL - 1})) = true := by
  decide +kernel

/-- **`{G} ∈ U_{LL}`**. -/
theorem up_only_mem_up{LL} : {G} ∈ gapSet IsUp {LL} := by
  have h := ut_wit_uo{LL}
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have hN := (isUp_iff_ut (by norm_num)).2 h0
  have hM := (isUp_iff_ut (by norm_num)).2 h1
  have hw : count (fun i => IsUp ({W} + 1 + i)) ({G} - 1) = {LL} - 1 := by
    rw [count_congr_lt (q := fun i => ut ({W} + 1 + i) = true)
      (fun i hi => isUp_iff_ut (by omega))]
    exact h2
  refine ⟨count IsUp {W}, ?_⟩
  rw [nth_add_of_window (by norm_num) (by norm_num) hN hM hw, Nat.nth_count hN]

lemma dt_small_uo{LL} : ∀ N < 105, dt N = true →
    ¬ (dt (N + {G}) = true ∧ count (fun i => dt (N + 1 + i) = true) {G - 1} = {LL - 1}) := by
  decide +kernel

set_option maxHeartbeats 0 in
/-- **`{G} ∉ D_{LL}`**. -/
theorem up_only_not_mem_down{LL} : {G} ∉ gapSet IsDown {LL} := by
  rintro ⟨k, hk⟩
  have hinf := down_infinite
  have hmono := Nat.nth_strictMono hinf
  have hT0 : IsDown (nth IsDown k) := Nat.nth_mem_of_infinite hinf k
  have hc0 : count IsDown (nth IsDown k) = k := Nat.count_nth_of_infinite hinf k
  rcases lt_or_ge (nth IsDown k) 105 with hs | hn
  · have hL : nth IsDown (k + {LL}) = nth IsDown k + {G} := by
      have := hmono (show k < k + {LL} by omega); omega
    have hM : IsDown (nth IsDown k + {G}) := hL ▸ Nat.nth_mem_of_infinite hinf (k + {LL})
    have hcL : count IsDown (nth IsDown k + {G}) = k + {LL} := hL ▸ Nat.count_nth_of_infinite hinf (k + {LL})
    have hc1 : count IsDown (nth IsDown k + 1) = k + 1 := by rw [Nat.count_succ, hc0, if_pos hT0]
    have hw : count (fun i => IsDown (nth IsDown k + 1 + i)) {G - 1} = {LL - 1} := by
      have := Nat.count_add IsDown (nth IsDown k + 1) {G - 1}
      rw [show nth IsDown k + 1 + {G - 1} = nth IsDown k + {G} by omega, hcL, hc1] at this
      omega
    rw [count_congr_lt (q := fun i => dt (nth IsDown k + 1 + i) = true)
      (fun i hi => isDown_iff_dt (by omega))] at hw
    exact dt_small_uo{LL} _ hs ((isDown_iff_dt (by omega)).1 hT0) ⟨(isDown_iff_dt (by omega)).1 hM, hw⟩""")
for i in range(1, LL + 1):
    prev = 'nth IsDown k' if i == 1 else f'nth IsDown (k + {i - 1})'
    cur = f'nth IsDown (k + {i})'
    M.append(f'  have l{i} : {prev} < {cur} := hmono (by omega)')
    M.append(f'  have g{i} : {cur} ≤ {prev} + 5 := gap_le_five_D {"k" if i == 1 else f"(k + {i - 1})"} (by omega)')
    M.append(f'  obtain ⟨s{i}, E{i}⟩ : ∃ s, {cur} = {prev} + s := ⟨_, (Nat.add_sub_cancel\' l{i}.le).symm⟩')
    M.append(f'  have s{i}l : 1 ≤ s{i} := by omega')
    M.append(f'  have s{i}u : s{i} ≤ 5 := by omega')
M.append('\n'.join(out))
M.append(f"""
/-- **The {LL}-step gap sets of down- and up-integers differ**: `{G} ∈ U_{LL} \\ D_{LL}`. -/
theorem gapSet_ne_uo{LL} : gapSet IsDown {LL} ≠ gapSet IsUp {LL} := fun h =>
  up_only_not_mem_down{LL} (h ▸ up_only_mem_up{LL})

end OpenProblemsLab.FibWalk""")
open(f'/home/user/open-problems-lab/Lab/FibWalk/UpOnly/L{LL}Main.lean', 'w').write('\n'.join(M) + '\n')
print('main lines', len(out))
