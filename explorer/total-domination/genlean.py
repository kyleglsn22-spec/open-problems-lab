"""Generate the Lean files of claim GHT-1 from B.json (build.py) and P.json (draw.py)."""
import json, sys, os
D = sys.argv[1] if len(sys.argv) > 1 else '.'
OUT = sys.argv[2] if len(sys.argv) > 2 else 'Lab/TotalDomination'
d = json.load(open(os.path.join(D, 'B.json'))); P = json.load(open(os.path.join(D, 'P.json')))
E = [tuple(e) for e in d['edges']]; E14 = [tuple(sorted(e)) for e in d['E14']]
iota = {int(k): v for k, v in d['iota'].items()}
names = d['names']
adj = {v: set() for v in range(36)}
for u, v in E: adj[u].add(v); adj[v].add(u)
adj14 = {v: set() for v in range(14)}
for u, v in E14: adj14[u].add(v); adj14[v].add(u)
# checks
for i in (1, 2, 3):
    io = iota[i]
    assert len(set(io)) == 14
    for u, v in E14: assert io[v] in adj[io[u]]
    for j in (3, 5, 9): assert adj[io[j]] == {io[n] for n in adj14[j]}
a, b, z2 = names.index('a'), names.index('b'), names.index('z2')
assert (iota[1][0], iota[1][2]) == (a, z2) and (iota[2][0], iota[2][2]) == (b, z2) and (iota[3][0], iota[3][2]) == (a, b)
HDR = "/-! Part of claim GHT-1, see `Lab/TotalDomination/Basic.lean`. -/\n\nnamespace OpenProblemsLab.TotalDomination\n\nopen SimpleGraph\n\n"
END = "\nend OpenProblemsLab.TotalDomination\n"
def w(name, imp, body):
    open(os.path.join(OUT, name + '.lean'), 'w').write(f"import {imp}\n\n" + HDR + body + END)
# ---- nested lemma on G14
order = [0, 2]
while len(order) < 14:
    order.append(max((v for v in range(14) if v not in order), key=lambda v: (len(adj14[v] & set(order)), -v)))
lines = []; hyps = []  # hyps: list of (kind, data) in order
introduced = []
pending_nd = [3, 5, 9]
for v in order:
    lines.append(f"∀ x{v} : Fin 4,")
    hyps.append(('var', v))
    introduced.append(v)
    for u in introduced[:-1]:
        if u in adj14[v]:
            lines.append(f"x{u} ≠ x{v} →"); hyps.append(('ne', u, v))
    if v == 2:
        lines.append("x2 = partner x0 →"); hyps.append(('partner',))
    for j in list(pending_nd):
        if j in introduced and adj14[j] <= set(introduced):
            nb = sorted(adj14[j])
            lines.append("(" + " ∨ ".join(f"x{n} = partner x{j}" for n in nb) + ") →")
            hyps.append(('nd', j, nb)); pending_nd.remove(j)
assert not pending_nd
lines.append("False")
lem = "set_option synthInstance.maxSize 4096 in\nset_option synthInstance.maxHeartbeats 400000 in\n/-- Lemma 3.1 of Kwon–Park–Sano in nested form (the order of the variables lets the kernel prune\nimproper partial colourings early): in a proper colouring of `G₁₄` in which `v₃`, `v₅`, `v₉` are\nnot defective, `v₀v₂` is not a partner edge. -/\ntheorem lemma31 :\n    " + "\n    ".join(lines) + " := by\n  decide +kernel\n"
w('Lemma', 'Lab.TotalDomination.Basic', lem)
# ---- applying the lemma to the three copies
body = ""
for i in (1, 2, 3):
    io = iota[i]
    for j in (3, 5, 9):
        nb = sorted(adj14[j])
        body += f"lemma nbr_{i}_{j} : ∀ u : Fin 36, adjB {io[j]} u = true → " + " ∨ ".join(f"u = {io[n]}" for n in nb) + " := by\n  decide +kernel\n\n"
body += """/-- Lemma 3.1 transported to the copy `H^(i)` of `G₁₄` inside `B`. -/
theorem no_partner_coloring_B (c : Fin 36 → Fin 4) (hp : ∀ u v, adjB u v = true → c u ≠ c v)
    (hnd : ∀ v, ∃ u, adjB v u = true ∧ c u = partner (c v)) : False := by
"""
for i in (1, 2, 3):
    io = iota[i]
    for j in (3, 5, 9):
        nb = sorted(adj14[j])
        disj = " ∨ ".join(f"c {io[n]} = partner (c {io[j]})" for n in nb)
        k = len(nb)
        ex = []
        for t in range(k):
            s = "h"
            if t < k - 1: s = "Or.inl " + s if t == 0 else s
            # build Or.inr^t (Or.inl h) or Or.inr^(k-1) h
            term = "h" if t == k - 1 else "(Or.inl h)"
            for _ in range(t): term = f"(Or.inr {term})"
            ex.append(term)
        body += f"  have n{i}_{j} : {disj} := by\n    obtain ⟨u, hu, h⟩ := hnd {io[j]}\n    rcases nbr_{i}_{j} u hu with " + " | ".join(["rfl"] * k) + "\n    exacts [" + ", ".join(ex) + "]\n"
    args = []
    hargs = []
    for h in hyps:
        if h[0] == 'var': hargs.append(f"(c {io[h[1]]})")
        elif h[0] == 'ne': hargs.append(f"(hp {io[h[1]]} {io[h[2]]} (by decide +kernel))")
        elif h[0] == 'partner': hargs.append("hP")
        else: hargs.append(f"n{i}_{h[1]}")
    body += f"  have e{i} : c {io[2]} ≠ partner (c {io[0]}) := fun hP =>\n    lemma31 " + " ".join(args) + "\n      " + " ".join(hargs) + "\n"
body += f"""  exact triangle (c {a}) (c {b}) (c {z2}) (hp {a} {b} (by decide +kernel)) (hp {a} {z2} (by decide +kernel))
    (hp {b} {z2} (by decide +kernel)) e1 e2 e3
"""
w('NoPartner', 'Lab.TotalDomination.Lemma', body)
# ---- drawing data
Pl = [tuple(P[str(v)]) for v in range(36)]
chunks = [E[k:k + 17] for k in range(0, len(E), 17)]
dd = "/-- Integer coordinates of a straight-line drawing of `B` (a rounded Tutte embedding with outer face\n`a b z₁`), indexed by vertex number. -/\ndef Pl : List (ℤ × ℤ) :=\n  [" + ", ".join(f"({x}, {y})" for x, y in Pl) + "]\n\n"
dd += "/-- The coordinates of vertex `i`. -/\ndef P (i : ℕ) : ℤ × ℤ := Pl.getD i (0, 0)\n\n"
dd += "lemma P_inj : ∀ i j : Fin 36, P i.val = P j.val → i = j := by decide +kernel\n\n"
dd += """/-- Two edges `ab`, `cd` (vertex numbers) are drawn correctly: if they share an endpoint the other
two ends are not collinear with it; otherwise one segment lies strictly on one side of the other's
line. -/
def goodPair (a b c d : ℕ) : Bool :=
  if a = c then AlbertsonBerman.orient (P a) (P b) (P d) ≠ 0
  else if a = d then AlbertsonBerman.orient (P a) (P b) (P c) ≠ 0
  else if b = c then AlbertsonBerman.orient (P b) (P a) (P d) ≠ 0
  else if b = d then AlbertsonBerman.orient (P b) (P a) (P c) ≠ 0
  else 0 < AlbertsonBerman.orient (P a) (P b) (P c) * AlbertsonBerman.orient (P a) (P b) (P d) ||
    0 < AlbertsonBerman.orient (P c) (P d) (P a) * AlbertsonBerman.orient (P c) (P d) (P b)

"""
for k, ch in enumerate(chunks):
    dd += f"def edges{k} : List (ℕ × ℕ) :=\n  [" + ", ".join(f"({u}, {v})" for u, v in ch) + "]\n\n"
dd += "lemma edges_split : edges = " + " ++ ".join(f"edges{k}" for k in range(len(chunks))) + " := by decide +kernel\n"
w('DrawData', 'Lab.TotalDomination.NoPartner', dd)
prev = 'Lab.TotalDomination.DrawData'
for k in range(len(chunks)):
    w(f'Good{k}', prev, f"lemma allGood{k} : ∀ e ∈ edges{k}, ∀ f ∈ edges, e ≠ f → goodPair e.1 e.2 f.1 f.2 = true := by\n  decide +kernel\n")
    prev = f'Lab.TotalDomination.Good{k}'
print("chunks", len(chunks), "order", order, "last import", prev)
print("EDGES", "[" + ", ".join(f"({u}, {v})" for u, v in E) + "]")
print("E14", "[" + ", ".join(f"({u}, {v})" for u, v in E14) + "]")
print("a b z2", a, b, z2, "z1", names.index('1_7'))
