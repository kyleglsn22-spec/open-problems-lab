import os
HERE = os.path.dirname(os.path.abspath(__file__))
import json, itertools
from math import comb

D = json.load(open(os.path.join(HERE, 'g29_lean_data.json')))
E, C = D['E'], D['C']
cyc = json.load(open(os.path.join(HERE, '..', 'g29_cycles.json')))
QI = [1, 2, 3, 4, 7, 8, 9, 10, 16, 17, 18, 19]
RI = [0, 5, 6, 11, 12, 13, 14, 15, 20, 21, 22, 23, 24, 25, 26]
LIMIT = 500

out = []
w = out.append


def fin(xs):
    return '({' + ', '.join(map(str, xs)) + '} : Finset (Fin 29))' if xs else '(∅ : Finset (Fin 29))'


def ins(pre, B='B'):
    s = B
    for a in reversed(pre):
        s = f'insert {a} ({s})'
    return s


counter = [0]


def emit(base, cs, Xs, elems, k, pre):
    counter[0] += 1
    nm = f'{base}_{counter[0]}'
    stmt = f'∀ B ∈ {fin(elems)}.powersetCard {k}, hits {cs} ({Xs} ∪ {ins(pre)}) = true'
    if k == 0 or k > len(elems) or comb(len(elems), k) <= LIMIT:
        w(f'lemma {nm} : {stmt} := by decide +kernel\n\n')
        return nm
    a, s = elems[0], elems[1:]
    h1 = emit(base, cs, Xs, s, k, pre)
    h2 = emit(base, cs, Xs, s, k - 1, pre + [a])
    w(f'lemma {nm} : {stmt} :=\n  forall_powersetCard_insert (P := fun B => hits {cs} ({Xs} ∪ {ins(pre)}) = true)\n'
      f'    (by decide) {h1} {h2}\n\n')
    return nm


names = {'': '0', '27': 'x', '28': 'y', '27,28': 'xy'}
Xl = {'': '([] : List (Fin 29))', '27': '[27]', '28': '[28]', '27,28': '[27, 28]'}
w('@@FILE Hits@@')
w('/-! ## Hitting facts: each large vertex set on one side contains a listed cycle -/\n\n')
for side in ('Q', 'R'):
    for X in ('', '27', '28', '27,28'):
        k = cyc[f'{side}|{X}'][0]
        cs = f'cyc{side}{names[X]}'
        w(f'lemma hit{side}{names[X]} : ∀ B : Finset (Fin 29), B ⊆ {side}L.toFinset → B.card = {k} →\n'
          f'    ∃ l ∈ {cs}, ∀ v ∈ l, v ∈ {Xl[X]} ∨ v ∈ B :=\n'
          f'  hits_of_allSub {cs} m{cs} m{cs}_eq {side}L {k} {Xl[X]} (by decide +kernel)\n\n')
w('@@FILE Drawing@@')
w('''/-! ## The forest bound -/

lemma mem_parts : ∀ v : Fin 29, (v ∈ QI ∧ v ∉ RI ∧ v ≠ 27 ∧ v ≠ 28) ∨ (v ∉ QI ∧ v ∈ RI ∧ v ≠ 27 ∧ v ≠ 28) ∨
    (v ∉ QI ∧ v ∉ RI ∧ (v = 27 ∨ v = 28)) := by decide +kernel

lemma card_split (S : Finset (Fin 29)) :
    S.card = (S ∩ QI).card + (S ∩ RI).card + (S ∩ {27, 28}).card := by
  have h1 := Finset.card_inter_add_card_sdiff S QI
  have h2 := Finset.card_inter_add_card_sdiff (S \\ QI) RI
  have e1 : (S \\ QI) ∩ RI = S ∩ RI := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    rcases mem_parts v with h | h | h <;> tauto
  have e2 : (S \\ QI) \\ RI = S ∩ {27, 28} := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    rcases mem_parts v with h | h | h <;> tauto
  rw [e1, e2] at h2
  omega

/-- Every induced forest of `G₂₉` has at most 14 vertices. -/
theorem card_le_of_isAcyclic (S : Finset (Fin 29))
    (hS : (G.induce (S : Set (Fin 29))).IsAcyclic) : S.card ≤ 14 := by
  rw [card_split S]
  by_cases hx : (27 : Fin 29) ∈ S <;> by_cases hy : (28 : Fin 29) ∈ S
  · have hP : S ∩ {27, 28} = {27, 28} := by
      ext v; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro (rfl | rfl) <;> simp_all
    have hX : ∀ v ∈ ([27, 28] : List (Fin 29)), v ∈ S := by
      intro v hv
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl <;> assumption
    have hq := card_inter_lt S QI QL [27, 28] cycQxy _ cycQxy_valid QL_eq hX hitQxy hS
    have hr := card_inter_lt S RI RL [27, 28] cycRxy _ cycRxy_valid RL_eq hX hitRxy hS
    rw [hP]; simp only [Finset.card_insert_of_notMem (by decide : (27 : Fin 29) ∉ ({28} : Finset (Fin 29))),
      Finset.card_singleton]
    omega
  · have hP : S ∩ {27, 28} = {27} := by
      ext v; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, rfl | rfl⟩
        · rfl
        · exact absurd h1 hy
      · rintro rfl; exact ⟨hx, Or.inl rfl⟩
    have hX : ∀ v ∈ ([27] : List (Fin 29)), v ∈ S := by
      intro v hv; rw [List.mem_singleton] at hv; rw [hv]; exact hx
    have hq := card_inter_lt S QI QL [27] cycQx _ cycQx_valid QL_eq hX hitQx hS
    have hr := card_inter_lt S RI RL [27] cycRx _ cycRx_valid RL_eq hX hitRx hS
    rw [hP, Finset.card_singleton]
    omega
  · have hP : S ∩ {27, 28} = {28} := by
      ext v; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, rfl | rfl⟩
        · exact absurd h1 hx
        · rfl
      · rintro rfl; exact ⟨hy, Or.inr rfl⟩
    have hX : ∀ v ∈ ([28] : List (Fin 29)), v ∈ S := by
      intro v hv; rw [List.mem_singleton] at hv; rw [hv]; exact hy
    have hq := card_inter_lt S QI QL [28] cycQy _ cycQy_valid QL_eq hX hitQy hS
    have hr := card_inter_lt S RI RL [28] cycRy _ cycRy_valid RL_eq hX hitRy hS
    rw [hP, Finset.card_singleton]
    omega
  · have hP : S ∩ {27, 28} = ∅ := by
      ext v; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false, not_and]
      rintro h (rfl | rfl)
      · exact hx h
      · exact hy h
    have hX : ∀ v ∈ ([] : List (Fin 29)), v ∈ S := by simp
    have hq := card_inter_lt S QI QL [] cycQ0 _ cycQ0_valid QL_eq hX hitQ0 hS
    have hr := card_inter_lt S RI RL [] cycR0 _ cycR0_valid RL_eq hX hitR0 hS
    rw [hP, Finset.card_empty]
    omega

@@FILE Drawing2@@/-! ## The straight-line drawing -/

/-- Integer coordinates (a rounded Tutte embedding of a triangulation containing `G₂₉`). -/
def P : Fin 29 → ℤ × ℤ :=
''')
w('  ![' + ', '.join(f'({x}, {y})' for x, y in C) + ']\n\n')
w('''lemma P_inj : ∀ i j : Fin 29, P i = P j → i = j := by decide +kernel

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

@@GOOD@@
lemma allGood : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f → goodPair e.1 e.2 f.1 f.2 = true := by
  intro e he
  rw [edges_split, List.mem_append, List.mem_append, List.mem_append] at he
  rcases he with ((he | he) | he) | he
  · exact allGood0 e he
  · exact allGood1 e he
  · exact allGood2 e he
  · exact allGood3 e he

/-- The real point of an integer point. -/
def toR (q : ℤ × ℤ) : ℝ × ℝ := ((q.1 : ℝ), (q.2 : ℝ))

lemma toR_injective : Function.Injective toR := by
  intro a b h
  simp only [toR, Prod.mk.injEq, Int.cast_inj] at h
  exact Prod.ext h.1 h.2

/-- Real orientation. -/
def orR (a b z : ℝ × ℝ) : ℝ := (b.1 - a.1) * (z.2 - a.2) - (b.2 - a.2) * (z.1 - a.1)

lemma orR_toR (a b c : ℤ × ℤ) : orR (toR a) (toR b) (toR c) = (orient a b c : ℝ) := by
  simp only [orR, toR, orient]; push_cast; ring

lemma orR_of_mem_segment_left {a b z : ℝ × ℝ} (hz : z ∈ segment ℝ a b) : orR a b z = 0 := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  simp only [orR, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have : s = 1 - t := by linarith
  subst this; ring

lemma orR_of_mem_segment {a b c d z : ℝ × ℝ} (hz : z ∈ segment ℝ c d) :
    ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t = 1 ∧ orR a b z = s * orR a b c + t * orR a b d := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  refine ⟨s, t, hs, ht, hst, ?_⟩
  simp only [orR, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have : s = 1 - t := by linarith
  subst this; ring

lemma segment_inter_eq_empty {a b c d : ℝ × ℝ} (h : 0 < orR a b c * orR a b d) :
    segment ℝ a b ∩ segment ℝ c d = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hab hcd
  have h0 := orR_of_mem_segment_left hab
  obtain ⟨s, t, hs, ht, hst, he⟩ := orR_of_mem_segment (a := a) (b := b) hcd
  rw [h0] at he
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · have h1 : s * min (orR a b c) (orR a b d) ≤ s * orR a b c :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hs
    have h2 : t * min (orR a b c) (orR a b d) ≤ t * orR a b d :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) ht
    have hm : 0 < min (orR a b c) (orR a b d) := lt_min hc hd
    nlinarith
  · have h1 : s * orR a b c ≤ s * max (orR a b c) (orR a b d) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hs
    have h2 : t * orR a b d ≤ t * max (orR a b c) (orR a b d) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) ht
    have hm : max (orR a b c) (orR a b d) < 0 := max_lt hc hd
    nlinarith

lemma segment_inter_subset {v x y : ℝ × ℝ} (h : orR v x y ≠ 0) :
    segment ℝ v x ∩ segment ℝ v y ⊆ {v} := by
  rintro z ⟨⟨s, t, hs, ht, hst, rfl⟩, ⟨s', t', hs', ht', hst', hz⟩⟩
  have e1 := congrArg Prod.fst hz
  have e2 := congrArg Prod.snd hz
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2
  have hs1 : s = 1 - t := by linarith
  have hs2 : s' = 1 - t' := by linarith
  subst hs1 hs2
  have key : t' * orR v x y = 0 := by
    simp only [orR]
    linear_combination (x.1 - v.1) * e2 - (x.2 - v.2) * e1
  have ht0 : t' = 0 := by
    rcases mul_eq_zero.1 key with h' | h'
    · exact h'
    · exact absurd h' h
  subst ht0
  rw [Set.mem_singleton_iff, ← hz]
  simp

/-- The drawing map. -/
def pt (i : Fin 29) : ℝ × ℝ := toR (P i)

lemma orient_cast_ne {a b c : Fin 29} (h : orient (P a) (P b) (P c) ≠ 0) :
    orR (pt a) (pt b) (pt c) ≠ 0 := by
  simp only [pt, orR_toR]; exact_mod_cast h

lemma orient_cast_pos {a b c d : Fin 29}
    (h : 0 < orient (P a) (P b) (P c) * orient (P a) (P b) (P d)) :
    0 < orR (pt a) (pt b) (pt c) * orR (pt a) (pt b) (pt d) := by
  simp only [pt, orR_toR]; exact_mod_cast h

lemma good_segments (a b c d : Fin 29) (h : goodPair a b c d = true) :
    segment ℝ (pt a) (pt b) ∩ segment ℝ (pt c) (pt d) ⊆ pt '' ({a, b} ∩ {c, d} : Set (Fin 29)) := by
  unfold goodPair at h
  split_ifs at h with h1 h2 h3 h4
  · subst h1
    have := segment_inter_subset (orient_cast_ne (of_decide_eq_true h))
    intro z hz
    rw [Set.mem_singleton_iff.1 (this hz)]
    exact ⟨a, by simp, rfl⟩
  · subst h2
    have := segment_inter_subset (orient_cast_ne (of_decide_eq_true h))
    intro z hz
    rw [segment_symm ℝ (pt c)] at hz
    rw [Set.mem_singleton_iff.1 (this hz)]
    exact ⟨a, by simp, rfl⟩
  · subst h3
    have := segment_inter_subset (orient_cast_ne (of_decide_eq_true h))
    intro z hz
    rw [segment_symm ℝ (pt a)] at hz
    rw [Set.mem_singleton_iff.1 (this hz)]
    exact ⟨b, by simp, rfl⟩
  · subst h4
    have := segment_inter_subset (orient_cast_ne (of_decide_eq_true h))
    intro z hz
    rw [segment_symm ℝ (pt a), segment_symm ℝ (pt c)] at hz
    rw [Set.mem_singleton_iff.1 (this hz)]
    exact ⟨b, by simp, rfl⟩
  · rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    rcases h with h | h
    · rw [segment_inter_eq_empty (orient_cast_pos h)]; exact Set.empty_subset _
    · rw [Set.inter_comm, segment_inter_eq_empty (orient_cast_pos h)]; exact Set.empty_subset _

/-- `G₂₉` has a straight-line planar drawing. -/
theorem straightLinePlanar_G : StraightLinePlanar G := by
  refine ⟨pt, fun i j h => P_inj i j (toR_injective h), ?_⟩
  intro a b c d hab hcd hne
  rw [adj_iff] at hab hcd
  have key : ∀ a b c d : Fin 29, (a, b) ∈ edges → (c, d) ∈ edges → s(a, b) ≠ s(c, d) →
      segment ℝ (pt a) (pt b) ∩ segment ℝ (pt c) (pt d) ⊆
        pt '' ({a, b} ∩ {c, d} : Set (Fin 29)) := by
    intro a b c d h1 h2 hne
    refine good_segments a b c d (allGood _ h1 _ h2 ?_)
    rintro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hne rfl
  rcases hab with hab | hab <;> rcases hcd with hcd | hcd
  · exact key a b c d hab hcd hne
  · rw [segment_symm ℝ (pt c), Set.pair_comm c d]
    exact key a b d c hab hcd (by rwa [Sym2.eq_swap (a := d)])
  · rw [segment_symm ℝ (pt a), Set.pair_comm a b]
    exact key b a c d hab hcd (by rwa [Sym2.eq_swap (a := b)])
  · rw [segment_symm ℝ (pt a), Set.pair_comm a b, segment_symm ℝ (pt c), Set.pair_comm c d]
    exact key b a d c hab hcd (by rwa [Sym2.eq_swap (a := b), Sym2.eq_swap (a := d)])

@@FILE Counterexample@@/-! ## Main result -/

/-- The Albertson–Berman conjecture, for straight-line planar graphs: every such graph on `n`
vertices has an induced forest on at least `n / 2` vertices. -/
def AlbertsonBermanConjecture : Prop :=
  ∀ (n : ℕ) (H : SimpleGraph (Fin n)), StraightLinePlanar H →
    ∃ S : Finset (Fin n), (H.induce (S : Set (Fin n))).IsAcyclic ∧ n ≤ 2 * S.card

/-- `G₂₉` is a counterexample: 29 vertices, straight-line planar, every induced forest has at most
14 vertices. Since a straight-line drawing is a planar drawing, the conjecture fails for planar
graphs in any usual sense. -/
theorem not_albertsonBermanConjecture : ¬ AlbertsonBermanConjecture := by
  intro h
  obtain ⟨S, hS, hcard⟩ := h 29 G straightLinePlanar_G
  have := card_le_of_isAcyclic S hS
  omega

end OpenProblemsLab.AlbertsonBerman
''')
part1 = open(os.path.join(HERE, 'AB_part1.lean')).read()
import re, os
text = ''.join(out)
Es = [E[i*20:(i+1)*20] for i in range(4)]
good = ''.join(f'def edges{i} : List (Fin 29 × Fin 29) :=\n  [' + ', '.join(f'({a}, {b})' for a, b in Es[i]) + ']\n\n' for i in range(4))
good += 'lemma edges_split : edges = edges0 ++ edges1 ++ edges2 ++ edges3 := by decide +kernel\n\n'
for i in range(4):
    good += f'@@FILE Good{i}@@lemma allGood{i} : ∀ e ∈ edges{i}, ∀ f ∈ edges, e ≠ f → goodPair e.1 e.2 f.1 f.2 = true := by\n  decide +kernel\n\n'
good += '@@FILE Drawing3@@'
text = text.replace('@@GOOD@@', good)
chunks = re.split(r'@@FILE (\w+)@@', text)
part1 = part1.rstrip() + '\n\nend OpenProblemsLab.AlbertsonBerman\n'
files = [('Basic', part1)]
for i in range(1, len(chunks), 2):
    files.append((chunks[i], chunks[i + 1]))
# rename: Drawing (forest bound) -> Forest, Drawing2 -> Drawing
ren = {'Drawing': 'Forest', 'Drawing2': 'DrawingData', 'Drawing3': 'Drawing'}
files = [(ren.get(a, a), b) for a, b in files]
d = os.path.join(HERE, '..', '..', '..', 'Lab', 'AlbertsonBerman') + '/'
for f in os.listdir(d): os.remove(d + f)
prev = None
for name, body in files:
    if name == 'Basic':
        src = body
    else:
        body = body.replace('end OpenProblemsLab.AlbertsonBerman\n', '')
        src = (f'import Lab.AlbertsonBerman.{prev}\n\n/-! Part of claim AB-1, see `Lab/AlbertsonBerman/Basic.lean`. -/\n\n'
               f'namespace OpenProblemsLab.AlbertsonBerman\n\nopen SimpleGraph\n\n{body.strip()}\n\nend OpenProblemsLab.AlbertsonBerman\n')
    open(d + name + '.lean', 'w').write(src)
    prev = name
print([n for n, _ in files])
print('lemmas', counter[0])
