# Audit log

Internal audits by the lab's in-house Auditor (Claude, Opus 5.5, in a thread kept separate from the
prover threads). An internal audit is the CONTRIBUTING.md "Auditor who did not write it" check, done
in-house. **Outside review is still welcome**: anyone may re-run `audit/` or challenge a verdict.

Verdicts: **pass** (claim and statement hold), **pass with notes**, **fail**, **not auditable** (no
certificate to check).

---

## 2026-11-25 · Claim 757-1 (Erdős #757 upper bound, PR #4, main 013420f) · **pass with notes**

**Statement fidelity.**
- erdosproblems.com/757: finite A ⊂ ℝ, every 4-subset B has |B − B| ≥ 11, best c with a Sidon subset
  of size ≥ c|A|. Upstream `Erdos757.IsAdmissible` (formal-conjectures 9097e2f) says exactly this,
  quantified over every finite `A : Set ℝ`. |B − B| = 1 + 2·(number of distinct positive differences),
  so `11 ≤ (B - B).ncard` is "at least 5 distinct positive differences". Checked by enumeration too.
- `IsSidon` (FormalConjecturesForMathlib/Combinatorics/Basic.lean) is the sum form
  i₁ + i₂ = j₁ + j₂ → {i₁,i₂} = {j₁,j₂}, including i₁ = i₂. That is the standard Sidon notion.
- Junk values: `sSup` on ℝ returns 0 for empty or unbounded sets. Not an issue here: the set is
  nonempty (c = 0) and bounded (c ≤ 1 via a one-point A), and our proof bounds every element by 7/12
  with `Real.sSup_le`, so it does not exploit junk values.
- "Every n" vs asymptotic reading: the Lean statement takes inf over all finite sets. By Ma–Tang
  (arXiv:2602.23282, Prop. 3.7, subadditivity) inf_n f(n)/n = lim f(n)/n, so the two readings agree
  and a single finite witness is a legitimate upper bound.
- `OpenProblemsLab.E757.erdos_757_upperBound` has the same type as upstream
  `erdos_757.variants.upperBound` (textual copy, same vacuous `{A : Set ℝ}` binder, no local
  shadowing of `IsAdmissible`).

**Proof.** CI on main 013420f: build, no sorry, axioms `[propext, Classical.choice, Quot.sound]` for
both theorems, leanchecker passes (run 45625045247). The witness was rechecked by the Auditor's own
script `audit/erdos757_check.py` (bitmask enumeration, difference-form Sidon test, cross-checked
against the sum form on all 4096 subsets): all 495 four-subsets pass, largest Sidon subset is 7
(e.g. {92, 95, 107, 184, 188, 190, 238}), exactly the 10 listed 3-APs exist.

**Notes (non-blocking).**
1. Tie the wrapper to upstream by type, so a future upstream edit cannot silently diverge:
   `example : type_of% @Erdos757.erdos_757.variants.upperBound := @erdos_757_upperBound`.
2. Stronger target with the same method: Ma–Tang's 14-point set
   {0,136,200,243,246,249,272,286,298,323,400,528,596,1056} has largest Sidon subset 8, giving
   sSup ≤ 4/7, the best known upper bound. A Lean proof of that would match the literature.
3. For the lower bound `1/2 < sSup`: the Lean statement needs a bound for every finite A, not only
   large n. Either use a bound valid for all n (Tao's page 5b quotes h(A) ≥ n − ⌊(8n−6)/17⌋ from Ma–Tang
   Lemma 2.4 + Henning–Yeo, not yet checked by us) or formalise the subadditivity step.
4. CI runs `lake update` even though `lake-manifest.json` is committed; dropping it would make builds
   use the pinned manifest exactly.

---

## 2026-11-25 · Claim 757-2 (Erdős #757 `sSup ≤ 4/7`, PR #7) · **pass**

**Statement.** `OpenProblemsLab.E757.FourSevenths.sSup_le_four_sevenths : sSup {c : ℝ | IsAdmissible c} ≤ 4 / 7`
uses upstream `Erdos757.IsAdmissible` and `IsSidon`, with no local shadowing. Fidelity of those
definitions, and why one finite witness is a legitimate upper bound, are covered in the 757-1 entry.
`≤ 4/7` is exactly Ma–Tang's (arXiv:2602.23282) bound. There is no reliance on `sSup` junk values.

**Witness.** `audit/erdos757_check_n14.py` (Auditor's own, independent of `check_n14.py`): all 1001
four-subsets pass, largest Sidon subset is 8 (e.g. {0, 136, 200, 243, 246, 298, 323, 528}), exactly
the 12 listed 3-APs.

**Proof.** Read in full. The `powersetCard_succ_insert` split (A₀ = insert 0 (insert 136 A₂)) covers all
4- and 9-subsets. The rest is the 757-1 argument. The new theorem is in `scripts/Axioms.lean`. Pass
conditional on green CI for PR #7 (build, no sorry, standard axioms, leanchecker).

Nit raised on the PR: the ledger's "upper side fully formalized" should read "best known upper bound formalized".

---

## 2026-11-25 · PR #10 (novelty check, reader's 5/9 family for #757) · **pass, conditional on one rewording**

**5/9 family (erdosproblemaday.com reader submission 7bkzb8).** I rechecked it independently with
`audit/erdos757_five_ninths.py`. The test uses the literal |B − B| ≥ 11 on every 4-subset and sum-form Sidon,
on sets scaled to integers. The largest Sidon subset comes from HiGHS MILP, a different solver from the PR's CP-SAT.
Results: S_K is a (4,5)-set with |S_K| = 11 + 9K and h = 7 + 5K for K = 0..8. K = 6 gives 37/65 < 4/7 and
K = 8 gives 47/83 ≈ 0.5663. **Verified by us: c ≤ 47/83.** The limit c ≤ 5/9 needs the claim for every K,
which rests on the site's all-depth argument (level/fixed-point lemma plus transfer matrix). AI referees
reviewed that argument and we have not checked it. Required rewording: say "5/9 claimed, 47/83 verified" in place of "the open window is 9/17 ≤ c ≤ 5/9".

**Novelty.** Fair. The 757-1/757-2 "very likely first complete Lean proofs" claim is supported by my spot checks:
formal-conjectures main still has `sorry`, and teorth `problems.yaml` lists #757 as `unformalized`. The upstream PR states
are on the novelty thread's word. "C37-1 not a first" is also fair (nit: Koshta's certificate is the original proof, not an alternative one).

**Planning note.** A Lean proof of ≤ 37/65 cannot use the enumeration method of 757-1/757-2 (C(65,38) ≈ 10^18
subsets). It needs the structured argument.

---

## 2026-11-25 · PR #13 (5/9 transfer certificate, gadget search) · **pass, conditional on two rewordings**

**Transfer certificate (`explorer/erdos757/gadgets/transfer_certificate.py`).** The telescoping is correct, and
the state conventions match, because φ is increasing with φ(a)=p and φ(b)=q. I reproduced it independently with
`audit/erdos757_five_ninths_transfer.py`: W = [[5,6,6,6],[4,5,5,5],[4,5,5,5],[4,5,5,5]], first-copy vector
[6,7,7,7], and π = (0,1,1,1), g = 5 is a valid potential. **h(S_K) ≤ 7 + 5K for every K, unconditionally:** the
upper bound is a union bound over the traces and needs no geometric assumption. Combined with the exact values
for K ≤ 8, it is tight there. For an all-K proof of c ≤ 5/9, only the geometric half is still unchecked by us:
|S_K| = 11 + 9K, no cross-copy relations, and the (4,5) property for every K.

**Negative search (no 2-point chain gadget below 5/9 with 12–14 points).** Spot-check: `ord.py 12 11 2` gives
50/50 UNSAT, as logged. The solver bounds potentials by PM (default 4), but a valid potential can need a span up
to 3·(den·t − num), which is 27, 15 and 33 for n = 12, 13 and 14. I reran n = 12 with PM = 27: still 50/50 UNSAT, so n = 12 is
complete within the class (not proof-logged). Required: rerun n = 13 and n = 14 with a sufficient PM, or label them
"bounded potentials". Also, the ledger log line must carry the class restrictions and the "not proof-logged" caveat.

---

## 2026-11-25 · PR #15 (all-K proof that the 5/9 family works, so c ≤ 5/9) · **pass**

Computer-assisted, exact, unrefereed by humans. I read the reduction step by step and found it sound:
- **Counting:** copies meet only in the glued pair, and non-adjacent copies are disjoint because O ∩ I_2 = ∅.
- **Depth normalisation:** both templates have coefficient sum 0, and φ^{−d} lowers every depth by exactly d.
- **Slot refinement:** the split into "depth exactly L+1" or "depth ≥ L+2" is complete, the intervals are closed, and ignoring distinctness of unknown slots only over-approximates.
- **Step 4:** every relation lies in some φ^d(S_1). Copy APs from copies ≥ 2 apart are disjoint, and adjacent ones lie in a common S_1 image.

Nit raised: the docstring's "copy k+1 / k+2" case and the 0/269 check are redundant.

Independent cross-check: `audit/erdos757_five_ninths_nomix.py`, separate code using depth-first refinement on the
shallowest deep slot. It finds 0 mixing relations (33,572 nodes, refined to level 3). A positive control finds the
expected adjacent-depth APs, and brute force on S_10 (101 points) finds no relation spanning non-adjacent depths.
Combined with the transfer certificate (PR #13 entry): **c ≤ 5/9 is checked by us for all K.** Not yet in Lean.

---

## 2026-11-25 · PR #17 (Lean: `sSup {c | IsAdmissible c} ≤ 5/9`, head 6f1e264) · **pass**

**Statement.** `OpenProblemsLab.E757.FiveNinths.sSup_le_five_ninths` uses upstream `IsAdmissible` and `IsSidon` only, with no local
shadowing. Every local definition (`S`, `Good`, `Rep`, `slots`, …) stays out of the final statement, so their
correctness rests on the kernel.

**Trust base.** I grepped for `sorry`/`admit`/`native_decide`/`axiom`/`implemented_by`/`extern`/`unsafe`/`opaque`, custom
syntax, and `debug`/`skipKernelTC`. There are none. The only option set is `set_option Elab.async false`, which is harmless.
CI run 45715173845 is green: axioms are [propext, Classical.choice, Quot.sound], and leanchecker replayed FiveNinths.

**Glue (read for intent).** `Rep`/`exists_rep` split every point into a known S_3 point or the interval φ^[4][0,269].
`nmA`/`nmB1`/`nmB2`/`nmT` are no-mixing through a point of O. `good_S` runs the induction, with a finite check of S_2 (`good_S2`)
and `comp_pull`. `sidon_bound` is the transfer certificate. This matches the Python proof passed under PR #15.
**c ≤ 5/9 for Erdős #757 is now Lean-checked.**

---

## 2026-11-25 · PR #19 (negative results: multi-point gluing, 16-point search) · **pass at cb059ba**

Wording check only. The 16-point run is described accurately: the first SAT call timed out on the 18 port choices tried.
The multiglue ratio is the within-copy transfer value. It is an upper bound on the Sidon growth, because cross-copy
progressions could only lower the true h. After the fix, the PR says this and notes that (4,5) validity was not checked.
"Nothing below 5/9" therefore holds only under no cross-copy progressions, and the PR now states it that way.

---

## 2026-11-27 · open-problems-lab PR #17 (Partial List Colouring Conjecture fails for every k ≥ 3 with ℓ = k − 1 [PLC-3], `Lab/PartialList/General.lean`) · **pass, conditional on CI green**

Internal audit, outside review welcome. Reviewed at f5f9723.

- **Statement.** `not_partialListColouringConjecture_general k` (k ≥ 3) gives a finite graph with `listChromaticNumber = k` (formal-conjectures'
  definition) and (k−1)-lists such that every proper partial colouring has |S|·k < n·(k−1). That is exactly "fewer than n(k−1)/k vertices can be coloured".
  `not_conjecture_of` feeds it into the PLC-1 definition of `PartialListColouringConjecture`. `Gk 2` is Noel's graph.
- **Proof (re-derived by hand).**
  - Upper bound: each clique has a common m-list. If all terminals are coloured, their colours spell out S_f for one f, which blocks vertices 0 and 1 of
    clique f. So |S|·k ≤ n·m − 1.
  - Choosability: if two terminal lists meet, Hall's condition holds per clique. Otherwise a clique blocks at most ∏|L(t_i) ∩ L(v₁)| ≤ 2 choices,
    and 2·m^m < (m+1)^m.
- **Independent recheck.** The Auditor's own CP-SAT script finds exact optima of 9/14, 83/111 and 1027/1284 for k = 3, 4, 5, equal to m^k + m − 1.
  Random k-lists were all colourable (300, 300 and 40 trials).
- **Trust base.** A grep of `General.lean` is clean. Axioms are listed in `scripts/Axioms.lean`. There was no local build (no Lean toolchain in the
  Auditor's container), so the verdict relies on CI.
- **Novelty.** "To our knowledge, no case other than Noel's (3, 2) had been settled" is fair. Noel calls (3, 2) the first non-trivial case. The known
  positive results (ℓ | k; Iradmusa's half of the ℓ values per graph; Janssen's Δ ≤ k) do not cover ℓ = k − 1, and the Auditor's web search found
  no follow-up.
- **Required changes.** None.

---

## 2026-11-27 · open-problems-lab PR #16 (connected Partial List Colouring counterexamples with gap n/42 [PLC-2], `Lab/PartialList/Connected.lean`) · **pass, conditional on CI green + 1 wording fix**

Internal audit, outside review welcome. Reviewed at 3b5d815.

- **Statement.** For every t ≥ 1, `connected_gap` gives a graph on 14t vertices that is `Connected`, has `listChromaticNumber = 3`
  (formal-conjectures' definition), and has 2-lists such that every proper partial colouring has |S| ≤ 9t and 2n ≥ |S|·χ_ℓ + t. That is exactly
  a gap nℓ/k − |S| ≥ n/42.
- **Proof.**
  - The bound of 9 per copy holds by restriction.
  - `colour_avoid` carries Noel's 8 < 9 pair count, because the first triangle's bad pairs lie in one set of at most 3 colours (`bad_cases`, `bad_sub`).
  - The copies are coloured in order, and the link edge (j+1,3)–(j,2) gives connectivity.
- **Independent recheck.** The Auditor's own script finds the chains for t = 1 and t = 2 connected, with maximum partial colourings of exactly 9 and 18. Random
  3-list sanity checks also passed: the t = 3 chain, and Noel's graph with vertex 3 avoiding a colour.
- **Trust base.** It is clean, and the axiom audit covers all four theorems.
- **Novelty and wording.** An arXiv search finds nothing after Noel. The Chappell cap (2n/21) is right. Noel's remark is a suggestion, not a formal open
  problem, so ACHIEVEMENTS should soften "answered an open question" to "answered a question raised in Noel's paper (no published answer known to us)".

---

## 2026-11-27 · open-problems-lab PR #14 (second minimal claw-free Schur counterexample [CF-2], `Lab/ClawFree2/`) · **pass, conditional on CI green + 2 wording fixes**

Internal audit, outside review welcome. Reviewed at 0112e2c.

- **Graph.** The paper's graph6 ``K?`CR@`bAbRB`` (Prajapati Prop. 4) decodes, label for label, to `edgesG` (21 edges). `adjBits` matches. The graph is
  claw-free and is the line graph of a graph with 10 vertices and 12 edges. It is Wang–Zhang–Zhao's G₂.
- **Independent recheck.** The Auditor's own script gives:
  - 7,680 proper 4-colourings;
  - monomial coefficients 5322: 24, 4422: 176, 4332: 440 and 3333: 1056, and no other non-increasing contents (so `antiOK` holds);
  - a Kostka matrix equal to K00–K33;
  - after a full triangular solve, Schur coefficients 24, 152, 240 and **−40**.
- **Proof structure.** It is CF-1's audited inversion with four shapes, and the shared definitions are unchanged. The `gen4` split is a kernel `decide`.
- **Trust base.** No sorry, native_decide, custom axioms or unsafe code. The axiom audit covers the three main theorems.
- **Fixes.** (1) The ACHIEVEMENTS date should be 2026-11-27, not 11-26. (2) Both the census ("exactly two") and the WZZ minimality claim are published computer
  results that we have not re-checked, so the text should say so.

---

## 2026-11-27 · open-problems-lab PR #12 (GMR smaller-group search, round 2: notes and scripts only) · **pass with notes (2 wording fixes)**

Internal audit, outside review welcome. Reviewed at 3fe6134.

- **§1 lemma is correct.** With commuting background, |H| ≥ ∏(l_i+1) and |J| ≥ ∏(k_i+1). The Auditor checked each step: HyzJ = H(z⁻¹yz)J,
  F_i = C_H(⋃_{j≠i}Y_j) ⊇ Z_i, and injectivity of R_1×⋯×R_m by successive conjugation.
- **The ratio formula and the floor table reproduce.** Under free rare double cosets with all rare labels distinct, the ratio is
  L³/(R₁R₄r₂r₃) and |G| ≥ L∏(k+1)(l+1). The Auditor's own enumeration gives the same floors: 60,025, 66,096,
  91,200, 107,604 and 114,688.
- **§2 is correct.** In a class-two 𝔽₂ group with a 3-regular 9×9 pattern, each row forces the even-weight vectors into
  rowspace(Z), so dim V1 ≥ 9 − #components ≥ 6. The same holds for V2, and dim W ≥ 5, so the order is at least 2¹⁷.
- **Fixes requested.**
  - (1) The floor covers commuting-background *block* designs, not the whole family. Elsholtz's 2²³ circulant is not a block design.
  - (2) "A non-free double coset only lowers the ratio" is unproved; state it as an assumption. In a model check (per-block size |H||J|/t,
    t ≤ 4), no design gets below 60,025.
- **Not checked.** The CP-SAT and GAP sweeps were not re-run; the timeouts are honestly listed. The affine one-liner was not checked.

---

## 2026-11-27 · open-problems-lab PR #10 (Partial List Colouring Conjecture is false [PLC-1], `Lab/PartialList/Counterexample.lean`) · **pass, conditional on CI green**

Internal audit, outside review welcome. Reviewed at 5dda71d.

- **Definitions are standard.** `IsKChoosable` and `listChromaticNumber` are formal-conjectures' definitions, checked at the pin 9097e2f:
  lists of exactly k colours from ℕ, and the χ_ℓ is the sInf over k. This is the standard Erdős–Rubin–Taylor notion; "exactly k" is equivalent to "≥ k".
- **The statement matches AGH 2000 as stated by Noel.** For finite G with 1 ≤ ℓ < χ_ℓ and lists of exactly ℓ colours, it asks for
  a set S, properly coloured from the lists, with n·ℓ ≤ |S|·χ_ℓ. That is the bound |S| ≥ nℓ/k written without division.
- **The graph and lists match Noel §2.** The terminals 0 and 1 are non-adjacent. Triangle i is {3i+2 (private), 3i+3, 3i+4}. The terminals are
  joined to the non-private vertices only (28 edges). The triangle lists are {1,3}, {1,4}, {2,3} and {2,4}, with L(s₁) = {1,2} and L(s₂) = {3,4}.
- **Independent recheck.** The Auditor's own exhaustive search finds a maximum partial colouring of 9 (< 28/3), and the graph is not 2-colourable. As a
  sanity check, 200,000 random 3-list assignments (palettes of 3–7 colours) were all colourable. The proof of 3-choosability itself is Lean's.
- **Trust base is clean.** No sorry, native_decide, custom axioms or unsafe code. The axiom audit covers all four theorems.

---

## 2026-11-27 · claw-free Schur-positivity conjecture is false [CF-1], `Lab/ClawFree/` · **pass, conditional on CI green + 1 wording fix (fix applied)**

Internal audit, outside review welcome. Reviewed on the private draft before the lab moved to this repository
(same Lean files); the requested wording fix has since been applied.

- **Definitions are faithful.**
  - `IsClawFree` means no induced K₁,₃.
  - `chromSym G n` is X_G with x_k = 0 for k ≥ n.
  - `IsSSYT`/`schurPoly` give the standard semistandard fillings (Mathlib cells are (row, col)).
  - The finite-variable restriction is a ring map that keeps ℕ-coefficients, so the classical conjecture implies
    `ClawFreeSchurPositivity`, and refuting it at n = 4 refutes the classical one.
  - `SchurPositive` allows any finite set of diagrams, so it is at least as weak as the standard notion. The proof
    handles five-row shapes (they vanish) and shapes of other sizes.
- **The graph matches Prajapati Thm 1.** L(H), built from the paper's description, is isomorphic to the paper's
  graph6 ``K?`CRAWWUXIM`` (networkx). So is the Lean `adjN` graph, and `adjBits` matches. It has 12 vertices and
  22 edges and is claw-free.
- **The counter is verified.** `mem_gen`, `nodup_gen` and `card_filter_eq` are Lean proofs, and the 84-prefix split is
  sound (`gen4`, `gen_add`). All counts use `decide +kernel`.
- **Independent recheck.** The Auditor's own backtracking, SSYT Kostka numbers and full triangular solve over partitions
  of 12 with ≤ 4 parts give 5,376 colourings, monomials 4422: 128, 4332: 320 and 3333: 768, and Schur coefficients
  128, 192 and **−64**.
- **Trust base is clean.** No sorry, native_decide, custom axioms or unsafe code. The axiom audit covers the
  three main theorems.
- **Fix requested.** The claim "12 vertices is the minimum" is the paper's computer census (Prop. 4), not re-run by
  us. ACHIEVEMENTS and the ledger Log must say so. (Done.)

---

## 2026-11-26 · PR #43 (non-abelian GMR inequality false in a group of order 2^17 [GMR-1], `Lab/GMR/Counterexample.lean`) · **pass, conditional on CI green + 3 wording fixes**

Internal audit, outside review welcome. Reviewed at 3d318f7. This is a new result, so fidelity and novelty were checked against the primary sources.

- **Statement is faithful.** `NonAbelianGMR` matches GMR Problem 1.3 as quoted by Nair–Namayandeh–Zhu (Conj. 1) and
  Elsholtz (eq. (2)): |A₁⋯Aₙ|^(n−1) ≤ ∏ max_{a∈Aᵢ} |A₁⋯a⋯Aₙ| for nonempty finite sets in any group. The product is
  the ordered pointwise product, `sliceMax` is a `sup` over nonempty sets, and `H` has one `Group` instance whose
  laws are proved in Lean (`card_H = 131072`).
- **Independent brute force gives the same numbers.** The Auditor's own script, built from the Lean `T` matrix, gives:
  - |S| = 114,688 and N = (2368, 16384, 16384, 2368), ratio 1372/1369;
  - 27 distinct nonzero labels;
  - ω bilinear, the group associative and non-abelian.
- **Construction.** This is Elsholtz's Prop. 6.8 (sparse single-coordinate template) with k = ℓ = 64, r = s = 9,
  I = 27 and Δ = 3, the same ratio as his Thm 6.7 (order 2²³). What is new is the realization: three 3×3 blocks on
  2-dimensional row and column spaces, so 17 dimensions instead of 23.
- **The group is new and smaller.** Elsholtz v1 (Table 3, Q 9.1) gives 518,400 as the smallest found for n = 4, 5
  and says after Prop. 6.8 that beating it with the sparse template is open. A singleton pad also gives n = 5 in
  the same group. arXiv and web searches on 26 Nov 2026 found nothing later. For n ≥ 6, smaller groups (1728, 243)
  are already published.
- **Trust base is clean.** There is no sorry, native_decide, custom axioms or unsafe code; the label counts are
  `decide +kernel`. The axiom audit covers all three theorems.
- **Fixes requested.** (1) Cite Thm 6.7 / Prop. 6.8 (§6) and §9, not "§5" / "§10". (2) Say in ACHIEVEMENTS that the
  record is for four (and five) sets. (3) Write "almost four times smaller" (518,400/131,072 ≈ 3.96) and call it a
  new realization of Elsholtz's template.

---

## 2026-11-26 · PR #41 (List Total Colouring Conjecture is false [LTC-1], `Lab/ListTotal/Counterexample.lean`) · **pass, conditional on CI green**

Internal audit, outside review welcome. Reviewed at 9d1064a.

- **Definitions match the standard ones.**
  - `IsTotalColoring` and `totalChromaticNumber` are formal-conjectures' definitions, checked at the pin 9097e2f.
  - `TotalChoosable k` (lists `Finset ℕ`, card ≥ k) is standard k-total-choosability. ℕ colours lose
    nothing (relabel injectively), and "≥ k" is equivalent to "= k", so `¬ TotalChoosable 4` refutes 4-choosability.
  - `listTotalChromaticNumber` is `sInf`. The `≠` proof handles the empty-set case.
- **Scope.** The conjecture is stated for finite simple graphs. That is a special case of the published
  multigraph conjecture, so refuting it refutes the original.
- **Graph and lists match Noel (arXiv 2609.38417).** Four blocks, each a K₂ core plus 3 terminals, give a
  cubic graph on 20 vertices (`G_cubic` by `decide`). Inside block i the lists are [5]∖{i+1}. The
  cross-edge lists are B1B2∖3, B1B3∖5, B1B4∖2, B2B3∖4, B2B4∖5 and B3B4∖1, all as in the paper.
- **Independent SAT recheck.** The Auditor's own pysat encoding, written from the paper text, gives:
  no colouring from the lists (UNSAT), a 4-total-colouring exists (SAT), no 3-total-colouring (UNSAT).
- **Trust base and wording are clean.**
  - No sorry, native_decide, custom axioms or unsafe code. The axiom audit covers the new theorems.
  - Noel is credited.
  - The upper bound χ''_ℓ ≤ 5 is stated as not formalized (and it is not needed).
  - "Appears to be the first formal proof" is hedged.

---

## 2026-11-26 · PR #39 (Davenport rank-9 search, round 2: notes and scripts only) · **pass**

Internal audit, outside review welcome. Reviewed at d4af319.

- **5-condition reduction: exact.** The Auditor re-ran `req.py`, `minreq.py` and `ach.py`:
  - With rank-1 blocks (any length-4 zero-sumfree sequence in C₆), the third block's unique minimal
    requirement is {011, 100, 101, 110, 111}.
  - So the 5-condition is necessary and sufficient for that rank-9 layout.
  - The paper's block fails it (`cond5.py`, |Miss| = 7).
- **Rank-4 scan: matches exactly.** The re-run of `fam.c 4 1` gave 1,377,037 zero-sumfree blocks, 4
  passing the 3-condition (all of the paper's type up to a basis change) and 0 passing the 5-condition.
  This is a structured-family search, not a proof.
- **Two copies of the paper's block, m = 8: UNSAT, confirmed independently.**
  - Their CaDiCaL model returns UNSAT (27 s).
  - The Auditor's own CNF (balanced adders, Glucose4) also returns UNSAT.
  - Fixing the first top term to 0 is WLOG.
- **Rank-3 claims and timeouts are honestly labelled.** The rank-3 results are reported as "none
  found" and the timeouts as uninformative, consistent with the rank-15 calibration failure. The
  Auditor corrected project memory, which had said "no rank-3 block has…".

---

## 2026-11-26 · PR #35 (Davenport: full GGWZ Thm 1.1 with floor term [DAV-4], `Lab/Davenport/FloorTerm.lean`) · **pass, conditional on CI green + ACHIEVEMENTS entry**

Internal audit, outside review welcome. Reviewed at 2bd45b3.

- **Statement.** `ggwz_floor`: for n % 4 = 2, n ≥ 6 and every r, there is a zero-sumfree multiset of
  size r(n−1) + (r−1)/(5(n/2)−1).
  - Since n is even, n/2 = k exactly, so ℕ division is ⌊(r−1)/(5k−1)⌋ for r ≥ 1.
  - The r = 0 case is a harmless extension.
  - Because D = 1 + d, this is exactly GGWZ v3 Thm 1.1.
- **`replace` lemma.** Its hypothesis ("nonempty, K-part 0, so C_n-part 1") is the paper's "every
  subsum in ⟨F₁⟩ equals F₁", and the map (w, j) ↦ (w, j•g) is the paper's.
- **`P_key`.** It is that property for P = S − (n−2)·F₁, proved the paper's way.
- **Iteration.** The ranks and length bookkeeping match.
- **Remark.** The n = 6 Remark (⌊(r−1)/8⌋) is still marked unproved.
- **Trust base.** No sorry, no decide, no native_decide, no axiom. All three theorems are in
  Axioms.lean.
- **Condition.** Add a DAV-4 line to ACHIEVEMENTS.md (Kyle's standing rule).

---

## 2026-11-26 · PR #31 (Davenport: Lean proof of the whole GGWZ family [DAV-3]; rank-9 search notes) · **pass, conditional on CI green**

Internal audit, outside review welcome. Reviewed at 5aa68d6.

- **`ggwz` statement.** For n % 4 = 2, n ≥ 6 and 5n ≤ 2r, there is a zero-sumfree multiset of r(n−1)+1
  elements in Fin r → ZMod n. This is exactly the "in particular" part of GGWZ v3 Thm 1.1 (r ≥ 5k).
- **`vEBK_fails` statement.** It is the negation of the PR 28 conjecture def at each such (n, r).
- **Construction.** The Auditor's own transcription of the paper's general construction, with padding,
  equals a literal reading of `vZ`/`mult` as a multiset for t = 1..4 and b ∈ {0, 3}.
- **Not-formalized wording.** The statement that the floor term `⌊(r−1)/(5k−1)⌋` is not formalized is
  honest and appears consistently.
- **Trust base.** No sorry, native_decide, axiom, extern, unsafe or set_option. The arithmetic is
  symbolic in t.
- **Rank-9 notes.** Reproduced independently: 66,672 zero-sumfree length-9 sequences in C_6², none with
  a valid (c, a, d) triple.
- **Stronger than the README says.** Rank-1 and rank-2 blocks each need deficit ≥ 2, and the scheme at
  rank 9 has total deficit 3. Every split of block ranks summing to 6 has two blocks of rank ≤ 2, so no
  choice of ranks or deficits works. The search runs are correctly labelled inconclusive.

---

## 2026-11-26 · PR #28 (Davenport: Lean disproof of van Emde Boas–Kruyswijk via GGWZ, C_6^15 [DAV-1]; CP-SAT check [DAV-2]) · **pass, conditional on CI green + one rewording**

Internal audit, outside review welcome. Reviewed at 6a8f469.

- **Fidelity.** `VanEmdeBoasKruyswijk` says: for all n > 0 and all r, every multiset of ≥ r(n−1)+1
  elements of `Fin r → ZMod n` has a nonempty zero-sum sub-multiset. That is D(C_n^r) ≤ r(n−1)+1,
  and the ≥ direction is classical. So its negation is the negation of Conjecture 1 in GGWZ v3
  (vEB–K 1969). The r = 0 case is trivially true, so including it is harmless.
- **Construction.** The Auditor's own transcription of GGWZ v3 (proof of Thm 1.1, k = 3) equals
  `M`/`mult` as a multiset: 35 distinct elements, 76 terms.
- **Self-contained.** The Lean proof does not rely on the unrefereed paper's argument.
- **Trust base.** No sorry, native_decide, axiom, extern or unsafe. `decide` is used only on the
  35×15 table, and all three theorems are in `scripts/Axioms.lean`.
- **DAV-2.** The encoding is correct and the controls are sensible. It is a solver verdict.
- **Condition.** Reword DAV-2 "exact CP-SAT infeasibility proof" to "CP-SAT infeasibility verdict
  (no certificate exported)".
- **Non-blocking suggestion.** In ACHIEVEMENTS, lead with "machine-checked GGWZ's disproof".
- **Novelty wording.** "Appears to be the first machine-checked disproof; the mathematics is GGWZ's"
  is acceptable.

---

## 2026-11-26 · PR #25 (C44: Lean proof of C44 ≥ 3/2 [C44-1]; block-composition search [C44-2]) · **pass, conditional on three rewordings + CI green**

Internal audit, outside review welcome. Reviewed at 39b2f46.

- **C44-1 fidelity holds.** `DegLE` (span of monomials of size ≤ d) is equivalent to real degree ≤ d,
  because the monomials are a basis. `Relevant` is flip-sensitivity. Tao's C44 = sup_d R_d/2^d
  satisfies the hypothesis of `three_halves_le`, so C44 ≥ 3/2 follows.
- **C44-1 matches the paper.** `exists_degLE_all_relevant` gives n + 2 = 3·2^(d−1), and Ξ is the
  CHS recursion.
- **C44-1 trust base.** No sorry, native_decide, axiom, extern, or unsafe. Both theorems are in
  `scripts/Axioms.lean`.
- **C44-2 reduction (`wdeg2.py`) is correct.** Heavy blocks are pairwise heavy, so
  G = A + Σ u_j B_j. Flipping u_j forces B_j ∈ {0,±1}, and from that exactly one piece is ±1 at each z.
- **C44-2 encoding is correct.** Degree caps, relevance, and the minimal-heavy-set derivative
  constraints are all right.
- **C44-2 enumeration (`weight_vectors`) is complete.** Its only pruning, Σ w·2^w ≤ d·2^d, is a valid
  necessary condition: substitute parities, then use the influence bound.
- **Recount from the logs.**
  - d = 5, ≤ 9 blocks: 127/127 infeasible.
  - d = 6, ≤ 9 blocks: 361/361 infeasible.
  - d = 6, 10 blocks: 167/172 infeasible.
  - wdeg2 recheck: 89/89 agree. SCIP: 51 agree (35 of them are all the ≤ 6-block d = 5 shapes).
- **Auditor's own brute force** (full Fourier test): no ≤ 4-block shape is feasible. The CHS
  controls are feasible.
- **Status of C44-2.** Solver verdicts, with no certificates exported.
- **Conditions (wording).**
  1. Ledger row "R_d ≥ 2R_(d−1)+2 … Lean-checked" overclaims, because only Ξ_d is formalized.
  2. ACHIEVEMENTS "searched every way …" must name the block-composition class and say these are
     solver verdicts.
  3. README d = 5 10–11-block row: the committed logs give 80 ruled out / 14 undecided (w5d.log is
     cited but missing).
- **Novelty.** "Appears to be the first formal proof" is acceptable. No formalization found:
  formal-conjectures has none, and Pinho's repo states none.

---

## 2026-11-26 · PR #23 (Lean proof of C37-1, `Lab/C37/Degree4.lean`; round-2 (14,5) results; C37 paused) · **pass, conditional on CI green**

Internal audit, outside review welcome. Reviewed at 8c200bd.

- **Statement fidelity: acceptable as is.** `no_degree4_sensitivity10` rules out integer multilinear
  coefficients `c` on 10 variables satisfying four conditions: `c ∅ = 0`, `c {i} = 1`, `c S = 0` for
  `|S| ≥ 5`, and `0 ≤ ∑_{S⊆x} c S ≤ 1` at every point. Each Boolean `q` has a unique such `c`
  (Möbius inversion gives integer coefficients), and degree is defined as max `|S|` with `c S ≠ 0`.
  So this is Koshta's normalized statement (n = 10, fully sensitive point 0, `q(0) = 0`).
  The constraints are pointwise Boolean ones, not just the averaged LP.
- **Not formalized, recorded as notes:**
  - the existence half of Möbius inversion
  - the standard WLOG reduction from "s(f) ≤ 9 for every degree-4 f" to this normal form
  - Suggested ledger wording: "Lean-checked in normalized coefficient form".
- **Trust base.** No sorry, admit, native_decide, axiom, extern, unsafe, opaque, custom syntax, or
  set_option. `#print axioms` was added to `scripts/Axioms.lean`.
- **Proof.** It matches the audited C37-1 certificate: the (8,2) split, `linarith` reaching
  `3·Cp(1,2) = 14`, which agrees with `audit/c37_own_cert.py`.
- **Search results.** I recounted the result files. Level 2: 77 infeasible, 71 feasible, 99
  undecided of 247. Rerun: 1 infeasible, 6 feasible, 2 unknown of 9. No new claims. The withdrawn
  buggy run is disclosed. "Paused" is justified.
- **Condition.** At review time the PR conflicted with main in `Lab.lean` and `scripts/Axioms.lean`
  (trivial append conflicts), so CI had not run. The pass applies once the Lean workflow is green.

---

## 2026-11-25 · Claim C37-1 (short proof of Koshta's degree-4 theorem, draft PR #5, 2186ff5) · **pass with notes**

**Statement fidelity.** Koshta 2026 as listed on Tao's optimisation-constants page (37a): there is no
q : {0,1}^10 → {0,1} with deg q ≤ 4, q(0) = 0, q(e_i) = 1. C37-1 claims exactly this. This implies every
degree-≤4 Boolean f has s(f) ≤ 9: shift a maximally sensitive point to 0, negate if needed, and restrict
to 10 sensitive coordinates (restriction keeps the function Boolean and does not raise degree).

**Certificate.** Rebuilt from the definitions without PR 5's code:
- Own LP (`audit/c37_find_own_cert.py`, scipy): with the (8,2) split the feasible region of the
  orbit-sum LP is a single point; every orbit sum is pinned, including C[1,2] = 14/3 (also
  C[3,0] = 98/3). The 9+1, 7+3, 6+4, 5+5 splits are feasible, so the (8,2) split is what does the work.
- Own exact certificate (`audit/c37_own_cert.py`, standard library, exact fractions): 8 multipliers
  for C[1,2] ≥ 14/3 and 9 for C[1,2] ≤ 14/3 (17 in total, different multipliers from PR 5). Changing
  one multiplier makes it fail.
- PR 5's file `results/cert_n10_d4_split8_2.json` re-verified with the Auditor's own forms
  (`audit/c37_verify_pr5_cert.py`): lower and upper combinations each reduce to ±C[1,2] + 14/3 ≥ 0.

**Notes (non-blocking).**
1. Novelty: Pinho (hexagonmath 2610.00694, Oct 2026) says his rational lattice packet "reproves"
   B4 ≤ 9. Before calling ours new, compare with his certificate and with Wellens 2022.
2. The certificate is written in terms of class counts N(i,j); a two-line derivation of why the
   orbit sums C[a,b] are integers and why N(i,j) is affine in them would help outside readers.

## 2026-11-25 · Claim C37-2 (symmetric (14,5) exclusions, PR #5) · **not auditable yet**

CP-SAT "infeasible" verdicts only, with no exported certificate. Stays draft until each group comes
with an exact certificate (e.g. an LP/ILP infeasibility proof or a DRAT/VIPR proof) the Auditor can
recheck.

---

## 2026-11-25 · Claim 757-3 (Erdős #757 `9/17 ≤ sSup`, conditional on Henning–Yeo, 514abb3) · **pass with notes**

*Internal audit, outside review welcome.* Reviewed `Lab/Erdos757/LowerBound.lean`. Every type below
was checked with `#check`/`#print`, not taken from docstrings.

**Statement fidelity.**
- `isAdmissible_nine_seventeenths : HenningYeoBound → Erdos757.IsAdmissible (9 / 17)`
- `nine_seventeenths_le_sSup : HenningYeoBound → 9 / 17 ≤ sSup {c | Erdos757.IsAdmissible c}`
- `erdos_757_lowerBound_of_henningYeo : HenningYeoBound → ∀ {_A : Set ℝ}, 1 / 2 < sSup {c | Erdos757.IsAdmissible c}`

All three use upstream `Erdos757.IsAdmissible` and `IsSidon` without shadowing. The third has the
upstream type of `erdos_757.variants.lowerBound` (including the unused `{A}` binder), with
`HenningYeoBound` added as a hypothesis. `Is45 A` is literally the upstream condition
`∀ B ⊆ A, B.ncard = 4 → 11 ≤ (B - B).ncard`; the Auditor checked this by `rfl`. Boundedness for
`le_csSup` comes from 757-2 (`FourSevenths.admissible_le`), so there is no junk-`sSup` issue.

**`HenningYeoBound` is no stronger than the published theorem.** The source is Henning–Yeo, Graphs
Combin. 37 (2021) 867–890. The abstract says: no subhypergraph isomorphic to AG(2,3) minus two
vertices ⇒ 17τ ≤ 5n + 3m. Ma–Tang Thm 5.3 restates it as "3-uniform linear, no subhypergraph
isomorphic to F₇". The Auditor read the abstract and Ma–Tang's restatement, but not the paywalled full
text of HY Thm 7. The Lean hypothesis asks for:
- 3-element edges, which is 3-uniform;
- pairwise intersection ≤ 1, which is linear;
- `F7Free`.

It allows isolated vertices (V ⊇ ⋃E). Those only add 5 per vertex to the right-hand side, so this is
implied. Multi-edges cannot occur (`Finset`), and linearity forbids them anyway.

Induced vs non-induced: Lean excludes every not-necessarily-induced copy, which is the narrower
hypergraph class, so the result is implied under either reading. In fact the two readings coincide
for linear hypergraphs. The 6 pairs of {0..6} that F₇ leaves uncovered (14, 16, 23, 25, 36, 45)
contain no triangle, so no linear hypergraph can add an edge inside a copy of F₇.

**`HenningYeoBound` is not false or vacuous (brute force, `audit/erdos757_lower/hy.c`).** The search
covered every labeled linear `F7Free` 3-uniform hypergraph on exactly n vertices, n = 3..9, with exact
τ computed by subset bitmasks:

| n | hypergraphs | violations | min slack 5n+3m−17τ |
|---|---|---|---|
| 7 | 5,176 | 0 | 2 |
| 8 | 190,417 | 0 | 4 |
| 9 | 15,663,980 | 0 | 1 |

Smaller n also gives 0 violations.

Control run with the F₇ filter switched off:
- n = 7: exactly 420 violations, which are the 420 labeled copies of F₇ (slack −1).
- n = 8: 840 violations (AG(2,3) minus a point, slack −4).

So the filter removes exactly the known extremal obstructions and nothing else. A second, independent
Python implementation (`audit/erdos757_lower/rand.py`) ran 4,917 random greedy linear F₇-free
hypergraphs on 9–14 vertices: 0 violations, min slack 1. The same script confirms that AG(2,3) minus
two points has 5 edges and is a copy of F₇.

**`F7Free`.** Injective `g : Fin 7 → α` with edges 012, 034, 056, 135, 246 all in E is exactly
"contains a (non-induced) copy of F₇". The edge list matches Ma–Tang Fig. 1, and AG(2,3) minus two
points gives this structure (see the check above).

**Proof hygiene.** `scripts/check_no_sorry.sh`: "No sorry found." `scripts/check_axioms.sh`: "Axiom
audit passed". All three theorems, `apEdges_F7Free` and `apEdges_linear` use only
[propext, Classical.choice, Quot.sound]. `HenningYeoBound` is a `def … : Prop` used only as a
hypothesis, not an `axiom`/`opaque`. The file is imported by `Lab.lean`.

**Notes (non-blocking).**
1. Wording elsewhere should always say "conditional on Henning–Yeo". Upstream's docstring credits
   `1/2 < sSup` to [GyLe95] unconditionally, but this file does not formalize that proof. It reaches
   `1/2 < sSup` only through HY.
2. Tie the wrapper to upstream by type:
   `example : HenningYeoBound → type_of% @Erdos757.erdos_757.variants.lowerBound := @erdos_757_lowerBound_of_henningYeo`.
3. The docstring citation "(Gyárfás–Lehel, Prop. 2.6)" for F₇-freeness was not checked against
   GyLe95. Ma–Tang cite it as their Lemma 5.2 from [5]. Either way the Lean proof of `apEdges_F7Free`
   does not depend on it.
4. The brute-force check is evidence, not proof. The hypothesis rests on the published,
   peer-reviewed HY theorem, whose full text the Auditor did not read.

## PR 21: Erdős #1186 claims 1186-1 (27/242) and 1186-2 (479/4356), 2026-11-26

Auditor: independent subagent (Claude Opus 5.5), did not write the work, used none of the authors' code.
**Verdict: both PASS WITH NOTES.**

- **Exact values, different method.** `audit/erdos1186/clip.py` cuts the unit square into exact rational
  polygons along u + i t = m/K (Fractions, shoelace areas; no strips or midpoint rule). Cells 8 / 30 / 66
  for K = 1 / 2 / 3, areas sum to 1. Lu–Peng's B20 gives exactly 17/150 in all 8 classes mod 20;
  cert_22_2 gives 27/242 in all 10 classes mod 22; cert_44_3 gives 479/4356 in all 20 classes mod 44;
  the one-string rule in the README reproduces all 10 tables of cert_22_2.
- **Brute force on real primes** (`audit/erdos1186/bf.c`, checked against a naive counter at p = 409):
  every residue class at p just above 20000 and 100000; |p · (m4 − limit)| ≤ 0.14 (b = 22) and ≤ 0.016
  (b = 44), constant from p ≈ 1000 to 100000, so the error falls like 1/p.
- **PROOF.md** reduction correct: Lu–Peng convention (d = 0 included), y_i ≡ a + i d − r k_i (mod b),
  convex cells, lattice-point estimate, O(Kp) boundary points; every prime p > b has a unit residue and
  both certificates cover all units.
- **Fidelity:** normalisation m4 = 2 δ̃_4 confirmed against Lu–Peng and erdosproblems.com/1186.

Notes:
1. Fixed in this PR: "approach the limit from below" was false (sign depends on the class).
2. **Novelty: not a record.** A public GitHub project (Marquardt, incrediblecrab/erdos-problems `p1186`,
   2 Nov 2026, unrefereed) has m4 ≤ 0.109645 from circle colourings. Our bounds still beat the
   published 17/150 and use a different kind of colouring, but must not be called the best known.

## PR 22: Erdős #1186, combining with Marquardt is empty (negative result), 2026-11-26

**Verdict: PASS WITH NOTES** (in-house Auditor, independent subagent with its own scratch code).

- Algebra of the dilation x -> b⁻¹x mod p checked by hand: floor(bK·y/p) = tK + floor(Kx/p) with
  t = (−s·r⁻¹) mod b; the dilation is a bijection sending 4-APs to 4-APs, so counts agree exactly for each p.
- 8 random (b, K, G, p) cases (b up to 12, p 401 to 829): pointwise identical and identical full mono-4-AP counts.
- `equiv_check.py` reproduces 479/4356 exactly; `search2/rc.c` reproduces Marquardt's 2998-word value to 1e-16;
  own brute force at p = 30011 agrees to 5e-8.
- Prose: no record or optimality claim; Marquardt credited; correction of PR 21's "new kind" wording accurate.
- Also corrects audit note 2 of PR 21 above: our colourings are *not* a different kind; they are special cases of his.

Notes, all fixed in this PR: arc-count typo (18 to 62, not 64); "another way" wording in ACHIEVEMENTS;
underived statements now marked "derived, not written up" / "numerically"; exact recomputation is for r = 1 only.

## 2026-11-26 · Claim 757-4 (Erdős #757 `9/17 ≤ sSup`, unconditional; Henning–Yeo Theorem 6, PR 27) · **pass with notes**

In-house Auditor (independent subagent).
- Statement fidelity: `erdos_757_lowerBound` has exactly the upstream type of
  `erdos_757.variants.lowerBound` (checked by `example`), `nine_seventeenths_le_sSup_unconditional`
  and `henningYeoBound` take no hypothesis. `F7Free` (5 lines of AG(2,3) minus two points) is not
  vacuous and is proved for the real AP hypergraph; `isoEdges`/`wt`/`Theorem6Bound` match the paper.
- Trust surface: no sorry/axiom/native_decide/implemented_by/extern/unsafe/opaque in `Lab/` outside comments.
- `scripts/Axioms.lean`: `theorem6`, `nine_seventeenths_le_sSup_unconditional`, `erdos_757_lowerBound`
  depend only on propext, Classical.choice, Quot.sound. Local leanchecker on all new modules passed (≤ 7.4 GB).
- Notes (fixed in this PR): ledger said "Theorem 6 in full"; only the bound (first half) is proved,
  the strict part in the corrected weaker form; status line updated after this audit.

