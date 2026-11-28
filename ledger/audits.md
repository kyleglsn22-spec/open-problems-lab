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

## 2026-11-28 · open-problems-lab PR #46 (Hinrichs–Vybíral positive-definite-function conjecture disproof [HV-1], `Lab/HinrichsVybiral/Basic.lean`) · **pass, conditional on green `build` at 82e8ef0 and an ACHIEVEMENTS.md entry**

Internal audit, outside review welcome. Reviewed at 82e8ef0.

- **Statement:** `IsPosDef` (complex Hermitian form, equivalent to the paper's Σ c̄_j c_k convention) and `HinrichsVybiralConjecture` (continuous, bounded, nonnegative, positive definite, f(0) = 1 ⇒ (Σc)²/n ≤ Σ c_j c_k f(x_j − x_k)) match Conjecture 2 of Hinrichs–Vybíral (2011) as quoted in Vybíral, arXiv:2609.21733 v1 (only version), §1; the real-coefficient conclusion is implied by the matrix inequality, so its refutation refutes the conjecture. The 2011 original was not read directly (quoted by its co-author).
- **Proof:** read in full (feature expansion for PD; multiaffinity plus 128 sign vectors for f ≥ 0; integer identity for the form).
- **Independent recheck:** own Python (exact rationals): f(0) = 1; min of 280·P on sign vectors is 0; form 22/5 vs 9/2 (violation −1/10, paper eq. (2.3)); random Gram matrices PSD, random min f ≥ 0.
- **Trust base:** no sorry/axiom/native_decide/set_option; `decide +kernel` only; `#print axioms` added.
- **Ledger wording:** claims nothing beyond the Lean statement. Nit: shortlist row 6 still says "In progress".
- **Required changes:** add the HV-1 entry to ACHIEVEMENTS.md.

---

## 2026-11-28 · open-problems-lab PR #43 (Bougard–Joret conjecture, first regime, disproof at (7,3,4) [BJ-1], `Lab/BougardJoret/Basic.lean`) · **pass, conditional on green `build` at 64bd260 and an ACHIEVEMENTS.md entry**

Internal audit, outside review welcome. Reviewed at 64bd260.

- **Statement:** checked against the original Conjecture 1 (Bougard–Joret, J. Graph Theory 58 (2008), Section 6, author-hosted preprint): hypotheses n ≥ 2α, n ≥ α+k, α ≥ 2, k ≥ 3 and f = ⌈nk/2⌉ for n ≤ kα match `BougardJoretFirstRegime` (attainment plus lower bound). `KConnected` is standard; `indepNum` is the stability number. No amendment found (Das–Gupta 2608.18828 v1 only; Wang–Wu 2022 and Liu–Ning 2026 restate it unchanged).
- **Proof:** read in full (min degree ≥ k; 14 edges force 4-regular; independent triple complete to the rest; G − T is a perfect matching, disconnected).
- **Independent recheck:** exhaustive Python over labelled 7-vertex graphs: no 4-connected graph with α = 3 has 14 edges (465 with min degree ≥ 4 checked); 490 such graphs with 15 edges, so f(7,3,4) = 15.
- **Trust base:** no sorry/axiom/native_decide/decide/set_option; `#print axioms` added.
- **Required changes:** add the BJ-1 entry to ACHIEVEMENTS.md.

---

## 2026-11-28 · open-problems-lab PR #42 (Mizzi unstable-graph cycle conjecture disproof [UG-1], `Lab/Unstable/Mizzi.lean`) · **pass for the Lean content, conditional on green `build` at c628475 and documentation changes**

Internal audit, outside review welcome. Reviewed at c628475.

- **Statement:** `cdc`, `IsUnstable` (an automorphism of G × K₂ outside Aut(G) × ℤ₂), `IsVertexDetermining`, connected, non-bipartite and `HasCycleOfLength` (cycle subgraph) faithfully state the conjecture in the abstract of **v1/v2** of arXiv:2603.27559 ("every unstable graph contains C_k and C_2k for some odd k"). The both-in-G reading is the only non-trivial one (C_2k in the CDC is automatic for non-bipartite G).
- **Version issue:** v3/v4 (current, 16 Nov 2026) restrict the conjecture to **asymmetric** unstable graphs; v4 §7 discusses Srivastava's graph, notes |Aut(G)| = 2, and gives a smaller 7-vertex counterexample (C_6 plus a pin) to the old statement. The current conjecture is not refuted.
- **Edge list:** matches Srivastava (arXiv:2608.15281) eq. (2) and the list in Mizzi v4 §7.
- **Independent recheck:** own Python/networkx: connected, non-bipartite, vertex-determining; |Aut(G)| = 2, |Aut(CDC)| = 8 > 4; cycle lengths 5, 5, 6.
- **Trust base:** no sorry/axiom/native_decide/set_option; `#print axioms` added.
- **Required changes:** docs, ledger and ACHIEVEMENTS must say the refuted statement is the v1/v2 conjecture, since amended to asymmetric graphs (not refuted); drop or fix the "holds for ≤ 9 vertices" row and don't call the graph smallest.
- **Follow-up (792008d):** all required changes made (renamed to `MizziConjectureV1`, docs cite v1/v2 and the amendment, row dropped). Verdict now: pass, conditional only on green `build`.

---

## 2026-11-28 · open-problems-lab PR #41 (Goemans single-source unsplittable-flow conjecture disproof [GUF-1], `Lab/Goemans/Unsplittable.lean`) · **pass, conditional on green `build` at 8eee6b4 and an ACHIEVEMENTS.md entry**

Internal audit, outside review welcome. Reviewed at 8eee6b4.

- **Statement:** `IsFlow`, `fracLoad`/`unsplitLoad`, `totalCost`, `maxDemand` and `GoemansConjecture` match Ge–Xie–Li–Li (arXiv:2611.23244) Def. 2.1 (path flows over directed simple s–t_i paths), eq. (2.2)–(2.3) (arc loads, cost), Def. 2.2 with λ = 1 and Conjecture 2.4. Loads and admissibility over all pairs are equivalent to over arcs. The Lean conjecture quantifies over slightly more instances (terminals need not be distinct or ≠ s), but the counterexample is a valid instance of the paper's setting, so the refutation applies to the paper's conjecture.
- **Instance:** arcs, costs, demands (15,10,15) and path flows match §2.2.2 (Rybin's example).
- **Independent recheck:** own Python: 2 simple paths per terminal; fractional loads (10,6,24,14,10,5,9,4,5) as in eq. (2.6), cost 58; over all 8 unsplittable choices the 1-admissible ones cost 60, 90, 60, 60, so minimum 60.
- **Trust base:** no sorry/axiom/native_decide/set_option; small `decide` only; `#print axioms` added.
- **Required changes:** add the GUF-1 entry to ACHIEVEMENTS.md.

---

## 2026-11-27 · open-problems-lab PR #38 (Albertson–Berman conjecture disproof via G29 [AB-1], `Lab/AlbertsonBerman/`) · **pass, conditional on green `build` at f991235 and an ACHIEVEMENTS.md entry**

Internal audit, outside review welcome. Reviewed at f991235.

- **Statement:** `AlbertsonBermanConjecture` (every straight-line planar graph on n vertices has S with `(H.induce S).IsAcyclic` and n ≤ 2|S|) is the conjecture c_P ≥ 1/2 of Cames van Batenburg–Goedgebeur–Jooken (arXiv:2608.23260, Conj. 1.1) restricted to straight-line drawable graphs, so its negation refutes the original. `StraightLinePlanar` (injective map to ℝ², distinct edges' segments meet only at images of common endpoints) is a faithful straight-line plane drawing; the integer-orientation proof is sound.
- **Edge list:** parsed from the arXiv TikZ of the G29 figure (labels v0..v28): the 80 solid edges equal `Basic.lean` `edges` exactly; the dashed G'29 edge is correctly excluded.
- **Independent recheck:** own Python: planar, connectivity 2, {27,28} separates sides of size 12 and 15; exact integer check of the Lean coordinates (no crossings or touchings); CP-SAT with lazy cycle cuts gives a(G29) = 14.
- **Trust base:** no sorry/axiom/native_decide/set_option; `decide +kernel` facts only; `allSub_sound` read; `#print axioms` added for the three main theorems.
- **Required changes:** add the AB-1 entry to ACHIEVEMENTS.md.

---

## 2026-11-27 · open-problems-lab PR #34 (Chen–van der Holst–Luo–Ma odd-fold cover conjecture disproof [OFC-1], `Lab/OddFoldCovers/Petersen.lean`) · **pass, conditional on green `build` at f19dd94 and the merge time being filled in**

Internal audit, outside review welcome. Reviewed at f19dd94.

- **Statement:** faithful to Wang, arXiv:2611.13394, Conjecture 1.1: loopless G, odd ℓ ≥ 3, s_ℓ(G) = L_ℓ(G). `cover`, `sCyc` (sInf over voltages α : E → ℤ/ℓ), `L` (max of Δ and ⌈2ℓ|E(G[S])|/(ℓ|S|−1)⌉ over odd S, |S| ≥ 3), `IsProper` and `chromaticIndex` match the paper's definitions. F is Wang's F_ℓ(P) at ℓ = 3 (p = 4 parallel edges per triangle side, connecting edges a matching).
- **Proof:** read in full; follows Lemma 3.1 (every colour meets each lifted block's 9 leaving edges once) and the Section 4 spoke count (each class ≡ 1 mod 4 spokes, 9 classes vs total 15).
- **Independent recheck:** own Python/networkx: Petersen isomorphism, F has 30 vertices, 135 edges, 9-regular; min odd cut of P is 3 (all odd subsets) and of F is 3 (Padberg–Rao via Gomory–Hu), so L_3(F) = 9; P has 6 perfect matchings with 1 or 5 spokes.
- **Trust base:** no sorry/axiom/native_decide/set_option; small `decide`/`decide +kernel` facts only; `#print axioms` added for `not_conjecture`, `F_L`, `F_sCyc`.
- **Scope:** only ℓ = 3 and the lower bound s_3 ≥ 10 (sufficient to refute); general ℓ, G_ℓ and s_3 = 10 not formalized.
- **Required changes:** none beyond filling in the merge time.

---

## 2026-11-27 · open-problems-lab PR #32 (Bencs–Csikvári spanning-forest conjecture false, K_{a,b}, Wu–Lu–Dong [SF-1], `Lab/SpanningForests/Counterexample.lean`) · **pass, conditional on CI green + merge time filled in**

Internal audit, outside review welcome. Reviewed at 6a243b2.

- **Statement.** `numSpanningForests` counts the acyclic edge subsets on all of V, which is the paper's 𝓕(G). `Conjecture` is Conjecture 1.1 word for word: δ ≥ 3 implies F(G) ≤ ∏ deg, with no connectivity assumption.
- **Proof.** Star forests are acyclic and injective, so (a+1)^b ≤ F(K_{a,b}), which is the paper's argument. `prod_degree` gives b^a a^b.
- **Independent recheck.**
  - Exact integers show 4^38 > 38³·3³⁸, and the inequality fails at b = 37.
  - Brute force gives F(K_{3,3}) = 328 and F(K_{3,4}) = 1856, which agree with the Auditor's own block-decomposition count.
  - That count shows K_{3,14} is the smallest a = 3 counterexample (F = 13,186,891,776 > 13,124,466,936).
- **Trust base.** Grep clean, with no `decide` or `set_option`. Axiom lines added. Not built locally.
- **Note.** The K_{3,14} / Stark remark was not found in the arXiv text the Auditor read. The number is correct, so if the paper does not state it, attribute it to our own computation.

---

## 2026-11-27 · open-problems-lab PR #30 (sunflowers S_n disprove the Lalou–Mbarek–Skender–Togni bipanchromatic conjecture, Novaković–Jojić [BP-1], `Lab/Bipanchromatic/Sunflower.lean`) · **pass, conditional on CI green**

Internal audit, outside review welcome. Reviewed at a981afe.

- **Statement.**
  - `IsPanchromatic`, `uniqueVerts`, `chiP` and `chiB` (via `sSup`), `alphaK` (via `sInf`) and `alpha = alphaK chiP` match the paper's Definitions 1–3 and its `α = α_{χ_P}`.
  - For S_n every set is nonempty and bounded, so each value is a genuine max or min.
  - `Conjecture` adds the hypotheses |V| ≥ 2, E ≠ ∅ and hyperedges of size ≥ 2. These only shrink the class of hypergraphs, so the negation is stronger.
- **Proof.**
  - Re-derived by hand: injectivity on each hyperedge forces all s_i to be unique and all p_i to share a colour.
  - The colouring {s_i, p_i} ↦ i is bipanchromatic, and χ_B ≤ |V|/2.
- **Independent recheck.** Brute force over all colourings gives:
  - S₃: χ_P = 4, α = 3, χ_B = 3, against a conjectured 2.
  - S₄: χ_P = 5, α = 4, χ_B = 4, against a conjectured 3.
- **Trust base.** Grep clean, with no `decide` and no `set_option`; the axiom lines are added. Not built locally.
- **Nit.** arXiv calls this Theorem 1, while the docstring says Theorem 3.1.

---

## 2026-11-27 · open-problems-lab PR #28 (Aliabadi's 9 ∈ U₄ \ D₄, Chung–Graham–Spiro gap-set conjecture false [FW-1], `Lab/FibWalk/`) · **pass, conditional on CI green + merge time filled in**

Internal audit, outside review welcome. Reviewed at a443b66.

- **Statement.**
  - `IsDown` / `IsUp` are defined as "the CGS representation parameter t is even / odd". This is Aliabadi's working definition, from the CGS characterisation; slow walks themselves are not formalized.
  - The `∃` definitions agree with CGS's D and U because the representation is unique (CGS). The Auditor checked uniqueness by brute force for n < 20,000. Suggested ledger wording: say this explicitly.
  - `gapSet` via `Nat.nth`, with both sets proved infinite, is the increasing enumeration.
- **Proof.**
  - `shift` is a correct generalisation of the forward-8 and backward-5 lemmas (new representation `(a + f_r, b − f_{r+1})`).
  - `core` is closed real arithmetic (`linarith`, 10 × 2⁸ cases). `maxHeartbeats` is a resource limit only.
  - `downB` is proved correct below 377, and `decide` covers the windows with n ≤ 104.
- **Independent recheck.**
  - The up-integers begin 3, 4, 6, 8, 11, 14, 16, 17.
  - For n < 200,000: D₄ = {5,6,7,8,10,11,13,16,18} and U₄ = D₄ ∪ {9}.
  - A direct slow-walk computation for n < 250 agrees with t-parity in all 216 unambiguous cases.
- **Trust base.** Grep clean apart from `maxHeartbeats`; no `native_decide`; axiom lines added. No local build.
- **Required.** Fill in the ACHIEVEMENTS merge time.

---

## 2026-11-27 · open-problems-lab PR #27 (T₃ = Cat(8,7,25) has χ_la = 43, Brondani–França Thm 4.1 [LA-2], `Lab/LocalAntimagic/T3.lean`) · **pass, conditional on CI green + merge time filled in**

Internal audit, outside review welcome. Reviewed at 785f65f.

- **Statement.**
  - `Cat d3` with degrees (9, 9, 26) is exactly Cat(8, 7, 25).
  - `T3` proves the following: it is a tree with 43 vertices, 40 leaves and chiLA = 43.
  - Both directions of the `sInf` are proved (nonempty set, and every local antimagic labelling has 43 weights).
- **Existence (replaces the Haslegrave citation).**
  - Only `a–b` is not separated by the degree bounds (leaves ≤ 42 < 45; U(9) = 342 < 351 = L(26)).
  - If `wt a = wt b`, swapping the labels x ≠ y of a leaf edge at `a` and one at `b` separates them by 2|x − y|.
  - The Auditor checked this by hand.
- **Independent recheck.** 19,855 of 20,000 random bijections are local antimagic, and all of them have exactly 43 distinct weights. The paper's intervals [45, 342] and [351, 767] were confirmed.
- **Trust base.** Grep clean; axiom lines added. No local build.
- **Required.** Fill in the ACHIEVEMENTS merge time.

---

## 2026-11-27 · open-problems-lab PR #24 (Lean disproof of the local antimagic leaf conjecture, Brondani–França Thm 5.2 (r ≥ 2) + Cor 5.3 [LA-1], `Lab/LocalAntimagic/`) · **pass, conditional on CI green + merge time filled in**

Internal audit, outside review welcome. Reviewed at f5c817d.

- **Statement.**
  - Labelling `G.edgeSet ≃ Fin m` with label `f e + 1`, so labels are exactly 1..m. `wt` sums over incident edges only.
  - `chiLA` is an `sInf`: an empty set would give 0, which only weakens the conjecture, so the disproof is safe. Here the set is nonempty.
  - `LeafConjecture` is Conjecture 2.2 exactly: trees with ≥ 3 vertices, arbitrary decidability instances.
  - `Separated` is the paper's degree separation, specialised to increasing degrees.
- **Independent recheck.**
  - Lean's `Separated` holds numerically for H_{r,t}, r = 2..5, t = 1..5. H_{3,1} has m = 20734, and its intervals match the paper.
  - 20,000 random bijections on the small separated caterpillar (6, 14) gave all-distinct weights.
  - The arithmetic (4)–(8) was re-derived by hand.
- **Trust base.** Grep clean across the three files; axiom lines added. No local build.
- **Notes.** The non-isomorphism clause of Thm 5.2 is not stated (it follows from the vertex count). r = 1, T₃ and T₄ are not covered, as the ledger says. **Required:** fill in the ACHIEVEMENTS merge time.

---

## 2026-11-27 · open-problems-lab PR #23 (Lauri's whole family G_{d,k}: gap χ_= − L unbounded on connected block graphs [BEQ-2], `Lab/BlockEquitable/Family.lean`) · **pass, conditional on CI green + merge time filled in**

Internal audit, outside review welcome. Reviewed at e9b1396.

- **Statement.**
  - `lauri_family` (d ≥ 2, k ≥ 4d − 1): connected block graph with L = k and χ_= = k + d.
  - `gap_unbounded C`: L + C < χ_= for some connected block graph.
  - Both use the BEQ-1 definitions (audited, PR #19). `adjR` matches the paper's construction, and `card_V` gives 4(k + d − 1).
- **Independent recheck.**
  - The Lean colouring `f`/`col`, ported verbatim, is proper and equitable for all d = 2..8 and k = 4d−1..4d+24 (168 cases).
  - On the Auditor's own graph built from the paper, for (d, k) = (2,7), (2,8), (2,10), (3,11), (3,12), (4,15):
    - networkx: blocks are all cliques, ω = k, α_min = 4, L = k.
    - CP-SAT: no equitable (k+d−1)-colouring; an equitable (k+d)-colouring exists.
- **Trust base.** Grep clean. The arguments are general (no `decide` over d, k). Axiom lines added. No local build.
- **Suggested.** arXiv v1 numbers the result Theorem 2 and the colouring Lemma 8, while the PR says Theorem 1.1 and Lemma 7; please align. **Required.** Fill in the ACHIEVEMENTS merge time.

---

## 2026-11-27 · open-problems-lab PR #21 (List Total Colouring fails for every k ≥ 4, generalised Noel graph [LTC-2], `Lab/ListTotal/General.lean`) · **pass, conditional on CI green**

Internal audit, outside review welcome. Reviewed at d39192b.

- **Statement.** `exists_counterexample k` (k ≥ 4) gives a finite simple graph with all degrees ≤ k − 1, `totalChromaticNumber = k`, not
  `TotalChoosable k`, using the LTC-1 definitions. The `d + 1` dummy vertices `(i, inr i)` are isolated (checked in `gAdj`) and get nonempty
  lists, so they affect neither χ'', nor choosability, nor degree. The `Sym2.lift` edge lists are well defined (`eL_symm`), and `degree_le`
  counts true neighbours.
- **Proof (re-derived by hand).**
  - `priv_eq`: an injective map from d − 1 private vertices to d − 2 terminals is impossible.
  - `block`: a cross edge has colour in {i, s_i}.
  - `star`: pairwise-meeting 2-sets over ≥ 4 indices form a star.
  - The `om` table covers every colour t with an edge {p, q} where t ∉ {p, q}.
- **Independent recheck.** The Auditor's own CP-SAT script, built from the docstring, covers d = 3, 4, 5 (20, 35, 54 vertices, d-regular):
  - no total d-colouring;
  - a total (d+1)-colouring exists;
  - the bad lists are infeasible.
- **Trust base.** Grep clean; axiom lines added. No local build (no Lean toolchain in the Auditor's container).
- **Docs.** Novelty is hedged appropriately. The PLC closure fact (k, ℓ) → (k, mℓ) was checked.
- **Required changes.** None.

---

## 2026-11-27 · open-problems-lab PR #19 (Lean disproof of the DFM gap-one conjecture for equitable colouring of block graphs [BEQ-1], `Lab/BlockEquitable/Counterexample.lean`) · **pass, conditional on CI green + 1 fix**

Internal audit, outside review welcome. Reviewed at c734344.

- **Statement.**
  - `IsBlockGraph` says every 2-connected induced subgraph is complete (∅, singletons and 2-sets are handled correctly), which is equivalent to "every block is a clique".
  - `αAt`, `αmin`, `L` (ceiling as `(n+1+α)/(α+1)`) and `IsEquitableColoring` (every class of `Fin q` has size between ⌊n/q⌋ and ⌈n/q⌉) match Lauri, arXiv:2608.14517, word for word.
  - `GapOneConjecture` is restricted to connected block graphs, so its negation is stronger than the original (every block graph).
- **Independent recheck.**
  - The Auditor built the graph from the paper's description; its edge set equals the Lean `adjR`.
  - networkx: connected; blocks of sizes [2, 7, 7, 7, 7, 7], all cliques; ω = 7; α_min = 4; L = 7.
  - CP-SAT: equitable q-colourings are infeasible for q = 7 and 8 and feasible for q = 9, so χ_= = 9.
- **Trust base.** The grep is clean. `decide` / `decide +kernel` only. The axiom lines were added. There was no local build (no Lean toolchain in the Auditor's container).
- **Required change.** ACHIEVEMENTS "(merge time TBD)" must become the real time. Suggested: "smallest one" → "smallest graph in his family".

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

## 2026-11-28 · Claim IDC-1 (Henning–Yeo identifying vertex cover conjecture, Wang's `H_{t,r}`, PR 51) · **pass with notes**

In-house Auditor (independent subagent).
- Statement fidelity: `IsIdCover` (covers every edge, equal traces force equal edges) and `idCoverNumber` (sInf over a
  nonempty set, `isIdCover_univ`) match Henning–Yeo; `HenningYeoConjecture` is the full bound over all finite graphs in ℚ.
  `adjB`/`H` match Wang's `H_{t,r}` (non-edges checked by `decide`). Main theorems also give connectivity and `Δ = t + r`.
- Trust surface: no sorry/axiom/native_decide/implemented_by/extern/unsafe/opaque. `#print axioms`: propext,
  Classical.choice, Quot.sound only. `leanchecker` passed.
- Own brute force: `τ_D = n − 1` and excess `(t−1)(r−1)/(Δ²+1)` for six `(t, r)`; `t = 1` or `r = 1` give equality.
- Notes (fixed in this PR): ACHIEVEMENTS wording (the excess is fractional, 7 vs ≈ 6.94), "Internal audit" line,
  ledger margin wording and status.

## 2026-11-28 · Claim SAT-1 (TxGraffiti μ* ≤ H, friendship graphs, Gupta Thm 1) · **pass**

In-house Auditor (independent subagent).
- Statement fidelity: `IsMatching`/`IsMaximalMatching` standard; `saturationNumber` is `sInf` over sizes (every finite
  graph has a maximal matching, so a true minimum); `harmonicIndex` sums `2/(d(u)+d(v))` over `edgeFinset` in ℚ;
  `TxGraffitiConjecture` = connected with ≥ 2 vertices. `F`/`adjB` is exactly `F_k`.
- Trust surface clean; `#print axioms` on the four main theorems: propext, Classical.choice, Quot.sound only.
- Own brute force `k = 1..6` (exact fractions): μ* = k, H = 2k/(k+1) + k/2, counterexample iff k ≥ 4.
- Optional note: the 9-vertex minimality is Gupta's computation, not proved in Lean (docstring attributes it).

## 2026-11-28 · Claim BOND-1 (Teschner's bondage-number conjecture, Yavari's 18-vertex graph) · **pass with notes**

In-house Auditor (independent subagent).
- Statement fidelity: `IsDominating`, `dominationNumber`, `bondageNumber` (strict increase of γ), `TeschnerConjecture`
  (nonempty edge set, ℚ comparison with `maxDegree`) faithful; the `sInf` sets are shown nonempty, so nothing rests on
  `sInf ∅ = 0`. Edge list matches the paper; `nb` checked by `mem_nb`; certificate data `Ls` re-validated by `validL_eq`.
- Logic of `isDominating_of_survB`, `dominationNumber_delete_le` (repeated sorted indices cover |F| < 4),
  `seven_le_dominationNumber_F5`, `bondageNumber_eq` checked.
- Trust surface clean; axioms propext, Classical.choice, Quot.sound only; leanchecker exit 0 on sampled modules.
- Own brute force: cubic, connected, bipartite; γ = 6 (297 minimum sets); γ(G − F) ≤ 6 for all 17,550 four-edge F;
  γ(G − F5) = 7.
- Notes (fixed in this PR): comment explaining `GPart0`'s import of `QPart19` (single import chain for CI memory);
  `explorer/bondage/gen_quads.py` committed with the Lean files.

## 2026-11-28 · open-problems-lab PR #53 (FW-4: `D_8 ≠ U_8`, `D_9 ≠ U_9`, `Lab/FibWalk/UpOnly/`) · **pass with notes**

In-house Auditor (independent subagent).
- Statements: `gapSet_ne_uo8/uo9 : gapSet IsDown ℓ ≠ gapSet IsUp ℓ` (ℓ = 8, 9) use the unchanged FW-1 definitions.
  `up_only_mem_up8/9` (17 ∈ U_8, 25 ∈ U_9) come from a `decide +kernel` witness via the audited `isUp_iff_ut`.
  `up_only_not_mem_down8/9` cover all k: a kernel table for d_k < 105, and a generated case tree with window
  lemmas for d_k ≥ 105.
- Independent recomputation (exact integers, n ≤ 10^6): the representation is unique; up-integers 25…42 are 9
  consecutive (span 17) and 30…55 are 10 consecutive (span 25); no 9 (resp. 10) consecutive down-integers span 17
  (resp. 25). Side observation: ℓ = 8 also has 27 ∈ D_8 \ U_8.
- Trust: no sorry, admit, axiom, native_decide, implemented_by or unsafe in the new files. Axioms are propext,
  Classical.choice, Quot.sound. `leanchecker` passes on L8Main, L9Main, Shift13 and all five Patterns modules.
- Shift13: θ₇ = (17φ−26)/5 satisfies θ₇√5φ⁶ = φ⁵+1 (checked by proof and numerically). `shift'` applies with
  j = 7 because down N ≥ 105 has t ≥ 8 (`eight_le_of_rep`).
- Notes (fixed in this PR): (a) "n down iff {φn} < c(n)" was called exact; it is now marked heuristic and checked
  numerically only. check_rule.py checks only the per-family rule, and the "families tile without gaps" sentence was
  wrong as written. (b) "max D_ℓ = max U_ℓ for every ℓ checked" fails from ℓ = 115 at the cutoff; now restricted.
  (c) The list of Lean-proved ℓ in valleys.md now includes 9. check_rule.py is now described as "high-precision".
- No claim that infinitely many ℓ is proved; the ℓ = 12…300 differences are marked as evidence.


## 2026-11-28 · Claim TH-1 (all-n exact codegree conjecture for tight Hamiltonian cycles, Ferudun's H_k, k = 3, 4, 5) · **pass with notes**

In-house Auditor (independent subagent).
- Statement fidelity: `codegree`, `window` (indices mod `n`), `HasTightHamiltonCycle` (bijection `Fin n → V`),
  `CodegreeConjecture` (k ≥ 3, n ≥ k + 1, k-uniform, bound `(n − k + 3)/2` in ℕ: no truncation since n ≥ k + 1)
  faithful to RRS 2011 Conj. 1.1; `Dface` is Ferudun's D′ shifted by one; `E k` is exactly `H_k`. Not vacuous.
- Logic of `no_tight_cycle`, `codegree_E_eq`, `forced5` (cases 7–8 vacuous), `H_counterexample` checked. The kernel
  checks the conclusion of Lemma 2.4 over every apex position set, independent of the paper's gap-vector proof.
- Trust surface clean; axioms propext, Classical.choice, Quot.sound only; all 8 files compile from source.
- Own brute force: k = 3, 4, 5 give 25, 50, 96 edges, min codegree 3 = bound, 0 tight Hamiltonian cycles.
- Notes (fixed in this PR): minimality of `H₃` attributed to Ferudun's search; "modeled on Lemma 2.4" wording; Zhang
  citation clarified; "Internal audit" line.

## 2026-11-28 · Claim GHT-1 (Goddard–Henning Conjecture 32, Kwon–Park–Sano's 36-vertex triangulation) · **pass with notes**

In-house Auditor (independent subagent).
- Statement fidelity: planar triangulation = straight-line planar drawing (AB-1's `StraightLinePlanar`) plus exactly
  `3n − 6` edges, `n ≥ 4`; conclusion in the partition form, implied by the original colouring form. Not vacuous.
- Graph: rebuilt `B` from the paper's TikZ edge list of `G₁₄` and the Section 3 gluing; identical to `edges`
  (36 vertices, 102 edges). The integer drawing re-checked exactly (no crossings or overlaps).
- Logic of `partnerColoring_of_partition`, `lemma31` (hypotheses parsed: exactly the 36 edges of `G₁₄`, `N(v₃)`,
  `N(v₅)`, `N(v₉)`, partner edge `v₀v₂`), `nbr_i_j`, `no_partner_coloring_B`, `triangle`, drawing proof,
  `card_edgeFinset_B` checked. `set_option synthInstance.*` in Lemma.lean only raises instance-search limits.
- Trust surface clean; axioms propext, Classical.choice, Quot.sound only.
- Own brute force: Lemma 3.1 over all 4^14 colourings of `G₁₄`; `B` has 41,472 proper 4-colourings, 0 partner
  colourings, and 0 colourings in partition form (tested directly).
- Notes (fixed in this PR): ACHIEVEMENTS says only `n = 36` is formalized, "Internal audit" line, clearer wording;
  audit script docstring corrected.

## 2026-11-28 · open-problems-lab PR #57 (EJ-1..4: Edmonds–Johnson, `A₆`, `A₆⁺`, `A₇`, `Lab/EdmondsJohnson/`) · **pass with notes**

In-house Auditor (independent subagent).
- Statements: `poly`, `chvatalClosure` (all `w ∈ ℤⁿ`, all real valid `δ`), `integerHull`, `HasEJProperty` match
  Del Pia §1; `IsTHM` matches the paper's definition. `A6`, `A6plus`, `A7` match §1/§6 entry for entry; `A₆`'s
  data match (3). Nothing vacuous.
- Logic: `mem_chvatalClosure_of_witness`, `mem_chvatalClosure_of_int` (`3k ≤ w·y + 2 ⇔ k ≤ ⌈w·y/3⌉`),
  `integerHull_le` and `isTHM_of_certs` (`Tuple.sort`, `inv_submatrix_equiv`, kernel vector ⇒ det 0,
  `SN = 2I ⇒ S⁻¹ = N/2`) are correct; table sizes right (791 for `A₇`).
- Trust: no sorry, admit, axiom, native_decide, implemented_by or unsafe; axioms propext, Classical.choice,
  Quot.sound; leanchecker exit 0 on sampled modules.
- Own recomputation: `z ∈ P`, `z ∉ P_I` (LP over integer points), no violated `{0,½}`-cut, no violated CG cut for
  `w ∈ [-3,3]⁶` / `[-2,2]⁷`, THM by exact inverses, minor closures 3,387 / 4,873 / 5,155 (without the empty
  matrix), no `A₃`/`A₄`, none of the three a minor of another.
- Notes (fixed in this PR): PR title no longer says "counterexamples in Lean" (no-minor clause is not Lean);
  EJ-3 credits the claims to Del Pia §6 (our proofs and data, not new results); `<` → `≤` and a softened
  generality sentence in the ledger; EJ-4 counts say they include the empty matrix; Axioms re-run after merging
  main.
