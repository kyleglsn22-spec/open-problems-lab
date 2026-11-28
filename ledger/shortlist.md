# Shortlist, 2026-11-25

Ten candidates, checked against Tao's optimization-constants repository (commit cloned
2026-11-25), DeepMind's formal-conjectures (commit 9097e2f) and the list of Erdős problems
AlphaProof Nexus attempted. "2026 activity" counts how often 2026 work is cited on the
constant's page; high means crowded, often by other AI-assisted teams.

| # | Problem | Gap today | Handle | 2026 activity | Verdict |
| --- | --- | --- | --- | --- | --- |
| 1 | Erdős #757 = constant C5b: Sidon subsets of (4,5)-sets | 9/17 ≈ 0.529 to 4/7 ≈ 0.571 | Lean statement exists; DeepMind did not attempt it; the known bounds (1/2 and 3/5) are still unproved in Lean upstream; exact small cases public | Low (3) | **Pick: proof + Lean** |
| 2 | Constant C37, degree vs sensitivity exponent | log3 6 ≈ 1.631 to 2 | A degree-5 Boolean function with sensitivity 14 would beat the 15-year-old Kushilevitz barrier. Degree 4 was just ruled out (Koshta 2026); degree 5 is a finite LP/ILP search with exact certificates | Low (2) | **Pick: computation** |
| 3 | Constant C44, relevant variables, lower bound | 3/2 to 4.358 | Find degree-4 Boolean functions with 25 or more relevant variables (R_4 ≥ 25 beats 3/2). Upper side is crowded; lower side untouched | Upper side active, lower side quiet | Strong backup |
| 4 | Constant C27b, Earth–Moon problem (biplanar chromatic number) | 9 to 12, unchanged since 1980 | SAT search for a 10-chromatic biplanar graph; any find is exactly checkable | None | Long shot, cheap to try |
| 5 | Constant C30, Stanley–Wilf limit of 1324 | 10.27 to 13.5 | Transfer-matrix and enumeration methods; needs real expertise | None | Later |
| 6 | Constant C90, covering systems with large minimum modulus | 44 to 615,999 | Construct a covering with minimum modulus 45; very hard search | Moderate, record set in 2026 | Skip for now |
| 7 | Constant C9, Shannon capacity of the 7-cycle | 3.25883 to 3.3177 | Independent-set constructions | High, 5 records in 2026 | Skip, crowded |
| 8 | Constant C89b, Ramsey multiplicity of K5 | 0.001524 to 0.001649 | Step-graphon search | High, AI teams racing | Skip, crowded |
| 9 | Constant C31a, Chvátal–Sankoff (binary) | 0.7927 to 0.8241 | Huge automata, heavy compute | High | Skip, crowded and costly |
| 10 | Pool: open Erdős problems stated in Lean that DeepMind did not attempt | 348 problems | Scout triage for the next round, cross-checked against erdosproblems.ai and OpenAI's October release | Varies | Triage next |

## Why these two

- **Erdős #757** gives the Formalizer a realistic first win: the upstream Lean bounds are
  still `sorry`, and the upper bound reduces to one explicit 12-element set (a published
  small case has largest Sidon subset 7, so the supremum is at most 7/12 < 3/5). The open
  question itself, closing 9/17 to 4/7, is a genuine research target for the Prover and
  Explorer.
- **C37 at degree 5** is a sharp yes/no computational question with a clear payoff. Either
  answer is a result: a function improves a long-standing bound; an impossibility
  certificate extends the 2026 degree-4 result.

Both still need the Scout's full literature check before work starts (logged in their ledgers).

## Round 2 (2026-11-26, roadmap item 4)

- C44 lower side (row 3) dropped: Pinho (Nov 2026, rpinho/c44-certificate) claims R_4 = 22 exactly and
  C44 < 1.99, so the degree-4 search is settled and the constant is crowded.
- Scanned Tao's constants with no 2026 activity and the open Erdős problems with few forum posts.
  **Picked Erdős #1186 (second part): fewest monochromatic 4-APs in 2-colourings of Z_p.** Gap 7/96 to
  17/150 untouched for primes since 2012, exact finite certificates possible. See `ledger/erdos-1186.md`.

## Round 3 (2026-11-26)

- Picked the **van Emde Boas–Kruyswijk conjecture** (Davenport constant of `C_n^r`, related to Tao
  constant 53a). A preprint of 18–24 Nov 2026 (Gao–Geroldinger–Wang–Zeng) disproves it with an
  explicit construction; nobody has machine-checked it. Payoff: first formal disproof of a 1969
  conjecture. See `ledger/davenport-vebk.md`.

## Round 4 (2026-11-26, scouting thread)

Scanned arXiv/Hexagon/Zenodo for disproofs and new theorems from September to November 2026, then checked each
one against the AFTD auto-formalization site (rainwangphy/aftd-platform, about 28k Lean files, which formalizes new arXiv
papers within days), formal-conjectures and GitHub. Ranked by likely payoff for us:

| # | Candidate | Source | Why | Formalized elsewhere? | Plan |
| --- | --- | --- | --- | --- | --- |
| 1 | **List Total Colouring Conjecture is false** (Borodin–Kostochka–Woodall, Juvan–Mohar–Škrekovski, Hilton–Johnson, late 1990s) | Noel, arXiv 2609.38417 (29 Sep 2026), counterexample found by an AI model | Well-known conjecture; explicit 20-vertex cubic graph with total chromatic number 4 but not total 4-choosable; short hand proof | No (not on AFTD; press coverage says no formal proof) | **Pick: Lean disproof now** |
| 2 | **Non-abelian Gyarmati–Matolcsi–Ruzsa inequality is false** (GMR 2010, Problem 1.3) | Nair–Namayandeh–Zhu arXiv 2611.00156 (D_4^14); Elsholtz arXiv 2611.12776 (general double-coset theorem, smallest n=4 group found has order 518,400, "no minimality claimed") | Lean: the general double-coset theorem only needs a lower bound on the product set and upper bounds on the slices. Search: a smaller group for 4 sets would beat a published record | No | **Done (GMR-1):** Lean disproof in a new group of order 2^17 = 131,072 (beats published 518,400); see ledger/gmr-non-abelian.md. Open lead: sparse template in non-class-two groups |
| 3 | Claw-free Schur-positivity conjecture (Stanley 1998 / Gasharov) is false | Prajapati arXiv 2607.26364; Matherne–Morales | 12-vertex graph, one Schur coefficient equals -64 | No | **Done (CF-1):** Lean disproof, `not_clawFreeSchurPositivity` (Lab/ClawFree/); see ledger/claw-free-schur.md. By the paper's computer census (not re-checked by us), 12 vertices is the minimum. Second minimal example (coefficient −40) also done (CF-2). Open lead: the infinite families of arXiv 2607.27166 |
| 4 | Partial List Colouring Conjecture (Albertson–Grossman–Haas) is false | Noel arXiv 2609.23291 | Same author and style as #1 | No (not on AFTD or formal-conjectures, checked 2026-11-27) | **Done (PLC-1):** Lean disproof, `not_partialListColouringConjecture` (Lab/PartialList/); see ledger/partial-list-colouring.md. New lead: Noel asks for *connected* counterexamples with a large gap (disjoint copies only inflate it); a small computer search is a natural hard follow-up |
| 5 | Gerards–Schrijver Edmonds–Johnson conjecture is false | arXiv 2611.28580 (20 Nov 2026), a 5×6 matrix | Very fresh | AFTD cites it once | **Done (EJ-1 to EJ-4, 2026-11-28, hard slot):** the closure step was done without LP duality (primal witness criterion plus a 9-point integer check); `A₆`, `A₆⁺`, `A₇` fail EJ and are THM in Lean; no-minor clause computer-checked only. See ledger/edmonds-johnson.md. Earlier note: **Moved to the hard list (2026-11-27):** the disproof needs Lean proofs that a point lies in the Chvátal closure, which the paper gets from the Appa–Kotnyek theorem (THM matrices: the closure equals the {0,½}-closure; needs LP duality and basic-solution theory, absent from Mathlib), plus a theory of matrix minors (pivots, halving). The elementary parts (THM of the 5×6 matrix, the point violates a valid inequality of the integer hull, the nine slack-⅓ sides are distinct mod 2) are easy; the closure step is a multi-week project. AFTD lists only the paper's open Question 6.1 |

Dropped: **Hilton's conjecture** (proved arXiv 2611.12199): AFTD already has a Lean proof (11 Nov) and Bai (Zenodo
24152331) Lean-proved the follow-up conjecture. Also dropped: El-Zahar–Erdős (probabilistic proof, hard to formalize) and
the happy-edge conjecture (flip-distance lower bounds, heavy).

## Round 5 (2026-11-27, easy slot)

Scanned arXiv disproofs from August to November 2026 against the AFTD knowledge base and formal-conjectures.

| # | Candidate | Source | Formalized elsewhere? | Plan |
| --- | --- | --- | --- | --- |
| 1 | Gap-one conjecture for equitable colouring of block graphs (Dybizbański–Furmańczyk–Mkrtchyan 2024) is false | Lauri, arXiv 2608.14517 | No (not on AFTD) | **Done (BEQ-1):** Lean disproof for `G_{2,7}`; see ledger/block-equitable.md. Whole family `G_{d,k}` (unbounded gap) also done (BEQ-2). Open lead from the paper: a multiplicative bound `χ_= ≤ C·L` (hard) |
| 2 | Local antimagic chromatic number, leaf conjecture (`χ_la(T) ≤ ℓ(T) + 2` for trees) | Brondani–França, arXiv 2610.22783 | No | **Done (LA-1):** Lean proof of their Theorem 5.2 (r ≥ 2) and Corollary 5.3; see ledger/local-antimagic.md. Theorem 5.2 (caterpillars `H_{r,t}`, every labelling antimagic, `χ_la = ℓ + r`) |
| 3 | Gap sets in the CGS setting | arXiv 2609.04473 | No | **Done (FW-1):** self-contained Lean proof of `9 ∈ U_4 \ D_4`; see ledger/fib-walk-gaps.md. Open lead from the paper: is `D_3 = U_3`? (hard list) |
| 4 | Oxley's circuit–cocircuit question, via the Golay matroid | arXiv 2610.06033 | No | Heavy: Mathlib has no representable matroids |
| 5 | Dominating Hadwiger conjecture | arXiv 2609.35361 | No | Probabilistic; hard list |
| 6 | Weighted union-closed variant | arXiv 2609.25101 | No | Asymptotic; hard list |

Dropped: Wormald's conjecture disproof (arXiv 2610.00086), already Lean-checked by its authors.

## Round 5 leads (2026-11-27, hard slot)

| # | Lead | Source | Status |
| --- | --- | --- | --- |
| 1 | Partial List Colouring for lists 2+ colours short (`ℓ ≤ k − 2`, `ℓ ∤ k`; first cases `(5,2)`, `(5,3)`) | raised by PLC-3 (ours) | Attempted. Noel-type terminal designs provably fail (ledger/partial-list-colouring.md, Dead ends). Needs a new idea; parked |
| 2 | List Total Colouring: counterexamples for every maximum degree `Δ ≥ 3`, or a gap `χ''_ℓ ≥ χ'' + 2` (Noel asks whether `χ''_ℓ ≤ χ'' + 1` always; gap 3 would disprove the List Edge Colouring Conjecture) | Noel, arXiv 2609.38417, closing remarks | Every-Δ half DONE (LTC-2, Lean, all Δ ≥ 3). Gap ≥ 2 attempted 2026-11-27: necessary conditions plus small searches, nothing found (ledger Dead ends); parked |

## Hard list additions (2026-11-27)

- **Multiplicative bound for equitable colouring of block graphs** (open question in Lauri, arXiv 2608.14517): is there
  a constant `C` with `χ_=(G) ≤ C · L(G)` for every connected block graph? Lauri's family (Lean-checked, BEQ-1/BEQ-2)
  forces `C ≥ 9/7`, and `C ≥ 5/4` asymptotically. A proof or a family beating `9/7` would be new.
  Attempted 2026-11-27: an elementary 7-vertex tree already gives `C ≥ 3/2`; Lauri-type obstructions look capped;
  searches found nothing above 3/2 (ledger/block-equitable.md). Parked.
- **`D_3 = U_3` for slow Fibonacci walks** (open question in Aliabadi, arXiv 2609.04473): do the 3-step gap sets of
  down- and up-integers agree? **Not open after all (checked 2026-11-28):** Mao–Zhao (arXiv 2608.19886, Aug 2026,
  Theorem 1.2) proved `D_3 = U_3 = {3,4,5,6,7,8,10,11,13}` on paper. **Done (FW-2):** our own Lean proof, with the FW-1
  machinery plus up-integer shifts; see ledger/fib-walk-gaps.md. Still open: does `D_ℓ ≠ U_ℓ` for infinitely many `ℓ`?

## Round 6 easy-slot scouting (2026-11-27)

Fresh arXiv disproofs checked against AFTD: already formalized there: Gao–Gu weighted Catalan (2611.26953), Tokareva
bent sums (2610.32239), Borg intersecting partitions (2610.01747). Not formalized:

| # | Candidate | Source | Plan |
| --- | --- | --- | --- |
| 1 | Bipanchromatic conjecture (Lalou et al.) | Novaković–Jojić 2610.27133 | **Done (BP-1):** sunflowers `S_n`, all `n ≥ 3`; see ledger/bipanchromatic.md |
| 2 | Triangle-free planar graphs need not be POSH | 2611.32999 | Planar embeddings; heavy |
| 3 | Chen–van der Holst–Luo–Ma conjecture on edge-colouring odd-fold covers (Petersen-based counterexample) | 2611.13394 | **Done (OFC-1):** `F_3`, `L_3 = 9`, `s_3 ≥ 10`; see ledger/odd-fold-covers.md |
| 4 | Jiang–Zhu relaxed multiplication in list colouring (91-vertex graph) | 2611.03151 | Choosability; heavy |
| 5 | Bencs–Csikvári spanning-forest conjecture `F(G) ≤ ∏ deg(v)` (min degree ≥ 3) | Wu–Lu–Dong 2611.18076 | **Done (SF-1):** `K_{3,38}` and `K_{a,4a³}` for all `a ≥ 3`; see ledger/spanning-forests.md |

Also already formalized (skip): Costas-array conjecture disproof 2611.00098 (authors' own Lean proof).

## Hard slot, 2026-11-27 evening
| Candidate | Source | Status |
| --- | --- | --- |
| Albertson–Berman ratio `c_P ≤ 25/52` (Problem 5.1) and Chappell–Pelsmajer `d = 2..6` (Problem 5.3) | 2608.23260 | Attempted: gadget calculus and searches, no improvement; see ledger/albertson-berman.md. Easy slot: **Done (AB-1)**, Lean disproof of the conjecture itself via `G₂₉` |
| Petersen colouring: smallest counterexample, gap `40 ≤ n ≤ 52` | 2608.10028 | Attempted 2026-11-28: SAT tooling, replacement searches in `G52` and random assemblies, nothing below 52; see ledger/petersen-colouring.md. Needs exhaustive weak-snark generation; parked |
| Non-cancelling intersections: smallest lattice without a winning tree | 2608.27416 | Not started (small primes `p = 5, 7` look unhelpful) |

## Round 7 easy-slot scouting (2026-11-28)

Fresh disproofs checked against AFTD (kb generated 2026-11-27):

| # | Candidate | Source | Formalized elsewhere? | Plan |
| --- | --- | --- | --- | --- |
| 1 | Goemans's unsplittable-flow conjecture (7-vertex network) | Ge–Xie–Li–Li 2611.23244 | AFTD: definitions only, no theorem | **Done (GUF-1):** Lean disproof; see ledger/goemans-unsplittable.md |
| 2 | Mizzi's conjecture on unstable graphs, v1/v2 statement (10-vertex counterexample) | 2608.15281 | No | **Done (UG-1):** Lean disproof of the v1/v2 statement (Mizzi's current version, for asymmetric graphs, stays open); see ledger/unstable-graphs.md |
| 3 | Bougard–Joret conjecture, smallest case `(n, α, k) = (7, 3, 4)` | 2608.18828 | No | **Done (BJ-1):** Lean disproof of the first regime; see ledger/bougard-joret.md |
| 4 | Domination vs edge domination in cubic graphs (50 vertices, `γ = 16 > 15 = γ_e`) | 2609.10783 | No | Checked 2026-11-28: `γ ≥ 16` needs a ~500k-node branch-and-bound even with fractional pruning (paper: 2^20 enumeration or 893k-node tree); too heavy for kernel `decide` without a better certificate |
| 5 | Harper-norm silver-mean conjecture (explicit rational point) | 2611.23265 | No | Checked 2026-11-28: needs operator norms on `ℓ²(ℤ)` and the Gerhold–Shalit reduction `E(p/q) = λ_max(H_{p/q})` for every phase; too heavy for the easy slot |
| 6 | Hinrichs–Vybíral conjecture on positive definite functions (7-dim explicit example) | Vybíral 2609.21733 | No | **Done (HV-1):** Lean disproof, audited; see ledger/hinrichs-vybiral.md |
| 7 | `D_3 = U_3` for slow Fibonacci walks (taken from the hard list, but already proved) | Mao–Zhao 2608.19886, Thm 1.2 | No (AFTD: not listed) | **Done (FW-2):** Lean proof, audited; see ledger/fib-walk-gaps.md |
| 8 | (hard slot) `D_ℓ ≠ U_ℓ` for more `ℓ` | ours | n/a | **Done (FW-3, new):** Lean proof of `D_7 ≠ U_7`, audited; certified evidence up to `ℓ = 24` |

Hard slot (2026-11-28): Mizzi's current conjecture (asymmetric unstable graphs) was attempted. There is no asymmetric unstable graph on ≤ 9 vertices (exhaustive search), and random two-fold-automorphism search produced no asymmetric graphs. Parked until `geng` is available for n = 10; see explorer/unstable-asymmetric/.

Also seen: the quantum Hedetniemi counterexample 2609.20690 is already Lean-checked by its authors (skip).

## Round 8 easy-slot scouting (2026-11-28)

Fresh disproofs checked against AFTD (kb generated 2026-11-27):

| # | Candidate | Source | Formalized elsewhere? | Plan |
| --- | --- | --- | --- | --- |
| 1 | Henning–Yeo identifying vertex cover bound (family `H_{t,r}`, smallest has 8 vertices) | Wang 2608.19455 | No | **Done (IDC-1, PR 51):** Lean disproof of the whole family, every `Δ ≥ 4`; see ledger/identifying-vertex-cover.md |
| 2 | Erveš–Tepeh conjectures on (1,2)-domination vs induced cycles in cubic graphs (counterexamples on 18–22 vertices, family `H(k)`) | Knor–Sedlar–Škrekovski 2608.17851 | No | Candidate |
| 3 | TxGraffiti saturation number vs harmonic index (friendship graph `F_4`, 9 vertices) | Gupta 2606.15761 (after Bıyıkoğlu) | No | **Done (SAT-1, PR 52):** Lean disproof, all `F_k`, `k ≥ 4`; see ledger/saturation-harmonic.md |
| 4 | Teschner's bondage-number conjecture `b(G) ≤ (3/2)Δ` (cubic bipartite graph on 18 vertices, `b = 5`) | Yavari 2609.04257 | No | **Done (BOND-1, PR 54):** Lean disproof; see ledger/bondage-number.md |
| 5 | Rödl–Ruciński–Szemerédi exact codegree conjecture for tight Hamiltonian cycles, all-`n` form (7-vertex 3-graph `H₃`, also `k = 4, 5`) | Ferudun, Zenodo 10.5281/zenodo.23006717 (Sep 2026) | No | **Done (TH-1, PR 56):** Lean disproof for `k = 3, 4, 5`; see ledger/tight-hamilton-codegree.md |
| 6 | Goddard–Henning Conjecture 32 (proper 4-colouring of triangulations with two total dominating colour pairs; 36-vertex triangulation) | Kwon–Park–Sano 2611.00572 | No (AFTD lists only its open Conjecture 1.4) | **Done (GHT-1, PR 58):** Lean disproof (`n = 36`); see ledger/goddard-henning-total-domination.md |
| 7 | Chow–Rimanić lonely runner conjecture over function fields (13 polynomials over `𝔽₂`, `C₃(2) ≤ 13 < 15`) | Hu 2608.18818 | No | **LR-1:** Lean disproof; see ledger/lonely-runner-function-field.md |

Also seen: Wormald's linear-forest conjecture counterexample 2610.00086 (authors' own Lean proof; skip); Alon–Krivelevich
choosability 2610.42094 (AFTD has it; skip).

