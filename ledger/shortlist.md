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
| 3 | Claw-free Schur-positivity conjecture (Stanley 1998 / Gasharov) is false | Prajapati arXiv 2607.26364; Matherne–Morales | 12-vertex graph, one Schur coefficient equals -64 | No | Later: needs chromatic symmetric functions and Schur coefficients in Lean (heavy definitions) |
| 4 | Partial List Colouring Conjecture (Albertson–Grossman–Haas) is false | Noel arXiv 2609.23291 | Same author and style as #1 | Not checked yet | Bundle with #1 if the proof is short |
| 5 | Gerards–Schrijver Edmonds–Johnson conjecture is false | arXiv 2611.28580 (20 Nov 2026), a 5×6 matrix | Very fresh | AFTD cites it once | Later: Chvátal closure is hard to formalize |

Dropped: **Hilton's conjecture** (proved arXiv 2611.12199): AFTD already has a Lean proof (11 Nov) and Bai (Zenodo
24152331) Lean-proved the follow-up conjecture. Also dropped: El-Zahar–Erdős (probabilistic proof, hard to formalize) and
the happy-edge conjecture (flip-distance lower bounds, heavy).
