---
problem: Erdős Problem 1186 (second part), monochromatic 4-term progressions in 2-colourings of Z_p
source: https://www.erdosproblems.com/1186
lean_statement: none yet (formal-conjectures has a statement for #1186 per teorth/erdosproblems; not checked)
status: paused (beats published bound; not a record; combining with Marquardt shown to be empty, 2026-11-26)
budget_usd: 150
spent_usd: 0
owner: Kyle
---

# Erdős #1186: fewest one-colour 4-term progressions mod a prime

## Statement
For a prime p and a 2-colouring c of Z_p, let m4(Z_p, c) be the fraction of the p^2 pairs (a, d) for
which a, a+d, a+2d, a+3d all get the same colour, and m4(Z_p) the minimum over colourings (Lu–Peng's
convention). erdosproblems.com #1186 writes the same quantity as δ̃_4 with unordered progressions
(δ̃_4 = m4/2, so its "7/192 ≤ δ̃_4 ≤ 17/300" is the row below). A random colouring gives 1/8.
Question: the asymptotic value of m4(Z_p) as p → ∞.

## Known results
| Bound or result | Reference | Checked by us? |
| --- | --- | --- |
| m4(Z_p) ≥ 1/16 + o(1) | Wolf, J. Comb. 1 (2010) | No |
| m4(Z_p) ≥ 7/96 + o(1) ≈ 0.0729 | Lu–Peng, JCTA 119 (2012), arXiv:1107.2888 | No |
| m4(Z_p) ≤ 17/150 + o(1) ≈ 0.11333 (periodic block colouring B20) | Lu–Peng 2012 | Yes: our exact formula gives exactly 17/150 for B20 in every residue class mod 20 |
| m4(Z_p) ≤ 1478233/13482006 + o(1) ≈ 0.109645 (δ̃_4 ≤ 0.054822, 3.25% below 17/300): 26-arc colouring of the circle x ↦ word[floor(2998x/p)] | Max Marquardt, github.com/incrediblecrab/erdos-problems `p1186` (public, 2 Nov 2026; unrefereed, built with Claude; exact checkers) | Partly: we reproduced their m = 496 word's value 0.10967850 with our own cell evaluator |
| liminf over composite n: 1/12 (n = 11·m); k = 5, 6 analogues | Lu–Peng 2012; Parczyk–Pokutta–Spiegel–Szabó, arXiv:2206.04036 | No (composite n only, does not apply to primes) |

Scout (2026-11-26): no refereed or arXiv improvement of 17/150 for primes after 2012. **But** the in-house
Auditor found a public GitHub project (Marquardt, Nov 2026, row above) with a better unrefereed bound,
0.109645, from plain circle colourings with free breakpoints. Our first scout missed it. So our
bounds below are **not records**; they are an independent construction of a different kind
(residue classes mod b, not only position) that also beats the published 17/150.

## Claims
| ID | Claim | Author (person + AI/model) | Status | Evidence |
| --- | --- | --- | --- | --- |
| 1186-2 | m4(Z_p) ≤ 479/4356 + o(1) ≈ 0.109963 for all primes p (12.0% below random; Lu–Peng: 9.3%; not a record, see Marquardt above): c(x) = G_r[x mod 44][floor(3x/p)], one 44 x 3 table per residue r = p mod 44 | Claude (Opus 5.5) | **checked** (internal audit 2026-11-26, pass with notes) | `explorer/erdos1186/cert_44_3.json`, same checker and proof; brute force at p ≈ 6000 in all 20 classes gives 0.10980; error ~1/p from either side (Auditor: up to p ≈ 100000) |
| 1186-1 | m4(Z_p) ≤ 27/242 + o(1) ≈ 0.111570 for all primes p (beats 17/150): c(x) = A[x mod 22] for x < p/2 and A[(x+5p) mod 22] for x > p/2, A = 1011110001001000011101 | Claude (Opus 5.5) | **checked** (internal audit 2026-11-26, pass with notes) | `explorer/erdos1186/`: `cert_22_2.json`, `check_certificate.py` (exact rationals, all 10 residue classes mod 22, plus brute force on real primes ≈ 6000), proof of the limit formula in `PROOF.md` |

## Log
- 2026-11-26: chosen as roadmap item 4 after C44 (relevant variables) was dropped: Pinho (Nov 2026) claims R_4 = 22 and C44 < 1.99, so that problem is crowded.
- 2026-11-26: plain 1D step colourings F(x/p) and unstructured tabu on Z_p (p ≤ 503) do worse than 17/150 in the limit. Family c(x) = G[x mod b, floor(Kx/p)] with exact limit formula: b = 22, K = 2 gives 27/242 in every residue class.
- 2026-11-26: C tabu (`tabu_family.c`) over b ≤ 88, K ≤ 4: b = 44, K = 3 gives 479/4356 in all 20 residue classes (claim 1186-2). Best single class seen: 791/7200 ≈ 0.109861 (b = 60, K = 4, r = 1), but not yet found for every class mod 60.

- 2026-11-26: in-house audit (independent polygon-clipping checker + own brute force up to p ≈ 100000): both claims pass with notes; found Marquardt's better unrefereed bound. Quick test: adding residue classes mod b ≤ 5 to Marquardt's m = 496 word by single-arc flips gives no gain (it is a local optimum for that move).
- 2026-11-26: combined family on finer grids (b ≤ 4 residues × M ≤ 72 equal slices, tabu): residues help a lot at equal M (M = 72: 0.11272 with b = 1, 0.11008 with b = 3), but tabu on fine grids is far from Marquardt's continuous optimum (his b = 1 basin is 0.109644). Next idea, not started: per-residue arc colourings with free breakpoints (his optimiser plus our residue structure). Paused here, effort cap reached.

- 2026-11-26 (thread "Set a record on Erdős #1186"): **the combined family is empty.** Multiplying by b⁻¹ mod p
  turns any colouring c(x) = S_{x mod b}(x/p) into a plain circle colouring (Marquardt's family); checked
  pointwise on real primes and exactly for cert_44_3 (`explorer/erdos1186/equiv_check.py`). Our "new kind of
  colouring" wording in PR 21 was wrong and is corrected in the README and ACHIEVEMENTS. Then tested families that
  are genuinely bigger: random colourings with position-dependent odds, a second coordinate x²/p, 2-D torus
  colourings, and a wide multistart with up to 64 arcs. None beats 0.1096440 (details: `explorer/erdos1186/search2/`).

## Dead ends
- Residue classes mod b on top of circle colourings: provably nothing new (a dilation turns them into circle colourings).
- Random colourings with position-dependent odds, and colourings using x²/p (or higher powers) as a second coordinate:
  at Marquardt's optimum the best choice is his ±1 colouring again (local optimality, L-BFGS from many perturbations).
- 2-D torus colourings F(x/p, λx/p): contained in the closure of circle colourings; v-dependent breakpoints relax back
  to his optimum.
- Multistart over antipodal circle colourings, 18 to 62 arcs: 138 starts, best 0.10964429, never below Marquardt's 0.10964403.
- Colourings that depend only on x/p (interval colourings, up to 30 pieces): ≥ 0.1249 at p = 1009.
- Periodic colourings c(x) = B[x mod b] alone (K = 1), b ≤ 40, optimised for the prime limit directly: nothing better than Lu–Peng's 17/150.
