# Achievements

A plain log of what we have done. One line per win: what we did, when, and where the proof is.
The detailed math lives in [ledger/](ledger/). Times are when the work was merged into the
main branch, in US Eastern time.

Words we use:
- **Lean-checked**: a computer proof checker (Lean) verified every step. No human trust needed for the logic.
- **Internal audit**: our own Auditor, who did not write the work, checked it. Outside review is still welcome.
- **Appears to be first**: we searched and found nobody who did this before, but we can't be certain.

## Log

- **2026-11-25, 8:34 AM ET.** We proved, with a computer-checked Lean proof, that the answer to
  Erdős problem #757 is at most 7/12 (the known bound was "less than 3/5"). This appears to be the
  first complete computer-checked proof of any bound for #757; the math itself uses an example from
  published work. Proof: PR #4, [UpperBound.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/Erdos757/UpperBound.lean).

- **2026-11-25, 10:00 AM ET.** Our in-house Auditor checked the 7/12 proof above and the degree-4
  sensitivity result below, and signed off on both (internal audit). Proof: PR #6,
  [audits.md](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/audits.md).

- **2026-11-25, 10:01 AM ET.** We found a short, independent proof of a 2026 result by Koshta on
  "degree vs sensitivity" (Tao's problem C37) for degree 4, checked with exact arithmetic.
  **Not a first:** Pinho published a proof in October 2026, before us. Proof: PR #5,
  [explorer/c37/](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/explorer/c37/).

- **2026-11-25, 10:31 AM ET.** We proved, with a computer-checked Lean proof, that the answer to
  Erdős problem #757 is at most 4/7. At the time we started this was the best published bound
  (a better 5/9 was later found posted online, not by us). This appears to be the first
  computer-checked proof of this bound; the example set comes from Ma and Tang's paper. Our Auditor
  signed off before merge (PR #8). Proof: PR #7,
  [FourSevenths.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/Erdos757/FourSevenths.lean).

- **2026-11-25, afternoon ET.** We proved in Lean that the answer to Erdős problem #757 is at
  least 9/17 ≈ 0.529 (the best known lower bound, from Ma and Tang), **conditional on one published
  theorem** (Henning–Yeo 2021, a 24-page hypergraph result that we state as an explicit assumption
  rather than prove). Every other step is computer-checked, including a fact Ma and Tang only cite
  from a 1995 paper. We have not checked whether anyone did this before. Our Auditor signed off
  (internal audit). Proof: PR #12,
  [LowerBound.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/Erdos757/LowerBound.lean).

- **2026-11-25, 2:10 PM ET.** For the online 5/9 construction, we proved that its largest Sidon
  subset is at most 7 + 5K for every size K. That is the counting half of the 5/9 claim. The other
  half (the copies never interact) is still unchecked by us. We also showed by computer search that
  small building blocks of this kind (12 to 14 points) cannot beat 5/9. Internal audit: pass.
  Proof and code: PR #13,
  [explorer/erdos757/gadgets/](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/explorer/erdos757/gadgets/).

- **2026-11-25, 4:05 PM ET.** We checked the online 5/9 construction for every size, so the answer to
  Erdős problem #757 is at most 5/9 ≈ 0.556 (previously that rested only on AI referees). The proof
  is an exact computer check that runs in about a second. Not yet in Lean. Internal audit: pass.
  The construction itself is a reader's, not ours. Proof: PR #15,
  [five_ninths_all_k.py](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/explorer/erdos757/gadgets/five_ninths_all_k.py).
- **2026-11-25, 6:00 PM ET.** We proved in Lean that the answer to Erdős problem #757 is at most
  5/9 ≈ 0.556, for every size of the reader's construction. As far as we know this is the first
  machine-checked proof of the best known upper bound. Standard axioms only, kernel re-check passed.
  Internal audit: pass. The construction itself is a reader's, not ours. Proof:
  PR #17,
  [FiveNinths.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/Erdos757/FiveNinths.lean).
- **2026-11-26, early morning ET.** New problem (Erdős #1186): colour 0..p−1 in two colours with as few
  one-colour 4-step progressions as possible. We found colourings (they use the remainder
  of x mod 44 as well as its position; correction 2026-11-26: these turn out to be a special case of
  Marquardt's position-only colourings after a change of variables, so not a new kind) with share 479/4356 ≈ 0.10996 for every large prime, below the
  best published bound 17/150 ≈ 0.11333 (Lu–Peng 2012). **Not a record:** an unrefereed online project
  (Marquardt, Nov 2026) already reached ≈ 0.10964 with a finer colouring of the same kind. Exact computer check plus a short proof;
  internal audit: pass. Proof: PR #21,
  [explorer/erdos1186/](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/explorer/erdos1186/).
- **2026-11-25, late night ET.** We proved in Lean that no Boolean function of degree at most 4 has
  sensitivity 10 (Koshta's 2026 result on Tao's problem C37), using our short two-block argument
  instead of Koshta's 479-leaf computer search. About 230 lines, standard axioms only, kernel
  re-check passed. Stated in the normalized coefficient form. Internal audit: pass. We have not seen
  a Lean proof of this result before, but we can't be certain. The open degree-5 case
  (14 inputs) is paused: our searches narrowed it but could not settle it. Proof:
  PR #23,
  [Degree4.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/C37/Degree4.lean).
- **2026-11-26, early morning ET.** New problem (Tao's constant C44: how many inputs can a
  degree-d yes/no function really use?). We **Lean-checked** the 2018 Chiarelli–Hatami–Saks
  construction for every degree, which proves the known lower bound C44 ≥ 3/2. We found no earlier
  formal proof of it. Our computer searches (solver verdicts, not proofs) found that no "block
  composition" of known extremal pieces with up to 9 blocks (488 shapes, degrees 5 and 6) beats
  the 2018 record, so beating it needs a genuinely new building block. Not a new bound. Internal
  audit: pass. Proof: [Lab/C44/LowerBound.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/C44/LowerBound.lean),
  search: [explorer/c44/](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/explorer/c44/).
- **2026-11-26, morning ET.** We machine-checked in Lean Gao, Geroldinger, Wang and Zeng's disproof of the 1969
  van Emde Boas–Kruyswijk conjecture on the Davenport constant: there are 76 elements of the group (Z/6)^15 with no nonempty
  group of them summing to zero, one more than the conjecture allows. The counterexample is from a
  preprint by Gao, Geroldinger, Wang and Zeng posted 18–24 Nov 2026 (not ours, and not yet refereed);
  as far as we can find, ours is the first machine-checked proof of it. Standard axioms only, kernel
  re-check passed. Internal audit: pass. Proof: PR #28,
  [VanEmdeBoasKruyswijk.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/Davenport/VanEmdeBoasKruyswijk.lean).
- **2026-11-26, morning ET.** We extended the Lean check of Gao, Geroldinger, Wang and Zeng's
  disproof to their whole family of examples: for every n = 6, 10, 14, … (n ≡ 2 mod 4) and every
  number of coordinates r ≥ 5n/2, Lean confirms a list of r(n−1)+1 elements of (Z/n)^r with no
  nonempty part summing to zero. So the 1969 conjecture fails for all these cases, not just one.
  The construction is theirs, and this appears to be the first machine-checked proof of it.
  Internal audit: pass. Proof: PR #31,
  [GeneralFamily.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/Davenport/GeneralFamily.lean).
- **2026-11-26, about 9 AM ET.** We finished the Lean check of Gao, Geroldinger, Wang and Zeng's
  Theorem 1.1 in full, including its sharper "floor" term: for every n = 6, 10, 14, … and every
  number of coordinates r, Lean confirms a list of r(n−1) + ⌊(r−1)/(5k−1)⌋ elements of (Z/n)^r
  (k = n/2) with no nonempty part summing to zero. So the 1969 conjecture is beaten by one more
  element for every extra 5k−1 coordinates (for n = 6: by 2 from 29 coordinates, by 3 from 43).
  The construction and the "replacement" trick are theirs; this appears to be the first
  machine-checked proof of the full theorem. Internal audit: pass. Proof:
  PR #35,
  [FloorTerm.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/Davenport/FloorTerm.lean).
- **2026-11-26, about 9:30 AM ET.** The Erdős #757 lower bound 9/17 ≈ 0.529 is now **Lean-checked with no
  assumptions**. We formalized the 24-page Henning–Yeo (2021) hypergraph transversal theorem that the
  earlier proof had to assume (about 7,700 lines of Lean). Along the way we found and fixed two small
  issues in the published proof (see the plan notes). So both best known bounds for #757,
  9/17 ≤ c ≤ 5/9, are now machine-checked. As far as we know this is the first formal proof of the
  Henning–Yeo theorem. Standard axioms only, kernel re-check passed. Internal audit: pass with notes.
  Proof: PR #27,
  [Unconditional.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/Erdos757/Unconditional.lean),
  [Lab/HenningYeo/](https://github.com/kyleglsn22-spec/open-problems-lab/tree/main/Lab/HenningYeo).

- **2026-11-26, 3:15 PM ET.** We gave a computer-checked Lean proof that the **List Total
  Colouring Conjecture** (Borodin–Kostochka–Woodall, Juvan–Mohar–Škrekovski, Hilton–Johnson, late
  1990s) is false. The counterexample is Noel's (arXiv 2609.38417, September 2026, found with an AI
  model): a 20-vertex graph that can be totally coloured with 4 colours, but has lists of 4 allowed
  colours per vertex and edge from which no total colouring exists. This appears to be the first formal
  proof of this disproof. Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Counterexample.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/ListTotal/Counterexample.lean).

- **2026-11-26, 5:28 PM ET.** We found a smaller counterexample to the non-abelian
  Gyarmati–Matolcsi–Ruzsa sumset inequality (a 2010 question, disproved in October 2026), and proved it
  with a computer-checked Lean proof. The smallest published four-set counterexample lives in a group of
  order 518,400; ours lives in a group of order 131,072 (almost four times smaller), and the same group also
  gives the smallest known five-set counterexample. (Smaller groups were already known for six or more sets.)
  It is a new way of building Elsholtz's "sparse template" (his Proposition 6.8), not a new mechanism. The
  published paper says no minimality is claimed and leaves open whether this template can beat 518,400. This appears to be
  the first improvement and the first formal proof of the disproof. Standard axioms only, kernel re-check passed.
  Internal audit: pass. Proof: [Counterexample.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/GMR/Counterexample.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/gmr-non-abelian.md).

- **2026-11-26, 8:36 PM ET.** We gave a computer-checked Lean proof that the **claw-free
  Schur-positivity conjecture is false** (Stanley 1998, credited to Gasharov; disproved in July 2026 by
  Prajapati and, independently, Matherne–Morales). The counterexample is a 12-vertex graph built from a
  square with two triangles and two whiskers; its "chromatic symmetric function" has a negative Schur
  coefficient (−64). Lean confirms the graph is claw-free and that no non-negative Schur expansion exists.
  This appears to be the first formal proof of this disproof. According to the paper's computer census (not
  re-checked by us), 12 vertices is the minimum. Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Counterexample.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/ClawFree/Counterexample.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/claw-free-schur.md).
- **2026-11-26, about 9 PM ET.** We gave a computer-checked Lean proof that the **Partial List
  Colouring Conjecture is false** (Albertson, Grossman and Haas, 2000; disproved in September 2026 by
  Noel, with a counterexample found by an AI model). The conjecture says: if a graph needs k colours for
  list colouring, then from any lists of ℓ < k colours you can still properly colour at least an ℓ/k share
  of its vertices. Noel's 14-vertex graph (four triangles plus two hub vertices) needs 3 colours, yet from
  his lists of 2 colours at most 9 of the 14 vertices can be coloured, short of the promised 28/3 ≈ 9.33.
  Lean checks both halves, including that every assignment of 3-colour lists works. This appears to be the
  first formal proof of this disproof. Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Counterexample.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/PartialList/Counterexample.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/partial-list-colouring.md).
