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
- **2026-11-26, about 10 PM ET.** We answered a question raised in Noel's Partial List Colouring paper (to
  our knowledge no answer has been published): he asked for **connected** counterexamples that miss the conjecture's promise by a **large** amount (his
  own example misses by only a third of a vertex). We chain copies of his graph together, joining each copy
  to the next by a single edge at a carefully chosen vertex. With t copies (14t vertices) the graph is
  connected and still needs 3 colours, yet at most 9t vertices can be coloured from the 2-colour lists,
  against the promised 28t/3. So the shortfall grows in step with the size of the graph (n/42), and a
  known theorem (Chappell) shows a shortfall of that order is the most possible. The key new step is
  checking that each copy stays colourable when one vertex loses a colour; other joining points fail.
  Lean checks the whole infinite family. Standard axioms only, kernel re-check passed.
  Internal audit: pass.
  Proof: [Connected.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/PartialList/Connected.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/partial-list-colouring.md).
- **2026-11-26, about 11:30 PM ET (2026-11-27 UTC).** We Lean-checked the **second of the two smallest
  counterexamples** to the claw-free Schur-positivity conjecture. A computer census (Prajapati 2026) found exactly
  two bad graphs on 12 vertices; we had already checked the first (coefficient −64). This one has 21 edges and
  coefficient −40, and Wang, Zhang and Zhao showed it is also the smallest counterexample when graphs are ordered
  by edge count first (both published computer results, not re-checked by us). With this, both counterexamples
  from that census are machine-verified. Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Counterexample.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/ClawFree2/Counterexample.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/claw-free-schur.md).
- **2026-11-26, about 11 PM ET.** We showed the **Partial List Colouring Conjecture fails far more
  widely than was known**. Noel's counterexample covered one case only (graphs needing 3 colours, lists
  of 2 colours). We generalised his construction to every case of the form "graphs needing k colours,
  lists of k − 1 colours", for every k ≥ 3: for example, a 111-vertex graph needing 4 colours where lists
  of 3 colours let at most 83 vertices be coloured, short of the promised 83.25. Lean checks the whole
  infinite family at once. To our knowledge no case other than Noel's had been settled. Standard axioms
  only, kernel re-check passed. Internal audit: pass.
  Proof: [General.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/PartialList/General.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/partial-list-colouring.md).
- **2026-11-27, about 12:30–1 AM ET.** We Lean-checked the disproof of the **gap-one conjecture for equitable
  colouring of block graphs** (Dybizbański, Furmańczyk and Mkrtchyan, 2024; checked by them by computer for all
  block graphs up to 19 vertices). An equitable colouring is a proper colouring where all colour groups have almost
  the same size. The conjecture said a simple lower bound L(G) is always within one of the true minimum number of
  colours. Lauri (arXiv:2608.14517, Aug 2026) found tree-like graphs where it is off by more; we checked the
  smallest graph in his family: 32 vertices, L = 7, but 9 colours are needed. Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Counterexample.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/BlockEquitable/Counterexample.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/block-equitable.md).
- **2026-11-27, about 1 AM ET.** We showed the **List Total Colouring Conjecture fails at every size, not just
  for cubic graphs**. Noel's counterexample has maximum degree 3. We generalised it to every maximum degree
  d ≥ 3: glue d + 1 copies of a complete bipartite block together with single edges, and give each piece a
  carefully chosen list of d + 1 colours. The graph can be totally coloured with d + 1 colours, but not from
  those lists. So for every k ≥ 4 there is a graph whose total colouring number is k that is not totally
  k-choosable. Lean checks the whole infinite family. We found no published version of this (web search,
  27 Nov), but Noel mentions private discussions about extensions, so others may have it too.
  Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [General.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/ListTotal/General.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/list-total-colouring.md).
- **2026-11-27, about 2:30 AM ET.** We Lean-checked Lauri's **whole family** of block-graph counterexamples, not
  just the smallest one. For every d ≥ 2 and k ≥ 4d − 1 there is a tree-like graph where the formula L(G) says k
  colours but k + d are needed, so the formula can be off by any amount. Lean checks all of these graphs at once.
  Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Family.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/BlockEquitable/Family.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/block-equitable.md).
- **2026-11-27, about 3:30 AM ET.** We Lean-checked the disproof of the **leaf conjecture for local antimagic
  colouring of trees**. Number the edges 1, 2, 3, … and give each vertex the sum of its edge numbers; the
  conjecture said that, with a clever numbering, a tree never needs more than "number of leaves + 2" different
  sums while neighbours always differ. Brondani and França (arXiv:2610.22783, Oct 2026) built caterpillar trees
  where every numbering gives all vertices different sums, so the excess can be any size. Lean checks the whole
  infinite family. Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Family.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/LocalAntimagic/Family.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/local-antimagic.md).
- **2026-11-27, about 4:15 AM ET.** We also Lean-checked the **smallest counterexample** in the same paper: a
  43-vertex tree with 40 leaves that needs 43 different sums, three more than the number of leaves. Three
  internal vertices is the fewest any counterexample can have. Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [T3.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/LocalAntimagic/T3.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/local-antimagic.md).
- **2026-11-27, about 5:20 AM ET.** We Lean-checked the disproof of the **Chung–Graham–Spiro gap-set
  conjecture**. Split the whole numbers from 2 up into two lists ("down" and "up") by a Fibonacci rule; the
  conjecture said the two lists always have the same spacing patterns. Aliabadi (arXiv:2609.04473, Sept 2026)
  showed that five consecutive "up" numbers can span exactly 9 but five consecutive "down" numbers never can.
  Our Lean proof is fully self-contained: it re-proves the older results the paper cites, and replaces two of
  them with a new five-shift argument. Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Main.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/FibWalk/Main.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/fib-walk-gaps.md).
- **2026-11-27, about 6:00 AM ET.** We Lean-checked the disproof of the **bipanchromatic colouring conjecture**
  of Lalou, Mbarek, Skender and Togni. Colour the points of a hypergraph so that every group sees every colour; the
  conjecture predicted the best you can do when no colour may be used only once. Novaković and Jojić
  (arXiv:2610.27133) showed that "sunflower" hypergraphs beat the prediction by an unlimited amount; the smallest
  has just 6 points. Lean checks the whole family. Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Sunflower.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/Bipanchromatic/Sunflower.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/bipanchromatic.md).
- **2026-11-27, about 7:00 AM ET.** We Lean-checked the disproof of the **Bencs–Csikvári spanning-forest
  conjecture**. A spanning forest of a network is a choice of links with no closed loop; the conjecture said that
  if every point has at least 3 links, the number of spanning forests is at most the product of the link counts.
  Wu, Lu and Dong (arXiv:2611.18076, Nov 2026) showed that "complete bipartite" networks (two groups, every point
  linked to every point of the other group) break it once one group is much bigger. Lean checks a concrete
  example with 3 + 38 points and the whole infinite family. Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Counterexample.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/SpanningForests/Counterexample.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/spanning-forests.md).
- **2026-11-27, about 8:05 AM ET.** We Lean-checked the disproof of the **Chen–van der Holst–Luo–Ma conjecture
  on colouring the links of "covers" of networks**. A 3-fold cover stacks three copies of a network and rewires
  each link between the copies; the conjecture gave an exact formula for the fewest link colours some such cover
  needs. Wang (arXiv:2611.13394, Nov 2026) built a network from the famous Petersen graph where the formula says
  9 but every cyclic cover needs 10. Lean checks this for the 30-point example. Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Petersen.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/OddFoldCovers/Petersen.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/odd-fold-covers.md).
- **2026-11-27, about 7:00 PM ET.** We Lean-checked the disproof of the **Albertson–Berman conjecture** (1979),
  which says every planar network on `n` points keeps a cycle-free part on at least half its points. Cames van
  Batenburg, Goedgebeur and Jooken (arXiv:2608.23260) found a 29-point planar network where every cycle-free part
  has at most 14 points. Lean checks both halves: an exact straight-line drawing with no crossings, and the
  14-point bound. Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Counterexample.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/AlbertsonBerman/Counterexample.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/albertson-berman.md).
- **2026-11-27, about 8:00 PM ET.** We Lean-checked the disproof of **Goemans's unsplittable-flow conjecture**
  (2000). Picture shipping goods from one warehouse to several stores: the conjecture said any plan that splits
  shipments over several routes can be replaced by a plan using one route per store, without overloading any road
  by more than the largest order and without costing more. Ge, Xie, Li and Li (arXiv:2611.23244, example credited
  to Rybin) give a 7-point network where the split plan costs 58 but every allowed single-route plan costs at least
  60. Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Unsplittable.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/Goemans/Unsplittable.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/goemans-unsplittable.md).
- **2026-11-27, about 9:00 PM ET.** We Lean-checked Srivastava's counterexample (arXiv:2608.15281) to the **first
  version of Mizzi's cycle conjecture on unstable graphs** (arXiv:2603.27559 v1/v2). That version said every
  "unstable" network (one whose doubled copy has unexpected symmetries) must contain loops of lengths `k` and `2k`
  for some odd `k`. A 10-point network has loops of lengths 5, 5 and 6 only. Mizzi has since narrowed the
  conjecture to networks with no symmetries at all; this example does not touch the narrowed version.
  Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Mizzi.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/Unstable/Mizzi.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/unstable-graphs.md).
- **2026-11-27, about 9:30 PM ET.** We Lean-checked the disproof of the **Bougard–Joret conjecture** (J. Graph
  Theory, 2008) on the fewest links a robust network can have. A network is "4-connected" if it stays in one piece
  after removing any 3 points. The conjecture predicted the fewest links for such networks with a given number of
  points and a given largest set of mutually unlinked points; Das and Gupta (arXiv:2608.18828) showed the first part
  fails for 7 points, where the prediction is 14 links but every such network needs 15. Lean checks that 15 is
  needed. Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Basic.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/BougardJoret/Basic.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/bougard-joret.md).
- **2026-11-27, about 11:10 PM ET.** We Lean-checked the disproof of the **Hinrichs–Vybíral conjecture** (2011) on
  "positive definite" functions, which measure similarity between points in space and are used in numerical
  integration. The conjecture claimed every such function (nonnegative, bounded, equal to 1 at the origin) satisfies
  a certain lower bound for any set of points and weights. Vybíral (arXiv:2609.21733) found a function on
  7-dimensional space built from cosines where 8 points break the bound (4.4 versus the promised 4.5). Lean checks
  that this function has every required property and that the bound fails. Standard axioms only, kernel re-check
  passed. Internal audit: pass.
  Proof: [Basic.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/HinrichsVybiral/Basic.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/hinrichs-vybiral.md).
- **2026-11-28, about 1:15 AM ET.** We found and Lean-proved a **new fact about slow Fibonacci walks**: the 7-step
  gap sets of "down" and "up" integers differ. Chung, Graham and Spiro (2019) split the whole numbers into two
  families and asked whether the two families have the same spacing patterns. Published work answered this only for
  patterns of up to 4 steps (no at 4 steps, yes at 3). We show the answer is also no at 7 steps: eight consecutive
  down-integers can span exactly 17 (9 to 26), but eight consecutive up-integers never can. As far as we know this is
  the first case beyond 4 steps, and computer checks suggest many more. Standard axioms only, kernel re-check
  passed. Internal audit: pass.
  Proof: [Seven/Main.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/FibWalk/Seven/Main.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/fib-walk-gaps.md).
- **2026-11-28, about 1:15 AM ET.** We Lean-checked **Mao and Zhao's theorem** (arXiv:2608.19886) that the 3-step
  gap sets of down- and up-integers are equal, both {3, 4, 5, 6, 7, 8, 10, 11, 13}, with our own proof. Standard
  axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Three/Main.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/FibWalk/Three/Main.lean).
- **2026-11-28, about 3:10 AM ET.** We Lean-checked **Wang's disproof of the Henning–Yeo conjecture**
  (arXiv:2608.19455). In 2012 Henning and Yeo predicted an upper limit on how many vertices of a network you need
  to "tell every link apart" (an identifying vertex cover), in terms of the number of vertices, links and the
  largest degree. Wang found a family of small networks that need more vertices than the limit allows (7 versus a
  limit of about 6.94 for the smallest, 8-vertex example). Lean checks the whole family, so the prediction fails for every largest degree from 4 up.
  Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Counterexample.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/IdentifyingCover/Counterexample.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/identifying-vertex-cover.md).
- **2026-11-28, about 4:00 AM ET.** We Lean-checked a **disproof of a computer-generated graph conjecture**
  (TxGraffiti, 2023): that in every connected network, the fewest links you can pick so that no two touch and
  no further link can be added (a minimum maximal matching) is at most the "harmonic index", a degree-weighted
  link count. Gupta (arXiv:2606.15761), after Bıyıkoğlu, showed that k triangles sharing one corner break it for
  every k ≥ 4: 4 links are needed but the index is only 3.6 for k = 4. Lean checks both exact formulas for every k.
  Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Harmonic.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/Saturation/Harmonic.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/saturation-harmonic.md).
- **2026-11-28, about 5:30 AM ET.** We Lean-checked **Yavari's disproof of Teschner's bondage-number conjecture**
  (arXiv:2609.04257). The "bondage number" of a network is how many links you must cut before you need more
  "guard" vertices to watch every vertex (each guard watches itself and its neighbours). Teschner conjectured in
  1995 that this is at most 1.5 times the largest number of links at any vertex. Yavari's network has 18 vertices,
  3 links at each, and needs 6 guards. Lean checks that cutting any 4 links still leaves 6 guards enough, while
  cutting a certain 5 forces a 7th guard. So 5 cuts are needed, more than the 4.5 the conjecture allows.
  Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Main.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/Bondage/Main.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/bondage-number.md).
- **2026-11-28, about 6:30 AM ET.** We proved, with computer-checked Lean proofs, that the down- and up-integer
  spacing patterns also **differ at 8 steps and at 9 steps**. Nine consecutive up-integers can span exactly 17 (25 to
  42), and ten can span 25 (30 to 55), but down-integers never can. As far as we know these are new; published work
  stops at 4 steps and our 7-step result came earlier today. We also attacked the open question of whether this
  happens for infinitely many step counts. We did not prove it, but computer checks show a difference for every step
  count from 15 to 300, and we found where the differences come from (notes in explorer/fib-walk/valleys.md).
  Standard axioms only, kernel re-check passed. Internal audit: pass with notes (notes applied).
  Proof: [UpOnly/L8Main.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/FibWalk/UpOnly/L8Main.lean),
  [UpOnly/L9Main.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/FibWalk/UpOnly/L9Main.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/fib-walk-gaps.md).
- **2026-11-28, about 7:00 AM ET.** We Lean-checked **Ferudun's counterexamples to the all-n codegree conjecture
  for tight Hamiltonian cycles** (Zenodo 10.5281/zenodo.23006717). A "hypergraph" has edges that join k vertices at
  once. Rödl, Ruciński and Szemerédi (2011) conjectured that if every group of k − 1 vertices sits inside at least
  about (n − k + 3)/2 edges, then all n vertices can be arranged in a circle so that every k neighbours in a row form
  an edge. Ferudun found that this fails for small n: a 7-vertex example for k = 3 built from the
  "hemi-icosahedron", plus 8- and 9-vertex versions for k = 4 and 5. Lean checks all three. (The conjecture for
  large n is untouched.) Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [Main.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/TightHamilton/Main.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/tight-hamilton-codegree.md).
- **2026-11-28, about 8:15 AM ET.** We Lean-checked **Kwon, Park and Sano's disproof of Goddard and Henning's
  Conjecture 32** (arXiv:2611.00572). Take a map where every region is a triangle and colour its corners with
  four colours so that neighbours always differ. Goddard and Henning (2018) conjectured that you can always do this
  so that, grouping the colours into two pairs, every corner has a neighbour coloured from each pair. Kwon, Park and Sano found a
  36-corner map where this is impossible. Lean checks that the map really is a flat triangle map: it has an
  exact drawing and the right number of edges. It also checks that no such colouring exists. (Lean checks the 36-corner example; the paper's
  bigger examples for every size from 36 up are not formalized.) Standard axioms only, kernel re-check passed.
  Internal audit: pass.
  Proof: [Main.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/TotalDomination/Main.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/goddard-henning-total-domination.md).
- **2026-11-28, about 9:45 AM ET.** We Lean-checked **Hu's disproof of the Chow–Rimanić "lonely runner"
  conjecture for function fields** (arXiv:2608.18818). The classic lonely runner puzzle asks whether runners at
  different speeds on a circular track always leave each runner, at some moment, far from all the others. Chow and
  Rimanić (2019) studied a version where the speeds are polynomials over a finite field. In one case, their
  conjecture says you need at least 15 speeds before "at every moment, some runner is very close to the start"
  can happen at a certain closeness level. Hu found just 13 speeds (polynomials with 0/1 coefficients) that already
  do it. Lean checks all 128 cases that matter. Standard axioms only, kernel re-check passed. Internal audit: pass.
  Proof: [FunctionField.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/LonelyRunner/FunctionField.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/lonely-runner-function-field.md).
- **2026-11-28, about 8:30 AM ET.** We Lean-checked **Del Pia's disproof of the Gerards–Schrijver conjecture**
  (arXiv:2611.28580), a 2007 conjecture in integer programming. It predicted exactly which "nicely behaved" matrices
  let one round of rounding cuts (the Chvátal closure) reach all whole-number solutions; Del Pia's 5 × 6 matrix
  breaks it. Lean checks that the matrix is of the right type and that the rounding cuts fall short for it. The step
  the paper does with linear-programming duality (not available in Lean's library) we did with a new shortcut that
  needs only a 9-case integer check. The paper also names **two more counterexample matrices without proofs**; we
  found data for them and proved them in Lean too, the first proofs we know of. Not in Lean: that the matrices avoid
  the conjecture's two forbidden patterns (computer-checked by us instead).
  Standard axioms only, kernel re-check passed. Internal audit: pass with notes (notes applied).
  Proof: [A6.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/EdmondsJohnson/A6.lean),
  [A6plus.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/EdmondsJohnson/A6plus.lean),
  [A7.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/EdmondsJohnson/A7.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/edmonds-johnson.md).
- **2026-11-28, about 10 AM ET.** We Lean-checked the disproof of **Sra's "quantum coupon collector" conjecture**
  (posed on MathOverflow in 2017; counterexample in arXiv:2608.29595, "GPT, the Counterexample Machine"). The
  classic coupon-collector formula gives the expected time to collect all coupons as an alternating sum of
  fractions, and it is always positive. Sra asked whether the same alternating sum stays positive when the numbers
  are replaced by positive definite matrices. It does not: six explicit 3 × 3 matrices give a sum that is negative
  in one direction. Lean checks all 63 matrix inverses involved with exact fractions. Standard axioms only, kernel
  re-check passed. Internal audit: pass with notes (notes applied).
  Proof: [Main.lean](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/Lab/QuantumCoupon/Main.lean),
  [ledger](https://github.com/kyleglsn22-spec/open-problems-lab/blob/main/ledger/quantum-coupon-collector.md).
