# Search for the rank-9 counterexample for n = 6 (GGWZ v3, Remark after Theorem 1.1)

GGWZ claim `D(C_6^r) ≥ 5r + 1 + ⌊(r-1)/8⌋`, which would need a zero-sumfree sequence of 46 elements
over `C_6^9`. They give no construction or proof. We did not find one. What we tried (2026-11-26):

- **Smaller blocks in the paper's scheme (exhaustive, negative).** The proof of Theorem 1.1 only uses that
  each block `W` is zero-sumfree with deficit 1 and has three elements `c, a, d` whose pairwise sums
  cannot be cancelled. With blocks of rank 2 the rank would be `3·2 + 2 + 1 = 9`. `rho2.py` enumerates
  all 66,672 zero-sumfree sequences of length 9 in `C_6^2`: none has such a triple. (For n = 6 the
  scheme needs exactly 3 blocks.) The Auditor strengthened this: the scheme only needs the three block
  deficits to sum to 3, but blocks of rank 1 or 2 need deficit ≥ 2 (lengths 4, 5 in `C_6` and 9, 10 in
  `C_6^2` have no valid triple). Every rank split summing to 6, namely (2,2,2), (1,2,3) and (1,1,4), has two
  such blocks, so the deficits would be ≥ 4. **No version of the GGWZ scheme reaches rank 9 for n = 6.**
- **Structured families (solver/annealing, inconclusive).** Lower part = `j` copies of `W` and `8 - 4j`
  coordinates with 4 copies of the basis vector, plus `L = 46 - 19j - 4(8-4j)` top elements with
  `u`-coordinate 1 (`sa2.py`, `gensearch.py`, `boxsearch.py`):
  - `j = 1` (L = 11): best found leaves **1** of 252 required conditions unmet (many restarts).
  - `j = 0` (L = 14): best 1 unmet.
  - `j = 2` (L = 8): best 16 unmet.
  - All-basis lower parts with L = 8..10: CP-SAT proves infeasible when the deficit sits on one
    coordinate, and times out otherwise.
- Letting the top `u`-coefficients vary as well (`sa3.py`-style) made annealing worse.

The repeated near-miss at 1 suggests an obstruction in these families. A rank-9 example probably needs a
different gadget.
