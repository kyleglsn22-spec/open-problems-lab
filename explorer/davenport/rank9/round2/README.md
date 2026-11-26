# Rank-9 search, round 2 (2026-11-26): new layouts, still no counterexample below rank 15

Goal: a zero-sumfree sequence over `C_6^r` of length `5r + 1` with `r < 15` (the GGWZ v3 Remark claims
`r = 9` without proof). **Nothing was found.** Everything below is either a proof of impossibility for a
specific layout or a search that came back empty. Search negatives are not proofs.

## Setting

Every layout here has the shape used by GGWZ: a lower part that is a direct sum of zero-sumfree
"components" `W_j` (ranks `b_j`, deficits `δ_j`, where a deficit-`δ` component has `5b_j − δ` terms),
plus `m = 6 + Σδ_j` "top" terms that all have coordinate 1 on one extra cyclic summand `⟨u⟩`. With
`m ≤ 11`, a zero sum must use exactly 0 or 6 top terms, so the whole sequence is zero-sumfree iff
**every 6-subset `T` of the top terms is blocked by some component**, meaning `−σ_j(T) ∉ Σ₀(W_j)`
(`Σ₀` = subsequence sums including the empty one). The length is exactly `5r + 1`.

## 1. The paper's scheme is looser than it looks (`req.py`, `minreq.py`, `ach.py`)

Keep the GGWZ top terms for `k = 3` (center, leaves `a_i, d_i`, the `u + vF_i` leaves, two `F`
coordinates) and treat each block abstractly by the set `M_i` of selection patterns
`(x, α, δ) ∈ {0,1}³` that it blocks. Enumerating all 6-subsets (`req.py`, 93 pattern triples) gives:

- If all three blocks are alike, the paper's condition (block every size-2 selection) is the unique
  minimal one.
- **But the blocks need not be alike.** Two of the blocks only need to block the pattern `(0,1,1)`,
  which a rank-1 block `e⁴` already does. The third block must then block
  `{011, 100, 101, 110, 111}`, i.e. there must be `x, y, z` with
  `x, x+y, x+z, y+z, x+y+z ∉ Σ₀(W)` (the "5-condition"). With a rank-4 third block this layout has
  rank `1 + 1 + 4 + 2 + 1 = 9`, exactly the rank of the Remark.

So a rank-9 counterexample would follow from a zero-sumfree length-19 sequence in `C_6^4` with the
5-condition. The paper's own block fails it (`cond5.py`).

## 2. Searching for blocks

| Search | Size | Result |
|---|---|---|
| Rank-3 blocks (length 14 in `C_6^3`) with the paper's 3-condition (would give rank 12): random greedy (`r3b.c` and an earlier variant) | 20M+ samples | none |
| Same, randomized DFS (`dfs4.c 3 14 … 3`) | 2.5M sequences | none |
| Same, structured family `e_j^{m1}(e_j+λf)^{m2}`, `f^α`, one free term `z` (`fam.c 3 0`) | 77,358 zero-sumfree blocks | none |
| Rank-4 blocks, same structured family with `z` restricted (`fam.c 4 1`) | 1,377,037 zero-sumfree blocks | 3-condition: 4 hits, all of the paper's own type (calibration OK). **5-condition: 0** |
| Rank-4 blocks, randomized DFS (`dfs4.c 4 19 … 5`) | 76k | none (but this sampler also misses the paper's block, so it is weak evidence) |

## 3. Other layouts, exact solver (`satmodel.py`, CaDiCaL)

The SAT model takes the components' blocking sets as input and searches over all top terms
(first top term fixed to 0, which loses nothing since adding a constant to all top terms changes each
6-sum by 6·w = 0).

| Layout | rank | m | Result |
|---|---|---|---|
| two copies of the paper's rank-4 block | 9 | 8 | **UNSAT (proved, 33 s)** |
| paper's block + 2 deficit-1 coordinates | 7 | 9 | timeout (40 min) |
| paper's block + 3 deficit-1 coordinates | 8 | 10 | timeout (40 min) |
| paper's block + 4 deficit-1 coordinates | 9 | 11 | timeout (40 min) |
| two copies of the paper's block + 1 coordinate | 10 | 9 | timeout (40 min) |

Calibration warning: on the known rank-15 GGWZ layout, neither this SAT model (10 min), CP-SAT
(2 min, also with a label-palette encoding), nor a simulated-annealing search (`ls.c`, best 32
unblocked subsets) found the known solution. The timeouts above therefore say nothing either way.

## Takeaways

- Proved: the "two rank-4 blocks, 8 top terms" route to rank 9 is impossible with the paper's block.
- New reduction: rank 9 would follow from a rank-4 block with the 5-condition. None exists in the
  1.38M-block structured family, which does contain the paper's block.
- Generic solvers can't even rediscover the rank-15 construction, so a rank-9 example, if it exists,
  probably needs a hand-made gadget, as GGWZ's did. The most promising next step is to get the authors'
  construction (the Remark has no proof), and the lab has already emailed them.
