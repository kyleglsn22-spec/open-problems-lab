# Formalizing Henning–Yeo (for an unconditional 9/17, Erdős #757)

Goal: remove the hypothesis `HenningYeoBound` from `Lab/Erdos757/LowerBound.lean`.

Source: M. A. Henning, A. Yeo, *Affine Planes and Transversals in 3-Uniform Linear Hypergraphs*,
Graphs Combin. 37 (2021) 867–890 (paywalled; the lab has a private copy, not committed).

## Structure of the proof

* **Theorem 7** (`17τ ≤ 5n + 3m`, what Ma–Tang use) follows from **Theorem 6**
  (`17τ ≤ 4n + 4m + h`, `h` = number of isolated edges) by deleting vertices of degree ≥ 4 and
  using `m + h ≤ n` when all degrees are ≤ 3. **Done in Lean**: `Lab/HenningYeo/Theorem7.lean`,
  and `Lab/Erdos757/Unconditional.lean` gives `Theorem6Bound ℝ → 9/17 ≤ sSup`.
* **Theorem 6** is a minimal-counterexample argument (Claims 1–15) over linear 3-uniform
  `F₇`-free hypergraphs, using deletions `H - X`, a few edge additions, the small hypergraphs
  `E₃`, `F₇`, `H₁₀`, `H₁₀'`, and one outside result:
  * **Lemma 1** (Frendrup–Vestergaard–Yeo 2009) for 2-regular hypergraphs. Only the weaker
    `17τ < 4n + 4m` is needed. In the dual cubic graph `G` (`N` vertices) this says the edge
    cover number is `< 10N/17`, i.e. a matching of size `> 7N/17`. Plan: Tutte–Berge style
    count from Mathlib's `SimpleGraph.tutte` (odd components of `G - U` send an odd number of
    edges to `U`; one that sends a single edge has ≥ 5 vertices), giving `ν ≥ 13N/30`.

## A gap in the published proof, and the fix we use

Theorem 6 also claims strict inequality when `H` has no exceptional vertex, and the induction
needs that strictness (Claim 6). The minimal-counterexample proof splits into type 1
(`17τ > w`) and type 2 (`17τ = w`, no exceptional vertex). After Claim 4 (`δ ≥ 2`) the paper
says "implying that H is of type-1", but no reason is given, and several later reductions
(e.g. Claims 6, 7.3, 7.5, 11.1, 13) only give `17τ ≤ w`, which does not exclude type 2.

Fix: prove the strict bound only for hypergraphs **with a vertex of degree 1** and no
exceptional vertex. That is all Claim 6 uses (the component `H_y` contains `y`, of degree 1),
Claims 1–4 still work for both types (they use favorable reductions), and now `δ ≥ 2` really
does rule out type 2. Random tests on small hypergraphs (n ≤ 11) found no counterexample to
the original strict statement either.

## Checkpoints

1. Infrastructure + Theorem 7 from Theorem 6 (this PR).
2. Small hypergraphs (`E₃`, `F₇`, `H₁₀`, `H₁₀'`), exceptional vertices, weight bookkeeping for
   `H - X`.
3. The 2-regular case (matching bound for cubic graphs).
4. Claims 1–5, then 6–10, then 11–15; Theorem 6; unconditional `9/17`.

## A second issue: the definition of `H₁₀` is ambiguous (2026-11-26)

The text builds `H₁₀` from `F₇` by deleting a (2,2,3)-edge `e` and adding `x₁,x₂,x₃` with
`e₁ ⊆ {x₂} ∪ e`, `e₂ ⊆ {x₃} ∪ e`, `|e₁ ∩ e₂| = 1`, without saying which vertex of `e` is the
common one. If it is the centre of `F₇` the result has a vertex of degree 4 and is not
isomorphic to the other choice, yet it is also tight: `n = 10`, `m = 7`, `τ = 4`, `17τ = 68 = w`,
linear, `F₇`-free, with a degree-1 vertex (checked by brute force). So read literally with one
fixed graph, the strict part of Theorem 6 is false; Claim 4.5 really produces every choice.
Fix: we treat "H₁₀ or H₁₀'" as the whole family (any line of `F₇`, any common vertex). The later
claims only use that the common vertex has degree ≥ 3 and that there is one degree-1 vertex,
which holds for every member.

## Status (2026-11-26): done

The Theorem 6 bound (first half; the strict part in the corrected, weaker form above) is in Lean (`Lab/HenningYeo/Theorem6.lean`, `theorem6 : Theorem6Bound α`), and
`Lab/Erdos757/Unconditional.lean` derives the unconditional `9/17` (claim 757-4). Notes:
* Claim 10's finite check on the `H₁₀` templates is split into 15 small `decide` files (one
  `H₁₀` choice per lemma) so the kernel re-check of each stays under ~7.4 GB.
* Claim 11 follows the paper but with one shared 5-vertex reduction (`C11.red5`) for Claim 11.2
  and the last step; the choice of `a₁, a₂, q` only needs `|Q| ≤ 3`.
* Claim 13's hypothesis is `m - m' ≥ 8` (the symbol is lost in some text extractions).

