# Why `D_ℓ ≠ U_ℓ` keeps happening: valleys at `f_t f_{t+1}`

Notes from an attempt at Aliabadi's question (arXiv 2609.04473, §6): is `D_ℓ ≠ U_ℓ` for infinitely many `ℓ`?
We did **not** prove this. These notes record an exact description of the down/up pattern, the place where
the differences come from, the numerical evidence, and why a proof looks hard.

## 1. An exact local rule

Write `δ = {φn}`. For each `t ≥ 2` the equation `a f_t + b f_{t-1} = n` has exactly one integer solution
with `0 ≤ Q := φb − a < φ^t`. (Solutions differ by `(f_{t-1}, −f_t)`, which changes `Q` by `φ^t`.) The same
computation as CGS Lemma 4.1 gives `Q = φ^t δ` for even `t` and `Q = φ^t (1 − δ)` for odd `t`. So `n` has CGS
parameter `t` exactly when this point lies in the triangle `1 ≤ a ≤ b ≤ f_t`. Solving for `a, b` in terms of
`(n, Q)` turns the triangle into three linear inequalities:

```
a ≤ b   ⇔  Q ≥ n / (φ f_{t+1})
a ≥ 1   ⇔  Q ≤ (φ n − φ^t) / f_{t-1}
b ≤ f_t ⇔  Q ≤ φ^t − n / f_t
```

`check_rule.py` confirms this rule against the CGS representation for every `n < 30000` (exact decimal
arithmetic).

So inside a stretch of integers, "family `t`" is the set of `n` whose `δ` falls in an interval
`I_t(n)`. Its endpoints move linearly and slowly with `n`. With `s = √5 n / φ^{2t}`, the interval is roughly
`[s/φ², min(φ² s, 1 − s)]` (for `δ` if `t` is even, for `1 − δ` if `t` is odd). Consecutive even
families tile `[0, c(n))` without gaps, and the odd families tile `(c(n), 1)`. Hence:

> **`n` is a down-integer iff `{φn} < c(n)`**, where the cut `c(n)` is continuous and piecewise linear in
> `n`. It oscillates between `η = 1/(√5φ) ≈ 0.276` and `ρ = 1 − η ≈ 0.724`, with period `φ⁴` on a log scale.

`adelta`-style listings (sort a stretch of integers by `{φn}` and print the types) show this directly: one
block of `D`s, then one block of `U`s, mixing only where the moving cut sweeps through.

## 2. Peaks and valleys, and the asymmetry

* **Falling phase** (family `t` dying because `b ≤ f_t` binds): `c(n) = 1 − n/(f_t φ^t)`.
* **Rising phase** (family `t + 2` being born because `a ≥ 1` binds): `c(n) = (φn − φ^{t+2})/(f_{t+1} φ^{t+2})`.

For even `t` the cut reaches its minimum `η` (a **valley**: down-integers are sparsest) at
`n = f_t f_{t+1}`, the largest member of family `t` (for example 104, 714, 4895). For odd `t` the same
point is a valley of the up-integers (273, 1870, ...). Near a down-valley the cut falls with slope
`1/(f_t φ^t)` and rises with slope `1/(f_{t+1} φ^{t+1})`, which is about `φ²` times gentler. The symmetry
that swaps the types (reverse the window, `D ↔ U`, `δ ↔ 1 − δ`) turns this into a valley that falls
gently and rises steeply. The up-valleys have the other shape. So **down-valleys and up-valleys have
mirror-image shapes**, and nothing maps one onto the other. Away from valleys and peaks the two types
have exactly the same local parameter space (`δ` anywhere, cut anywhere in `[η, ρ]`). That is why the
gap sets agree "mostly" and differ only in a few gaps.

To leading order the shapes do not matter. For example, the largest `ℓ`-step gap only depends on
`pq/(p+q)` for valley slopes `p, q`, which is symmetric. This matches the data: `min D_ℓ = min U_ℓ` and
`max D_ℓ = max U_ℓ` for every `ℓ` we checked. The differences are holes in the middle of the range.

## 3. Evidence

`valley_differences.py 700000 1 300` (all members below 700,000, windows ending below 233,333):

* `D_ℓ ≠ U_ℓ` for **every** `ℓ` from 15 to 300, and for `ℓ = 4, 7, 8, 9, 12`. No difference shows up
  for `ℓ = 1, 2, 3, 5, 6, 10, 11, 13, 14`.
* Almost every difference first occurs in a window starting at `n = f_t (a + f_{t-1})` (the line
  `b = f_t`, so just before the valley `f_t f_{t+1}`), with a start offset that is a multiple of `f_t`. A
  down-only gap comes from an even `t`, an up-only gap from an odd `t`.
* Valley `t` first contributes at `ℓ ≈ f_t` (`t = 8, 9, 10, 11, 12, 13`: first `ℓ` = 26, 36, 51, 94, 158,
  201). This is the scale where the moving cut matters: over a window of length `g ≈ φ^t` the cut moves
  by about `1/g`, the resolution of the rotation.

A difference seen only up to a cutoff could in principle be realised later. The cutoff is safe for the
small cases: they are certified by the constraint method (`differences.md`) and Lean-proved for
`ℓ = 4, 7, 8`.

## 4. A route to "infinitely many", and why it is hard

1. Rotation by `φ` renormalizes exactly at Fibonacci scales, and `δ(f_t f_{t+1}) → η` or `ρ` (`η ∈ ℚ(√5)`
   has an eventually periodic Ostrowski expansion). So the down pattern in a window of length `K f_t` around
   the valley `f_t f_{t+1}` should stabilise as `t → ∞` (even `t`), after rescaling by `f_t`. The same holds
   for up-valleys (odd `t`). This would give explicit families `ℓ_t, g_t`, linear in `f_t, f_{t-1}`.
2. One would then show `g_t ∉ U_{ℓ_t}`. Up-windows of length about `g_t` at much larger scales see a
   straight cut, so this needs `(ℓ_t, g_t)` to lie outside the straight-cut gap set for every cut
   `c ∈ [η, ρ]`, every phase, and every exact boundary case. It also needs the same exclusion against
   up-valleys, up-peaks and comparable scales.

Step 2 is a uniform statement about infinitely many linear systems, and it involves second-order
effects. We did not find a slicker invariant (min/max gaps, counts, parity) that separates the types.
This is where the attempt is parked. It is worth reopening if someone finds such an invariant, or wants
to carry out the renormalization by hand.
