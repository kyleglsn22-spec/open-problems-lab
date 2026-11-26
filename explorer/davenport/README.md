# Davenport constant: GGWZ counterexample to van Emde Boas–Kruyswijk

- `build.py K` builds the zero-sumfree sequence of Gao–Geroldinger–Wang–Zeng (arXiv:2611.24775 v3)
  over `C_{2K}^{5K}`, of length `5K(2K-1)+1`, one more than the conjecture allows.
- `check_cpsat.py K` asks CP-SAT for a nonempty zero-sum sub-multiset. `INFEASIBLE` = zero-sumfree.
  It also runs controls (one extra copy of an element must create a zero sum).
- `logs_k3.txt`, `logs_k5.txt`: outputs for n = 6 and n = 10 (each solves in well under a second).

Requires `pip install ortools`. The Lean proof for n = 6 is `Lab/Davenport/VanEmdeBoasKruyswijk.lean`.
