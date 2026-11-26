# List Total Colouring Conjecture: independent Python checks

Plain-Python cross-checks for `Lab/ListTotal/Counterexample.lean` (they are not part of the proof).

- `no_list_colouring.py`: builds Noel's graph and list assignment from scratch, checks the graph is cubic
  with 30 edges and all lists have size 4, then runs an exhaustive backtracking search
  (most-constrained-first). Output: `colourable from L: False` after about 2.1 million nodes.
- `final_step.py`: the last step of the proof. For every choice of private colours `s_i ≠ i`, some cross
  edge has no colour in `{i, s_i} ∩ {j, s_j}` ∩ its list. Output: `satisfiable s: 0`.
- `four_colouring.py`: checks the paper's total 4-colouring and prints it in the 0-based form used in Lean.

Run with `python3 -I <file>`.
