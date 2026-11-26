# audit/

The in-house Auditor's independent checkers. Written from the problem definitions, not from the
provers' code. Verdicts are in `../ledger/audits.md`.

| Script | Checks | Needs |
| --- | --- | --- |
| `erdos757_check.py` | Claim 757-1 witness: (4,5) property, largest Sidon subset = 7, the 3-APs | stdlib |
| `erdos757_check_n14.py` | Claim 757-2 witness: (4,5) property, largest Sidon subset = 8, the 12 3-APs | stdlib |
| `erdos757_five_ninths.py K0 K1` | Reader's 5/9 family S_K: literal (4,5) test, largest Sidon subset by HiGHS MILP | scipy |
| `erdos757_five_ninths_transfer.py` | 5/9 family: per-copy max-plus matrix, h(S_K) = 7 + 5K bound for all K | stdlib |
| `erdos757_five_ninths_nomix.py` | 5/9 family: own "no mixing" search (no relation spans copies 2+ apart) plus brute force on S_10 | stdlib |
| `c37_own_cert.py` | Claim C37-1 with the Auditor's own 17-multiplier certificate | stdlib |
| `c37_verify_pr5_cert.py <cert.json>` | PR 5's certificate file, using the Auditor's own forms | stdlib |
| `c37_find_own_cert.py` | How the multipliers in `c37_own_cert.py` were found (LP, then rationalised) | scipy |

Run with `python3 -I <script>`.
