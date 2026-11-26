# Explorer

Search code and certificates, one folder per problem. Each certificate ships with:

1. the certificate file (the set, graph, polynomial or function found),
2. a checker using exact arithmetic (no floating point in the final check),
3. a second, independently written checker from the Auditor before the ledger marks it checked.

Existing public data to start from:
- Erdős #757 small cases (exact f(n) for n ≤ 15 and n = 17, 19, 21, with explicit sets and a checker):
  https://github.com/JeetuSK0808/tao-constants-certificates/tree/afa2e1010cd5f36cfbad213dc83b9568fe77f934/c5b-erdos757-small-n
- Degree 4 / sensitivity 10 impossibility certificate (method to reuse for degree 5):
  https://github.com/DennisKoshta/c37-degree-sensitivity-certificate/tree/472e2d95c85fe681826e70c90bc60a05ab5c0bc3
