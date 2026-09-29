# JSP-000139

**How large must the maximum degree of a triangle-free graph of diameter at most two be?**

Catalog record: <https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000139>
(Graph theory; Current status *Solved*; Lean proof *No*; "No later than 1997 (bibliographic
evidence)".  Publications cited by the catalog: Er97b, HaSe84 "k-saturated graphs of
prescribed maximum degree", HaLe18 "Symmetric complete sum-free sets in cyclic groups",
FuSe94 "Maximal triangle-free graphs with restrictions on the degrees", plus Alon's remark
1901.)

The question is Erdős–Pach Problem 1.3: writing `f(n)` for the least maximum degree of a
triangle-free graph of diameter at most two on `n` vertices, what is the order of growth
of `f(n)`?  Known: `f(n) ≥ √(n−1)` (Moore 1859) and `f(n) ≤ (√2 + o(1))√n`
(Hanson–Seyffarth 1984, Füredi–Seress 1994, Haviv–Levy 2018), so `f(n) = Θ(√n)`; whether
`f(n) = (1+o(1))√n` is still open.  Alon's remark also records the Erdős–Gyárfás problem
that a triangle-free graph of maximum degree `≤ n^{1/2−ε}` can be completed to diameter
two by adding `O(n^{2−ε})` edges (Theorem 1.2 of the remark).

Formalisation status in this repository: the lower bound ("how large must it be") is
proved in full — `jsp_000139_main`: a triangle-free graph of diameter `≤ 2` with maximum
degree `≤ d` has at most `d² + 1` vertices.  Also proved: the sharp bipartite
dichotomy (a bipartite triangle-free graph of diameter `≤ 2` is complete bipartite, so
`Δ ≥ ⌈n/2⌉`) and the existence of examples for every `n`.  The `O(√n)` construction side
is not formalised.  See `ACCEPTANCE.md`.
