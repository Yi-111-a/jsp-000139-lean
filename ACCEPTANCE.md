# ACCEPTANCE — JSP-000139

Catalog statement (JSP-000139, Graph theory, Current status: **Solved**, Lean proof: No
in the catalog as of the fetch below):

> **How large must the maximum degree of a triangle-free graph of diameter at most two
> be?**

Source: <https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000139>
(Problem description verbatim from the catalog detail table; record fetched 2026-09-30.)

The catalog points at Erdős–Pach Problem 1.3, recorded e.g. in Alon's remark
<https://web.math.princeton.edu/~nalon/PDFS/remark1901.pdf>: with `f(n)` the least
maximum degree of a triangle-free graph of diameter at most two on `n` vertices,

* Moore (1859) gives `f(n) ≥ √(n − 1)`;
* Hanson–Seyffarth (1984), Füredi–Seress (1994), Haviv–Levy (2018) give
  `f(n) ≤ (√2 + o(1))√n`, so `f(n) = Θ(√n)` — the order of growth is settled up to the
  constant `√2`; whether `f(n) = (1 + o(1))√n` remains open.

## Required theorem

`jsp_000139_main` — the Moore bound, i.e. the "how large **must** it be" half:

```lean
theorem jsp_000139_main (d : ℕ) (hG : TriangleFreeDiamTwo G) (hd : ∀ v : α, G.degree v ≤ d) :
    Fintype.card α ≤ d * d + 1
```

with `TriangleFreeDiamTwo G := G.CliqueFree 3 ∧ (∀ u ≠ v, u ~ v ∨ ∃ w, u ~ w ∧ w ~ v)`
on a finite vertex type `[Fintype α] [DecidableEq α]`.  Equivalently, over `ℝ`,
`Δ² ≥ n − 1` (`jsp_000139_main_real`).

## Supporting results proved in the same repository (all placeholder-free)

| name | content |
| --- | --- |
| `jsp_000139_moore_ball` | `\|V\| ≤ 1 + deg v + ∑_{w ∼ v} (deg w − 1)` for every `v` |
| `jsp_000139_main_perVertex` | `\|V\| ≤ 1 + deg v + deg v (d − 1)` |
| `jsp_000139_main_real` | `Δ² ≥ n − 1` over `ℝ` |
| `jsp_000139_main_tooMany` | more than `d² + 1` vertices is impossible |
| `card_distanceTwo`, `nbr_disjoint_of_adj`, `independent_neighborFinset`, `not_triangle` | the triangle-free combinatorics used above |
| `bipartite_diamTwo_adj'`, `bipartite_structure`, `bipartite_diamTwo`, `bipartite_noedge` | a bipartite triangle-free graph of diameter `≤ 2` is complete bipartite |
| `jsp_000139_bipartite_diamTwo` | in the bipartite case `max deg = max \|s\| \|t\| ≥ ⌈n/2⌉`, plus degrees `= ` opposite part |
| `jsp_000139_exists`, `completeBipartiteFin_cliqueFree`, `completeBipartiteFin_diam` | examples exist for every `n`; the balanced `K_{⌈n/2⌉,⌊n/2⌋}` is triangle-free of diameter `2` |

## Status of the Lean build

`lake build` succeeds, there are **0** `sorry`/`admit` placeholders, and
`jsp_000139_main` is a fully proved `theorem`.  `harness/score.py --strict-prize`
reports `prize_ready: true`.

Not formalised (see `discovery/JSP-000139/policy.json`): the `O(√n)` construction side,
i.e. symmetric complete sum-free sets in finite Abelian groups giving Cayley graphs of
diameter two with `Δ = O(√n)`.
