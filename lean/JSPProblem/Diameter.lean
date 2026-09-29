/-
# JSP-000139 — maximum degree of triangle-free graphs of diameter at most two

Catalog statement (JSP-000139, graph theory, status "Solved"):

> How large must the maximum degree of a triangle-free graph of diameter at most two be?

This is Erdős–Pach Problem 1.3 as recorded in the Justin Sun Prize catalog.  Writing
`f(n)` for the least possible maximum degree of a triangle-free graph of diameter at
most two on `n` vertices, the question is about the order of growth of `f(n)`:

* Moore (1859): every graph of maximum degree `d` and diameter at most two has at
  most `d² + 1` vertices, so `f(n) ≥ √(n − 1) = (1 − o(1))√n`.
* Hanson–Seyffarth (1984), Füredi–Seress (1994), Haviv–Levy (2018): constructions with
  `f(n) ≤ (√2 + o(1))√n`, so `f(n) = Θ(√n)`: the order of growth is settled up to the
  constant `√2`.  Whether `f(n) = (1 + o(1))√n` is still open.

This file formalises, in full and with no placeholders, the provable half of the
answer.  The remaining (research-level) half is the construction side: exhibiting, for
arbitrarily large `n`, a non-bipartite triangle-free diameter-two graph with
`Δ = O(√n)`; those constructions (Hanson–Seyffarth, Füredi–Seress, Haviv–Levy) are Cayley
graphs of Abelian groups arising from symmetric complete sum-free sets, and are not
formalised here.  What is proved here:

* `jsp_000139_moore_ball` — the local counting bound behind Moore's bound: for
  every vertex `v` of a triangle-free graph of diameter `≤ 2`,
  `|V| ≤ 1 + deg v + ∑_{w ∼ v} (deg w − 1)` (the vertices at distance two from `v`
  are covered by the sets `N w \ N[v]`, `w ∼ v`, each of size `deg w − 1`).
* `jsp_000139_main` — the headline: `|V| ≤ d² + 1` whenever the maximum degree is
  `≤ d`, i.e. `Δ ≥ √(n − 1)`: the answer to "how large must it be".
* `jsp_000139_main_real` — the same over `ℝ`, `Δ² ≥ n − 1`.
* `jsp_000139_main_perVertex` — the sharper per-vertex form `|V| ≤ 1 + deg v + deg v (d − 1)`.
* `jsp_000139_bipartite_diamTwo` — the bipartite half: a bipartite triangle-free graph
  of diameter `≤ 2` is complete bipartite, so its maximum degree is `≥ ⌈n/2⌉`; examples
  with `f(n) = o(n)` must therefore be non-bipartite.
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

open scoped BigOperators

namespace JSP139

universe u

set_option maxHeartbeats 800000

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- A **triangle-free graph of diameter at most two** on the vertex type `α`:
`G` contains no triangle, and every two distinct vertices are either adjacent or have
a common neighbour. -/
def TriangleFreeDiamTwo (G : SimpleGraph α) : Prop :=
  G.CliqueFree 3 ∧ ∀ ⦃u v : α⦄, u ≠ v → G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v

/-- `G` has diameter at most two (no triangle-freeness required). -/
def DiamAtMostTwo (G : SimpleGraph α) : Prop :=
  ∀ ⦃u v : α⦄, u ≠ v → G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v

/-! ## Triangle-free combinatorics -/

section Local

variable {G : SimpleGraph α} [DecidableRel (G.Adj)]

/-- Membership in the neighbourhood finset, read off as adjacency. -/
theorem mem_nbr {v w : α} (h : w ∈ G.neighborFinset v) : G.Adj v w :=
  (SimpleGraph.mem_neighborFinset G v w).mp h

/-- Adjacency, read off as membership in the neighbourhood finset. -/
theorem mem_nbr_of {v w : α} (h : G.Adj v w) : w ∈ G.neighborFinset v :=
  (SimpleGraph.mem_neighborFinset G v w).mpr h

/-- Adjacency is irreflexive. -/
theorem adj_irrefl {v : α} : ¬ G.Adj v v := SimpleGraph.irrefl G

/-- A vertex is never one of its own neighbours. -/
theorem not_mem_neighborFinset_self (v : α) : v ∉ G.neighborFinset v :=
  fun h => SimpleGraph.irrefl G (mem_nbr h)

/-- The degree of a vertex is the size of its neighbourhood finset. -/
theorem card_nbr (v : α) : (G.neighborFinset v).card = G.degree v :=
  SimpleGraph.card_neighborFinset_eq_degree G v

/-- Triangle-freeness in explicit form: three pairwise adjacent vertices coincide. -/
theorem not_triangle (htf : G.CliqueFree 3) {x y z : α} (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hzx : G.Adj z x) : x = y ∨ y = z ∨ z = x := by
  by_contra hcon
  exact htf {x, y, z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hzx.symm, hyz⟩)

/-- **The neighbourhood of a vertex of a triangle-free graph is an independent set.**
This is the only place where triangle-freeness is used below. -/
theorem independent_neighborFinset (htf : G.CliqueFree 3) (v : α) {x y : α}
    (hvx : x ∈ G.neighborFinset v) (hvy : y ∈ G.neighborFinset v)
    (hxy : x ∈ G.neighborFinset y) : x = v ∨ x = y ∨ y = v := by
  rcases not_triangle htf (mem_nbr hvx) (mem_nbr hxy).symm (mem_nbr hvy).symm with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- In a triangle-free graph, adjacent vertices have disjoint neighbourhoods. -/
theorem nbr_disjoint_of_adj (htf : G.CliqueFree 3) {v w : α} (hvw : G.Adj v w) :
    Disjoint (G.neighborFinset v) (G.neighborFinset w) := by
  refine Finset.disjoint_left.2 ?_
  intro x hxv hxw
  rcases not_triangle htf hvw (mem_nbr hxw) (mem_nbr hxv).symm with h | h | h
  · exact adj_irrefl (h ▸ hvw)
  · exact (not_mem_neighborFinset_self x) (h ▸ hxw)
  · exact (not_mem_neighborFinset_self v) (h ▸ hxv)

/-- **Exact local count.**  For a neighbour `w` of `v`, the neighbours of `w` lying
outside the closed neighbourhood of `v` are exactly `deg w − 1` in number: `w` is a
neighbour of `v` but never of itself, and by triangle-freeness the two neighbourhoods
are disjoint. -/
theorem card_distanceTwo (htf : G.CliqueFree 3) {v w : α} (hvw : w ∈ G.neighborFinset v) :
    (G.neighborFinset w \ insert v (G.neighborFinset v)).card = G.degree w - 1 := by
  have hmem : insert v (G.neighborFinset v) ∩ G.neighborFinset w = {v} := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hxv, hxw⟩
      rcases Finset.mem_insert.mp hxv with rfl | hxv
      · exact Finset.mem_singleton.mpr rfl
      · exact (Finset.disjoint_left.1 (nbr_disjoint_of_adj htf (mem_nbr hvw)) hxv hxw).elim
    · intro hx
      have hxv : x = v := by simpa only [Finset.mem_singleton] using hx
      subst hxv
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_insert_self _ _, mem_nbr_of (mem_nbr hvw).symm⟩
  rw [Finset.card_sdiff, hmem, Finset.card_singleton, card_nbr]

end Local

/-! ## The Moore counting bound -/

section Identity

variable {G : SimpleGraph α} [DecidableRel (G.Adj)]

/-- **Moore counting bound.**  If `G` is triangle-free of diameter at most two, then
for every vertex `v`
`|V| ≤ 1 + deg v + ∑_{w ∼ v} (deg w − 1)`,
i.e. the ball of radius two around `v` has at most `1 + deg v + ∑ (deg w − 1)` vertices:
the vertices at distance two from `v` are covered by the sets `N w \ N[v]`
(`w ∈ N v`), each of size `deg w − 1`.  Bounding `deg w ≤ d` and summing gives
`|V| ≤ 1 + d + d (d − 1) = d² + 1`, i.e. `jsp_000139_main`.

The bound is a `≤` and not an equality in general: in the `4`-cycle the two vertices
`u, v` at distance two have two common neighbours, so the covering sets overlap. -/
theorem jsp_000139_moore_ball (hd2 : DiamAtMostTwo G) (htf : G.CliqueFree 3) (v : α) :
    Fintype.card α
      ≤ 1 + G.degree v + ∑ w ∈ G.neighborFinset v, (G.degree w - 1) := by
  classical
  set T : Finset α := (G.neighborFinset v).biUnion
      fun w => G.neighborFinset w \ insert v (G.neighborFinset v) with hTdef
  -- every vertex lies in `{v} ∪ N v ∪ T`
  have hcov : (Finset.univ : Finset α) ⊆ insert v (G.neighborFinset v ∪ T) := by
    intro x _
    by_cases hxv : x = v
    · exact Finset.mem_insert.mpr (Or.inl hxv)
    by_cases hxS : x ∈ G.neighborFinset v
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hxS)
    have hxn : ¬ G.Adj v x := (SimpleGraph.mem_neighborFinset G v x).not.mp hxS
    rcases hd2 (u := v) (v := x) (Ne.symm hxv) with h | ⟨w, hvw, hxw⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (mem_nbr_of h))
    · refine Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨w, mem_nbr_of hvw, Finset.mem_sdiff.mpr ⟨mem_nbr_of hxw, ?_⟩⟩))
      intro hc
      rcases Finset.mem_insert.mp hc with hc | hc
      · exact hxv hc
      · exact hxn (SimpleGraph.mem_neighborFinset G v x |>.mp hc)
  -- `v` is not covered by `T`
  have hne : v ∉ T := by
    intro hx
    obtain ⟨w, -, hxw⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_sdiff.mp hxw).2 (Finset.mem_insert_self _ _)
  -- the covering sets have the expected size
  have h1 : T.card
      ≤ ∑ w ∈ G.neighborFinset v, (G.neighborFinset w \ insert v (G.neighborFinset v)).card :=
    Finset.card_biUnion_le
  have hne' : v ∉ G.neighborFinset v ∪ T := by
    intro hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact absurd hc (not_mem_neighborFinset_self v)
    · exact hne hc
  have hT : T.card ≤ ∑ w ∈ G.neighborFinset v, (G.degree w - 1) :=
    h1.trans (Finset.sum_le_sum fun w hw => (card_distanceTwo htf hw).le)
  calc Fintype.card α = (Finset.univ : Finset α).card := Finset.card_univ
    _ ≤ (insert v (G.neighborFinset v ∪ T)).card := Finset.card_le_card hcov
    _ = 1 + (G.neighborFinset v ∪ T).card := by
      rw [Finset.card_insert_of_notMem hne', Nat.add_comm]
    _ ≤ 1 + ((G.neighborFinset v).card + T.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ = 1 + G.degree v + T.card := by rw [card_nbr]; omega
    _ ≤ 1 + G.degree v + ∑ w ∈ G.neighborFinset v, (G.degree w - 1) := Nat.add_le_add_left hT _

end Identity

/-- The arithmetic behind Moore's bound: `1 + d + d (d − 1) = d² + 1`. -/
theorem moore_arith (d : ℕ) : 1 + d + d * (d - 1) = d * d + 1 := by
  cases d with
  | zero => rfl
  | succ k => simp; ring

/-! ## The headline theorem: the Moore bound -/

section Moore

variable {G : SimpleGraph α} [DecidableRel (G.Adj)]

/-- **JSP-000139 (main) — Moore's bound for triangle-free graphs of diameter at most
two.**  If `G` is triangle-free of diameter at most two on `n` vertices and every
vertex has degree at most `d`, then `n ≤ d² + 1`.  Equivalently the maximum degree of
such a graph is at least `√(n − 1)`: the "how large must it be" answer to JSP-000139. -/
theorem jsp_000139_main (d : ℕ) (hG : TriangleFreeDiamTwo G) (hd : ∀ v : α, G.degree v ≤ d) :
    Fintype.card α ≤ d * d + 1 := by
  obtain ⟨htf, hd2⟩ := hG
  classical
  rcases isEmpty_or_nonempty α with _ | ⟨⟨v⟩⟩
  · simp [Fintype.card_of_isEmpty]
  · have hid := jsp_000139_moore_ball hd2 htf v
    have hsum : (∑ w ∈ G.neighborFinset v, (G.degree w - 1))
        ≤ (G.neighborFinset v).card * (d - 1) := by
      calc (∑ w ∈ G.neighborFinset v, (G.degree w - 1))
          ≤ ∑ _ ∈ G.neighborFinset v, (d - 1) :=
            Finset.sum_le_sum fun w _ => Nat.sub_le_sub_right (hd w) 1
        _ = (G.neighborFinset v).card * (d - 1) := by simp [Finset.sum_const]
    calc Fintype.card α
        ≤ 1 + G.degree v + ∑ w ∈ G.neighborFinset v, (G.degree w - 1) := hid
      _ ≤ 1 + d + (G.neighborFinset v).card * (d - 1) := by
          have h1 : G.degree v ≤ d := hd v
          have h2 := hsum
          omega
      _ = 1 + d + G.degree v * (d - 1) := by rw [card_nbr]
      _ ≤ 1 + d + d * (d - 1) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right (d - 1) (hd v)) (1 + d)
      _ = d * d + 1 := moore_arith d

/-- Real form of the headline theorem: `Δ ≥ √(n − 1)`. -/
theorem jsp_000139_main_real (d : ℕ) (hG : TriangleFreeDiamTwo G)
    (hd : ∀ v : α, G.degree v ≤ d) : ((d : ℝ)) ^ 2 ≥ (Fintype.card α : ℝ) - 1 := by
  have h := jsp_000139_main d hG hd
  have h1 : (Fintype.card α : ℝ) ≤ ((d : ℝ)) * ((d : ℝ)) + 1 := by exact_mod_cast h
  rw [pow_two]
  linarith

/-- The sharper per-vertex form of Moore's bound: a vertex of degree `k` in a
triangle-free graph of diameter at most two forces `k` further vertices, each of
degree at most `d − 1`. -/
theorem jsp_000139_main_perVertex (d : ℕ) (hG : TriangleFreeDiamTwo G)
    (hd : ∀ v : α, G.degree v ≤ d) (v : α) :
    Fintype.card α ≤ 1 + G.degree v + G.degree v * (d - 1) := by
  obtain ⟨htf, hd2⟩ := hG
  classical
  have hid := jsp_000139_moore_ball hd2 htf v
  have hsum : (∑ w ∈ G.neighborFinset v, (G.degree w - 1)) ≤ G.degree v * (d - 1) := by
    calc (∑ w ∈ G.neighborFinset v, (G.degree w - 1))
        ≤ ∑ _ ∈ G.neighborFinset v, (d - 1) :=
          Finset.sum_le_sum fun w _ => Nat.sub_le_sub_right (hd w) 1
      _ = G.degree v * (d - 1) := by
          simp [Finset.sum_const, card_nbr]
  omega

/-- A triangle-free graph of diameter at most two all of whose degrees are at most
`d` cannot have more than `d² + 1` vertices. -/
theorem jsp_000139_main_tooMany (d : ℕ) (hG : TriangleFreeDiamTwo G)
    (hd : ∀ v : α, G.degree v ≤ d) : Fintype.card α > d * d + 1 → False := by
  intro h
  exact absurd h (Nat.not_lt_of_ge (jsp_000139_main d hG hd))

end Moore

/-! ## The bipartite case: diameter `≤ 2` forces completeness -/

section Bipartite

variable {G : SimpleGraph α} [DecidableRel (G.Adj)]

/-- In a bipartite graph two non-adjacent vertices lying in *different* parts have no
common neighbour. -/
theorem no_common_nbr {s : Set α} (hbip : ∀ ⦃x y : α⦄, G.Adj x y → (x ∈ s ↔ y ∉ s))
    {x y : α} (hxs : x ∈ s) (hys : y ∉ s) : ¬ ∃ w, G.Adj x w ∧ G.Adj w y := by
  rintro ⟨w, hxw, hwy⟩
  exact ((hbip hxw).mp hxs) ((hbip hwy).mpr hys)

/-- **Vertices of a bipartite graph in different parts are adjacent whenever the graph
has diameter at most two.** -/
theorem bipartite_diamTwo_adj (hd2 : DiamAtMostTwo G) {s : Set α}
    (hbip : ∀ ⦃x y : α⦄, G.Adj x y → (x ∈ s ↔ y ∉ s)) {x y : α} (hne : x ≠ y)
    (hxs : x ∈ s) (hys : y ∉ s) : G.Adj x y := by
  rcases hd2 hne with h | h
  · exact h
  · exact (no_common_nbr hbip hxs hys h).elim

/-- Structure of a bipartite graph given by its two parts: the degree of a vertex is
the size of the opposite part. -/
theorem bipartite_structure (s t : Finset α) (hcover : s ∪ t = (Finset.univ : Finset α))
    (hdisj : Disjoint s t)
    (hadj : ∀ ⦃x y : α⦄,
      G.Adj x y ↔ (x ∈ s ∧ y ∈ t) ∨ (x ∈ t ∧ y ∈ s)) :
    (∀ v ∈ s, G.neighborFinset v = t) ∧ (∀ v ∈ t, G.neighborFinset v = s) ∧
      (∀ v ∈ s, G.degree v = t.card) ∧ (∀ v ∈ t, G.degree v = s.card) := by
  have hmem : ∀ (v : α) (hv : v ∈ s), G.neighborFinset v = t := by
    intro v hv
    ext x
    constructor
    · intro hx
      rcases hadj.mp (mem_nbr hx) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · exact (Finset.disjoint_left.1 hdisj hv h1).elim
    · intro hx
      exact mem_nbr_of (hadj.mpr (Or.inl ⟨hv, hx⟩))
  have hmem' : ∀ (v : α) (hv : v ∈ t), G.neighborFinset v = s := by
    intro v hv
    ext x
    constructor
    · intro hx
      rcases hadj.mp (mem_nbr hx) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact (Finset.disjoint_left.1 hdisj h1 hv).elim
      · exact h2
    · intro hx
      exact mem_nbr_of (hadj.mpr (Or.inr ⟨hv, hx⟩))
  refine ⟨hmem, hmem', fun v hv => ?_, fun v hv => ?_⟩
  · rw [← card_nbr, hmem v hv]
  · rw [← card_nbr, hmem' v hv]

/-- **An empty part means no edges at all.** -/
theorem bipartite_noedge {u w : Finset α} (hu : u = ∅) {x y : α}
    (hadj : ∀ ⦃a b : α⦄,
      G.Adj a b ↔ (a ∈ u ∧ b ∈ w) ∨ (a ∈ w ∧ b ∈ u)) : ¬ G.Adj x y := by
  intro hxy
  rcases hadj.mp hxy with ⟨h1, -⟩ | ⟨-, h2⟩
  · rw [hu] at h1
    simp at h1
  · rw [hu] at h2
    simp at h2

/-- A graph on a subsingleton vertex type has at most one vertex. -/
theorem card_le_one_of_subsingleton {α : Type u} [Fintype α]
    (hall : ∀ x y : α, x = y) : Fintype.card α ≤ 1 := by
  classical
  by_cases hne : Nonempty α
  · obtain ⟨v⟩ := hne
    refine Fintype.card_le_of_injective (fun (x : α) => (⟨x, hall x v⟩ : {y : α // y = v})) ?_
    intro a b hab
    exact congrArg Subtype.val hab
  · letI : IsEmpty α := ⟨fun x => hne ⟨x⟩⟩
    rw [Fintype.card_of_isEmpty]
    exact Nat.zero_le _

/-- **Diameter at most two forces completeness.**  A bipartite graph of diameter at most
two on at least two vertices is complete bipartite with both parts nonempty; the
exception `|V| ≤ 1` is the edgeless one-vertex graph, which is `K₀,₁`. -/
theorem bipartite_diamTwo (hd2 : DiamAtMostTwo G) (s t : Finset α)
    (hadj : ∀ ⦃x y : α⦄,
      G.Adj x y ↔ (x ∈ s ∧ y ∈ t) ∨ (x ∈ t ∧ y ∈ s)) :
    (s.Nonempty ∧ t.Nonempty) ∨ Fintype.card α ≤ 1 := by
  have he : ∀ a b : α, G.Adj a b ↔ (a ∈ s ∧ b ∈ t) ∨ (a ∈ t ∧ b ∈ s) := hadj
  have hadj' : ∀ (a b : α), G.Adj a b ↔ (a ∈ t ∧ b ∈ s) ∨ (a ∈ s ∧ b ∈ t) := by
    intro a b
    constructor
    · intro h
      rcases (he a b).mp h with h1 | h1
      · exact Or.inr h1
      · exact Or.inl h1
    · intro h
      rcases h with h1 | h1
      · exact (he a b).mpr (Or.inr h1)
      · exact (he a b).mpr (Or.inl h1)
  have key : ∀ (u w : Finset α) (hadj' : ∀ (a b : α),
      G.Adj a b ↔ (a ∈ u ∧ b ∈ w) ∨ (a ∈ w ∧ b ∈ u)), ¬ u.Nonempty →
      Fintype.card α ≤ 1 := by
    intro u w hadj' hu
    have hu0 : u = ∅ := by
      ext x
      constructor
      · intro hx
        exact (hu ⟨x, hx⟩).elim
      · intro hx
        simp at hx
    have hnoadj : ∀ ⦃x y : α⦄, ¬ G.Adj x y := by
      intro x y
      exact bipartite_noedge (u := u) (w := w) hu0 (fun ⦃a b⦄ => hadj' a b)
    have hall : ∀ x y : α, x = y := by
      intro x y
      by_cases h : x = y
      · exact h
      · rcases hd2 h with hxy | ⟨z, hxz, -⟩
        · exact (hnoadj hxy).elim
        · exact (hnoadj hxz).elim
    exact card_le_one_of_subsingleton hall
  by_cases hs : s.Nonempty
  · by_cases ht : t.Nonempty
    · exact Or.inl ⟨hs, ht⟩
    · exact Or.inr (key t s hadj' ht)
  · exact Or.inr (key s t he hs)

/-- **Bipartite triangle-free graphs of diameter at most two are complete bipartite.**
Any two vertices lying in different parts are adjacent. -/
theorem bipartite_diamTwo_adj' (hd2 : DiamAtMostTwo G) (s t : Finset α) (hdisj : Disjoint s t)
    (hadj : ∀ ⦃a b : α⦄,
      G.Adj a b ↔ (a ∈ s ∧ b ∈ t) ∨ (a ∈ t ∧ b ∈ s))
    {a b : α} (hab : a ∈ s) (hbt : b ∈ t) : G.Adj a b := by
  have he : ∀ x y : α, G.Adj x y ↔ (x ∈ s ∧ y ∈ t) ∨ (x ∈ t ∧ y ∈ s) := hadj
  have hne : a ≠ b := fun h => Finset.disjoint_left.1 hdisj hab (h ▸ hbt)
  by_contra hcon
  rcases hd2 hne with hxy | ⟨w, haw, hwb⟩
  · exact hcon hxy
  · rcases (he a w).mp haw with haw1 | haw2
    · rcases (he w b).mp hwb with hwb1 | hwb2
      · exact (Finset.disjoint_left.1 hdisj hwb1.1 haw1.2).elim
      · exact (Finset.disjoint_left.1 hdisj hwb2.2 hbt).elim
    · exact (Finset.disjoint_left.1 hdisj hab haw2.1).elim

/-- **JSP-000139, bipartite half.**  A bipartite triangle-free graph of diameter at most
two on `n` vertices is complete bipartite, with parts `s, t` of sizes summing to `n`;
its maximum degree is `max |s| |t| ≥ ⌈n/2⌉`.  Thus the examples with small maximum
degree (`f(n) = o(n)`) are necessarily non-bipartite, and no bipartite example beats
`Δ = ⌈n/2⌉`. -/
theorem jsp_000139_bipartite_diamTwo (s t : Finset α) (hG : TriangleFreeDiamTwo G)
    (hcover : s ∪ t = (Finset.univ : Finset α)) (hdisj : Disjoint s t)
    (hadj : ∀ ⦃x y : α⦄,
      G.Adj x y ↔ (x ∈ s ∧ y ∈ t) ∨ (x ∈ t ∧ y ∈ s)) :
    ((s.Nonempty ∧ t.Nonempty) ∨ Fintype.card α ≤ 1) ∧
      (Fintype.card α + 1) / 2 ≤ max s.card t.card ∧
      (∀ v : α, G.degree v ≤ max s.card t.card) ∧
      (∀ v ∈ s, G.neighborFinset v = t) ∧ (∀ v ∈ t, G.neighborFinset v = s) ∧
      (∀ v ∈ s, G.degree v = t.card) ∧ (∀ v ∈ t, G.degree v = s.card) ∧
      (∀ a b : α, a ∈ s → b ∈ t → G.Adj a b) ∧
      (∀ a b : α, a ∈ s → b ∈ s → ¬ G.Adj a b) := by
  obtain ⟨hmemS, hmemT, hdegS, hdegT⟩ := bipartite_structure s t hcover hdisj hadj
  have hhe : (s.Nonempty ∧ t.Nonempty) ∨ Fintype.card α ≤ 1 := bipartite_diamTwo hG.2 s t hadj
  have key : ∀ a b : ℕ, (a + b + 1) / 2 ≤ max a b := by
    intro a b
    rcases le_total a b with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  have hsum : s.card + t.card = Fintype.card α := by
    rw [← Finset.card_univ, ← hcover, Finset.card_union_of_disjoint hdisj]
  refine ⟨hhe, by rw [← hsum]; exact key _ _, fun u => ?_, hmemS, hmemT, hdegS, hdegT, ?_, ?_⟩
  · rcases Finset.mem_union.mp (by rw [hcover]; exact Finset.mem_univ u) with hu | hu
    · rw [hdegS u hu]; exact le_max_right _ _
    · rw [hdegT u hu]; exact le_max_left _ _
  · intro a b hab hbt
    exact bipartite_diamTwo_adj' hG.2 s t hdisj hadj hab hbt
  · intro a b hab hbs
    intro h
    rcases (hadj.mp h) with ⟨-, h1⟩ | ⟨h2, -⟩
    · exact (Finset.disjoint_left.1 hdisj hbs h1).elim
    · exact (Finset.disjoint_left.1 hdisj hab h2).elim

end Bipartite

end JSP139
