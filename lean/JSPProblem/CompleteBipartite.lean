/-
# JSP-000139 — explicit examples: the complete bipartite graph on `n` vertices

Companion to `JSPProblem.Diameter`.  It exhibits, for every `n ≥ 2`, a triangle-free
graph of diameter at most two on `n` vertices, namely the balanced complete bipartite
graph; together with `jsp_000139_bipartite_diamTwo` this shows that in the bipartite
regime the maximum degree of such a graph is forced to be `≥ ⌈n/2⌉`, so the examples
with small maximum degree (the Hanson–Seyffarth constructions, `Δ = O(√n)`) must be
non-bipartite.
-/
import JSPProblem.Diameter

namespace JSP139

universe u

noncomputable section

variable {n : ℕ}

/-- Membership in the first part of the balanced partition of `Fin n`. -/
def inPartOne (n : ℕ) (i : Fin n) : Prop := i.val < n / 2

/-- The complete bipartite graph on `n` vertices `Fin n`, with parts
`{i | i < n / 2}` and `{i | n / 2 ≤ i}`. -/
def completeBipartiteFin (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := inPartOne n x ≠ inPartOne n y ∧ x ≠ y
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun x h => (h.1 rfl).elim⟩

noncomputable instance (n : ℕ) : DecidableRel (completeBipartiteFin n).Adj :=
  fun _ _ => Classical.propDecidable _

local instance (n : ℕ) (i : Fin n) :
    DecidablePred fun j : Fin n => inPartOne n i ≠ inPartOne n j := fun _ =>
  Classical.propDecidable _

@[simp] theorem mem_neighborFinset_completeBipartiteFin (i j : Fin n) :
    j ∈ (completeBipartiteFin n).neighborFinset i ↔
      inPartOne n i ≠ inPartOne n j ∧ i ≠ j :=
  SimpleGraph.mem_neighborFinset (completeBipartiteFin n) i j

/-- The neighbourhood of a vertex of the balanced complete bipartite graph is the
opposite part, with the vertex itself removed. -/
theorem neighborFinset_completeBipartiteFin (i : Fin n) :
    (completeBipartiteFin n).neighborFinset i
      = Finset.filter (fun j => i ≠ j)
          (Finset.filter (fun j => inPartOne n i ≠ inPartOne n j) (Finset.univ : Finset (Fin n))) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    mem_neighborFinset_completeBipartiteFin]

/-- **The balanced complete bipartite graph is triangle-free.**  Two adjacent vertices
lie in different parts, so no three vertices can be pairwise adjacent. -/
theorem completeBipartiteFin_cliqueFree : (completeBipartiteFin n).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ :=
    (Finset.card_eq_three (s := s)).mp hs.card_eq
  have hAdj (u v : Fin n) (hu : u ∈ s) (hv : v ∈ s) (huv : u ≠ v) :
      (completeBipartiteFin n).Adj u v := hs.isClique hu hv huv
  have h01 := hAdj a b (by simp [hset]) (by simp [hset]) hab
  have h02 := hAdj a c (by simp [hset]) (by simp [hset]) hac
  have h12 := hAdj b c (by simp [hset]) (by simp [hset]) hbc
  by_cases ha : inPartOne n a
  · have hb : ¬ inPartOne n b := fun hb0 => h01.1 (propext ⟨fun _ => hb0, fun _ => ha⟩)
    have hc : ¬ inPartOne n c := fun hc0 => h02.1 (propext ⟨fun _ => hc0, fun _ => ha⟩)
    have hbc : inPartOne n b = inPartOne n c := by
      apply propext
      constructor
      · intro h
        exact False.elim (absurd h hb)
      · intro h
        exact False.elim (absurd h hc)
    exact h12.1 hbc
  · have hb : inPartOne n b := by
      by_cases hb0 : inPartOne n b
      · exact hb0
      · exact False.elim
          (h01.1 (propext ⟨fun h => False.elim (absurd h ha),
            fun h => False.elim (absurd h hb0)⟩))
    have hc : inPartOne n c := by
      by_cases hc0 : inPartOne n c
      · exact hc0
      · exact False.elim
          (h02.1 (propext ⟨fun h => False.elim (absurd h ha),
            fun h => False.elim (absurd h hc0)⟩))
    have hbc : inPartOne n b = inPartOne n c := propext ⟨fun _ => hc, fun _ => hb⟩
    exact h12.1 hbc

/-- **The balanced complete bipartite graph has diameter at most two** (for `n ≥ 2`):
vertices in different parts are adjacent, and two vertices of the same part share a
neighbour from the other part. -/
theorem completeBipartiteFin_diam (hn : 2 ≤ n) : DiamAtMostTwo (completeBipartiteFin n) := by
  classical
  intro u v huv
  by_cases h1 : inPartOne n u
  · by_cases h2 : inPartOne n v
    · -- both vertices in the first part: use a vertex `w` of the second part
      have hw2 : (n / 2 : ℕ) < n := by omega
      have hw : ¬ inPartOne n ⟨n / 2, hw2⟩ := by simp [inPartOne]
      have huv' : u ≠ ⟨n / 2, hw2⟩ := fun h => (congrArg (inPartOne n) h ▸ hw) h1
      have hvw' : ⟨n / 2, hw2⟩ ≠ v := fun h => (congrArg (inPartOne n) h ▸ hw) h2
      refine Or.inr ⟨⟨n / 2, hw2⟩, ⟨fun h => (h ▸ hw) h1, huv'⟩,
        ⟨fun h => (h ▸ hw) h2, hvw'⟩⟩
    · refine Or.inl ⟨fun h => h2 (h ▸ h1), huv⟩
  · by_cases h2 : inPartOne n v
    · refine Or.inl ⟨fun h => h1 (h ▸ h2), huv⟩
    · -- both vertices in the second part: use the vertex `w = 0` of the first part
      have hw0 : (0 : ℕ) < n := by omega
      have hw : inPartOne n ⟨0, hw0⟩ := by simp only [inPartOne, Fin.val_mk]; omega
      have huv' : u ≠ ⟨0, hw0⟩ := fun h => h1 ((congrArg (inPartOne n) h).symm ▸ hw)
      have hvw' : ⟨0, hw0⟩ ≠ v := fun h => h2 ((congrArg (inPartOne n) h).symm ▸ hw)
      refine Or.inr ⟨⟨0, hw0⟩, ⟨fun h => h1 (h.symm ▸ hw), huv'⟩,
        ⟨fun h => h2 (h.symm ▸ hw), hvw'⟩⟩

/-- **JSP-000139: examples exist for every `n`.**  For every `n ≥ 1` there is a
triangle-free graph of diameter at most two on `n` vertices: for `n ≥ 2` the balanced
complete bipartite graph, for `n = 1` the trivial one.  Hence the extremal quantity
`f(n) = min Δ` is well defined for all `n`, and both the Moore bound
`f(n) ≥ √(n − 1)` (`jsp_000139_main`) and the bipartite value `f(n) = ⌈n/2⌉`
(`jsp_000139_bipartite_diamTwo`) apply to it. -/
theorem jsp_000139_exists (hn : 0 < n) : ∃ (G : SimpleGraph (Fin n)), TriangleFreeDiamTwo G := by
  classical
  by_cases h2 : 2 ≤ n
  · exact ⟨completeBipartiteFin n, completeBipartiteFin_cliqueFree,
      completeBipartiteFin_diam h2⟩
  · have h1 : n = 1 := by omega
    subst h1
    refine ⟨completeBipartiteFin 1, completeBipartiteFin_cliqueFree, ?_⟩
    intro u v huv
    exfalso
    apply huv
    apply Fin.ext
    have hu := u.isLt
    have hv := v.isLt
    omega

end

end JSP139
