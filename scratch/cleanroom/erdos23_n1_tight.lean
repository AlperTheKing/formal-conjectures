/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 23

*References:*
* [erdosproblems.com/23](https://www.erdosproblems.com/23)
* [OEIS A389646](https://oeis.org/A389646)
-/

open SimpleGraph BigOperators Classical

namespace Erdos23

/--
Every triangle-free graph on $5$ vertices can be made bipartite by removing at most $1$ edge.
This is the $n = 1$ case of Erdős Problem 23.
-/
@[category test, AMS 5]
theorem erdos_23.variants.n1 :
    ∀ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 5)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
  sorry

/--
There exists a triangle-free graph on $5$ vertices such that at least $1$ edge must be removed
to make it bipartite. This shows the bound in `erdos_23_n1` is tight.
-/
@[category test, AMS 5]


private lemma erdos23_dummy : True := trivial
attribute [-instance] instDecidableRelFinAdjCycleGraph

theorem erdos_23.variants.n1_tight :
    ∃ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 5)),
        H ≤ G → H.IsBipartite → 1 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  have not_bip : ¬ (cycleGraph 5).IsBipartite := by
    rintro ⟨c⟩
    have e01 : (cycleGraph 5).Adj 0 1 := by rw [cycleGraph_adj']; decide
    have e12 : (cycleGraph 5).Adj 1 2 := by rw [cycleGraph_adj']; decide
    have e23 : (cycleGraph 5).Adj 2 3 := by rw [cycleGraph_adj']; decide
    have e34 : (cycleGraph 5).Adj 3 4 := by rw [cycleGraph_adj']; decide
    have e40 : (cycleGraph 5).Adj 4 0 := by rw [cycleGraph_adj']; decide
    have h01 : (c 0).val ≠ (c 1).val := fun h => c.valid e01 (Fin.ext h)
    have h12 : (c 1).val ≠ (c 2).val := fun h => c.valid e12 (Fin.ext h)
    have h23 : (c 2).val ≠ (c 3).val := fun h => c.valid e23 (Fin.ext h)
    have h34 : (c 3).val ≠ (c 4).val := fun h => c.valid e34 (Fin.ext h)
    have h40 : (c 4).val ≠ (c 0).val := fun h => c.valid e40 (Fin.ext h)
    have b0 := (c 0).isLt; have b1 := (c 1).isLt; have b2 := (c 2).isLt
    have b3 := (c 3).isLt; have b4 := (c 4).isLt
    omega
  refine ⟨cycleGraph 5, ?_, ?_⟩
  · intro t ht
    rw [is3Clique_iff] at ht
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
    rw [cycleGraph_adj'] at hab hac hbc
    fin_cases a <;> fin_cases b <;> fin_cases c <;> revert hab hac hbc <;> decide
  · intro H hHle hHbip
    rcases eq_or_ne H (cycleGraph 5) with rfl | hne
    · exact absurd hHbip not_bip
    · by_contra hcc
      push_neg at hcc
      rw [Nat.lt_one_iff, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hcc
      exact hne (le_antisymm hHle (edgeFinset_subset_edgeFinset.mp hcc))

#print axioms Erdos23.erdos_23.variants.n1_tight
