/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 92

*Reference:* [erdosproblems.com/92](https://www.erdosproblems.com/92)
-/

open Filter
open scoped EuclideanGeometry

namespace Erdos92

/--
For a given point `x` and a set of other points, this function finds the maximum number of points
that lie on a single circle centered at `x`. It does this by grouping the other points by their
distance to `x` and finding the size of the largest group.
-/
noncomputable def maxEquidistantPointsAt (x : ℝ²) (points : Finset ℝ²) : ℕ :=
  letI otherPoints := points.erase x
  letI distances := otherPoints.image (dist x)
  sSup (distances.image fun d ↦ (otherPoints.filter fun p ↦ dist x p = d).card)

/--
This property holds for a set of points `A` if every point `x` in `A` has at least `k` other
points from `A` that are equidistant from `x`.
-/
def hasMinEquidistantProperty (k : ℕ) (A : Finset ℝ²) : Prop :=
  A.Nonempty ∧ ∀ x ∈ A, k ≤ maxEquidistantPointsAt x A

/--
The set of all possible values `k` for which there exists a set of `n` points
satisfying the `hasMinEquidistantProperty k`. The function `f(n)` will be the supremum of this set.
-/
noncomputable def possible_f_values (n : ℕ) : Set ℕ :=
  {k | ∃ (points : Finset ℝ²) (_ : points.card = n), hasMinEquidistantProperty k points}

/--
A sanity check to ensure the set of possible `f(n)` values is bounded above. A trivial bound is
`n-1`, since any point can have at most `n-1` other points equidistant from it.
This ensures `sSup` is well-defined.
-/
@[category test, AMS 52]
theorem possible_f_values_BddAbove (n : ℕ) : BddAbove (possible_f_values n) := by
  use n - 1
  intro k hk
  obtain ⟨points, h_card, hprop⟩ := hk
  obtain ⟨⟨x, hx⟩, hbound⟩ := hprop
  refine (hbound x hx).trans ?_
  simp only [maxEquidistantPointsAt]
  apply csSup_le'
  intro m hm
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_image] at hm
  obtain ⟨d, -, rfl⟩ := hm
  refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
  rw [Finset.card_erase_of_mem hx, h_card]

#print axioms Erdos92.possible_f_values_BddAbove
