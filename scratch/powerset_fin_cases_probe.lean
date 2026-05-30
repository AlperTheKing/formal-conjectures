import FormalConjectures.Util.ProblemImports

example (B : Finset ℕ)
    (hB : B ∈ (({1, 2, 3} : Finset ℕ).powerset.filter (fun S => S.card ≤ 2))) :
    B.sum id ≠ 5 := by
  fin_cases hB <;> simp
