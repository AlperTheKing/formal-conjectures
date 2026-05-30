import FormalConjectures.Util.ProblemImports

example (A : Finset ℤ) (hsub : A ⊆ Finset.Icc (1 : ℤ) 6) (hcard : A.card = 3) : True := by
  finset_cases A
  all_goals trivial
