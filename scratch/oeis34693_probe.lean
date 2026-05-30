import FormalConjectures.OEIS.«34693»

namespace OeisA34693

theorem probe_root : (Real.nthRoot 100 (19 : ℝ)) ^ 74 < 9 := by
  apply lt_of_pow_lt_pow_left₀ 100 (by norm_num : (0 : ℝ) ≤ 9)
  calc
    ((Real.nthRoot 100 (19 : ℝ)) ^ 74) ^ 100
        = ((Real.nthRoot 100 (19 : ℝ)) ^ 100) ^ 74 := by ring
    _ = (19 : ℝ) ^ 74 := by
      rw [Real.pow_nthRoot]
      exact Or.inl ⟨by norm_num, by norm_num⟩
    _ < 9 ^ 100 := by norm_num

theorem probe_k (k : ℕ)
    (hk : k < 1 + (Real.nthRoot 100 (19 : ℕ)) ^ 74) : k < 10 := by
  have hbound : (1 : ℝ) + (Real.nthRoot 100 (19 : ℝ)) ^ 74 < 10 := by
    linarith [probe_root]
  have hk_real : (k : ℝ) < 10 := lt_trans hk hbound
  exact_mod_cast hk_real

theorem probe_not_prime (k : ℕ) (hk : k < 10) : ¬(19 * k + 1).Prime := by
  interval_cases k <;> norm_num

theorem probe_main : ∃ n > (0 : ℕ), ∀ (k : ℕ),
    k < 1 + (Real.nthRoot 100 n) ^ 74 → ¬(n * k + 1).Prime := by
  refine ⟨19, by norm_num, ?_⟩
  intro k hk
  exact probe_not_prime k (probe_k k hk)

#print axioms probe_root
#print axioms probe_k
#print axioms probe_not_prime
#print axioms probe_main

end OeisA34693
