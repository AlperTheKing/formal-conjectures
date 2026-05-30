import FormalConjectures.ErdosProblems.«385»

namespace Erdos385

example (n : ℕ) : F n ≤ n + √n := by
  have hnat : F n ≤ n + Nat.sqrt n := by
    unfold F
    let S : Set ℕ := {x | ∃ m < n, ∃ (_ : m.Composite), m + m.minFac = x}
    change sSup S ≤ n + Nat.sqrt n
    by_cases hS : S.Nonempty
    · apply csSup_le hS
      rintro x ⟨m, hmn, hmcomp, rfl⟩
      have hmpos : 0 < m := by omega
      have hmin : m.minFac ≤ Nat.sqrt m := by
        rw [Nat.le_sqrt]
        simpa [pow_two] using Nat.minFac_sq_le_self hmpos hmcomp.2
      have hsqrt : Nat.sqrt m ≤ Nat.sqrt n := Nat.sqrt_le_sqrt (Nat.le_of_lt hmn)
      omega
    · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
      simp [hSempty]
  have hsqrt_cast : (Nat.sqrt n : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt]
    · exact_mod_cast Nat.sqrt_le' n
    · positivity
    · positivity
  have hcast : (F n : ℝ) ≤ (n : ℝ) + (Nat.sqrt n : ℝ) := by
    exact_mod_cast hnat
  linarith

end Erdos385
