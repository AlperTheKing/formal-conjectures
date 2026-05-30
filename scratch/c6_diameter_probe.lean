import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph
namespace WrittenOnTheWallII.Test

example (u v : Fin 6) : C6.dist u v = computable_dist C6 u v := by
  rw [dist_eq_computable]

example : C6.dist (0 : Fin 6) (3 : Fin 6) = 3 := by
  rw [dist_eq_computable]
  decide +kernel

private lemma C6_connected : C6.Connected := by
  simpa [C6] using (cycleGraph_connected (n := 5))

private lemma C6_edist_eq_dist (u v : Fin 6) : C6.edist u v = C6.dist u v := by
  exact (C6_connected u v).coe_dist_eq_edist.symm

private lemma C6_dist_le_three (u v : Fin 6) : C6.dist u v ≤ 3 := by
  rw [dist_eq_computable]
  fin_cases u <;> fin_cases v <;> decide +kernel

private lemma C6_has_dist_three (u : Fin 6) : ∃ v : Fin 6, (3 : ℕ∞) ≤ C6.edist u v := by
  fin_cases u
  · refine ⟨3, ?_⟩
    rw [C6_edist_eq_dist]
    norm_num
    rw [dist_eq_computable]
    decide +kernel
  · refine ⟨4, ?_⟩
    rw [C6_edist_eq_dist]
    norm_num
    rw [dist_eq_computable]
    decide +kernel
  · refine ⟨5, ?_⟩
    rw [C6_edist_eq_dist]
    norm_num
    rw [dist_eq_computable]
    decide +kernel
  · refine ⟨0, ?_⟩
    rw [C6_edist_eq_dist]
    norm_num
    rw [dist_eq_computable]
    decide +kernel
  · refine ⟨1, ?_⟩
    rw [C6_edist_eq_dist]
    norm_num
    rw [dist_eq_computable]
    decide +kernel
  · refine ⟨2, ?_⟩
    rw [C6_edist_eq_dist]
    norm_num
    rw [dist_eq_computable]
    decide +kernel

private lemma C6_eccentricity_eq_three (u : Fin 6) :
    C6.eccentricity u = 3 := by
  rw [show C6.eccentricity u = C6.eccent u by
    simp [SimpleGraph.eccentricity, SimpleGraph.eccent, sSup_range]]
  apply le_antisymm
  · rw [SimpleGraph.eccent_le_iff]
    intro v
    rw [C6_edist_eq_dist]
    exact_mod_cast C6_dist_le_three u v
  · rcases C6_has_dist_three u with ⟨v, hv⟩
    exact hv.trans (SimpleGraph.edist_le_eccent (G := C6) (u := u) (v := v))

example : maxEccentricity C6 = 3 := by
  have hrange : Set.range (C6.eccentricity) = ({3} : Set ℕ∞) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      simp [C6_eccentricity_eq_three u]
    · intro hx
      refine ⟨0, ?_⟩
      simpa [C6_eccentricity_eq_three 0] using hx.symm
  rw [maxEccentricity, hrange]
  simp

example : minEccentricity C6 = 3 := by
  have hrange : Set.range (C6.eccentricity) = ({3} : Set ℕ∞) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      simp [C6_eccentricity_eq_three u]
    · intro hx
      refine ⟨0, ?_⟩
      simpa [C6_eccentricity_eq_three 0] using hx.symm
  rw [minEccentricity, hrange]
  simp

end WrittenOnTheWallII.Test
