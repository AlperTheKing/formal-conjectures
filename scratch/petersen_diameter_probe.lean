import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph
namespace WrittenOnTheWallII.Test

private lemma petersen_edist_le_two (a b : Fin 10) : PetersenGraph.edist a b ≤ 2 := by
  have adj_le {u v : Fin 10} (h : PetersenGraph.Adj u v) :
      PetersenGraph.edist u v ≤ 2 := by
    have hed : PetersenGraph.edist u v = 1 := by
      rwa [SimpleGraph.edist_eq_one_iff_adj]
    rw [hed]
    norm_num
  have via (c : Fin 10) {u v : Fin 10}
      (huc : PetersenGraph.Adj u c) (hcv : PetersenGraph.Adj c v) :
      PetersenGraph.edist u v ≤ 2 := by
    have hed1 : PetersenGraph.edist u c = 1 := by
      rwa [SimpleGraph.edist_eq_one_iff_adj]
    have hed2 : PetersenGraph.edist c v = 1 := by
      rwa [SimpleGraph.edist_eq_one_iff_adj]
    calc
      PetersenGraph.edist u v ≤ PetersenGraph.edist u c + PetersenGraph.edist c v :=
        SimpleGraph.edist_triangle (G := PetersenGraph)
      _ = 2 := by
        rw [hed1, hed2]
        norm_num
  fin_cases a <;> fin_cases b <;>
    first
    | exact adj_le (by decide +kernel)
    | exact via (0 : Fin 10) (by decide +kernel) (by decide +kernel)
    | exact via (1 : Fin 10) (by decide +kernel) (by decide +kernel)
    | exact via (2 : Fin 10) (by decide +kernel) (by decide +kernel)
    | exact via (3 : Fin 10) (by decide +kernel) (by decide +kernel)
    | exact via (4 : Fin 10) (by decide +kernel) (by decide +kernel)
    | exact via (5 : Fin 10) (by decide +kernel) (by decide +kernel)
    | exact via (6 : Fin 10) (by decide +kernel) (by decide +kernel)
    | exact via (7 : Fin 10) (by decide +kernel) (by decide +kernel)
    | exact via (8 : Fin 10) (by decide +kernel) (by decide +kernel)
    | exact via (9 : Fin 10) (by decide +kernel) (by decide +kernel)

private lemma petersen_two_le_dist {a b : Fin 10}
    (hnot : ¬ PetersenGraph.edist a b ≤ 1) :
    (2 : ℕ∞) ≤ PetersenGraph.edist a b := by
  have hlt : (1 : ℕ∞) < PetersenGraph.edist a b := lt_of_not_ge hnot
  simpa using (ENat.add_one_le_iff (m := (1 : ℕ∞))
    (n := PetersenGraph.edist a b) (ENat.coe_ne_top 1)).2 hlt

private lemma petersen_has_dist_two (a : Fin 10) :
    ∃ b : Fin 10, (2 : ℕ∞) ≤ PetersenGraph.edist a b := by
  fin_cases a
  · refine ⟨2, petersen_two_le_dist ?_⟩
    rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
    simp [PetersenGraph]
  · refine ⟨3, petersen_two_le_dist ?_⟩
    rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
    simp [PetersenGraph]
  · refine ⟨4, petersen_two_le_dist ?_⟩
    rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
    simp [PetersenGraph]
  · refine ⟨0, petersen_two_le_dist ?_⟩
    rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
    simp [PetersenGraph]
  · refine ⟨1, petersen_two_le_dist ?_⟩
    rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
    simp [PetersenGraph]
  · refine ⟨6, petersen_two_le_dist ?_⟩
    rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
    simp [PetersenGraph]
  · refine ⟨7, petersen_two_le_dist ?_⟩
    rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
    simp [PetersenGraph]
  · refine ⟨8, petersen_two_le_dist ?_⟩
    rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
    simp [PetersenGraph]
  · refine ⟨9, petersen_two_le_dist ?_⟩
    rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
    simp [PetersenGraph]
  · refine ⟨5, petersen_two_le_dist ?_⟩
    rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
    simp [PetersenGraph]

private lemma petersen_eccentricity_eq_two (a : Fin 10) :
    PetersenGraph.eccentricity a = 2 := by
  rw [show PetersenGraph.eccentricity a = PetersenGraph.eccent a by
    simp [SimpleGraph.eccentricity, SimpleGraph.eccent, sSup_range]]
  apply le_antisymm
  · rw [SimpleGraph.eccent_le_iff]
    intro b
    exact petersen_edist_le_two a b
  · rcases petersen_has_dist_two a with ⟨b, hb⟩
    exact hb.trans (SimpleGraph.edist_le_eccent (G := PetersenGraph) (u := a) (v := b))

example : maxEccentricity PetersenGraph = 2 := by
  have hrange : Set.range (PetersenGraph.eccentricity) = ({2} : Set ℕ∞) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      simp [petersen_eccentricity_eq_two a]
    · intro hx
      refine ⟨0, ?_⟩
      simpa [petersen_eccentricity_eq_two 0] using hx.symm
  rw [maxEccentricity, hrange]
  simp

example : minEccentricity PetersenGraph = 2 := by
  have hrange : Set.range (PetersenGraph.eccentricity) = ({2} : Set ℕ∞) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      simp [petersen_eccentricity_eq_two a]
    · intro hx
      refine ⟨0, ?_⟩
      simpa [petersen_eccentricity_eq_two 0] using hx.symm
  rw [minEccentricity, hrange]
  simp

end WrittenOnTheWallII.Test
