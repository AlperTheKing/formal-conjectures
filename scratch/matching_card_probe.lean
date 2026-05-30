import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph
open Classical

namespace WrittenOnTheWallII.Test

example (M : Subgraph K4) (hM : M.IsMatching) :
    M.edgeSet.toFinset.card ≤ 2 := by
  have hMdeg := (Subgraph.isMatching_iff_forall_degree.mp hM)
  have hsum_degree : (∑ x : M.verts, M.degree x) = Fintype.card M.verts := by
    rw [show (∑ x : M.verts, M.degree x) = ∑ _x : M.verts, (1 : ℕ) by
      apply Finset.sum_congr rfl
      intro x _hx
      exact hMdeg x x.2]
    simp
  have hsum : M.verts.toFinset.card = 2 * M.coe.edgeFinset.card := by
    have h := M.coe.sum_degrees_eq_twice_card_edges
    rw [← h]
    simpa [Set.toFinset_card, M.coe_degree, hsum_degree]
  have hverts : Fintype.card M.verts ≤ 4 := by
    rw [← Set.toFinset_card]
    exact M.verts.toFinset.card_le_univ
  have hcoe_edges : M.coe.edgeFinset.card ≤ 2 := by
    omega
  -- relate M.coe.edgeFinset.card and M.edgeSet.toFinset.card
  sorry

end WrittenOnTheWallII.Test
