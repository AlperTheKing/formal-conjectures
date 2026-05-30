import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph
open Classical

namespace WrittenOnTheWallII.Test

example : Star5.egirth = ⊤ := by
  have hconn : Star5.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨Sum.inl (0 : Fin 1), ?_⟩
    intro w
    cases w with
    | inl a =>
        fin_cases a
        exact Reachable.rfl
    | inr b =>
        exact (show Star5.Adj (Sum.inl (0 : Fin 1)) (Sum.inr b) by simp [Star5]).reachable
  have hcard : Nat.card Star5.edgeSet + 1 = Nat.card (Fin 1 ⊕ Fin 5) := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    norm_num [Star5, Fintype.card_sum]
    decide +kernel
  have htree : Star5.IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    exact ⟨hconn, hcard⟩
  exact htree.IsAcyclic.egirth_eq_top

end WrittenOnTheWallII.Test
