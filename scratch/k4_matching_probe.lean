import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph
namespace WrittenOnTheWallII.Test

private lemma k4_matching_edge_ncard_le_two (M : Subgraph K4) (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ 2 := by
  classical
  have hdeg : ∀ v : Fin 4, M.degree v ≤ 1 := by
    intro v
    by_cases hv : v ∈ M.verts
    · have hvdeg : M.degree v = 1 := by
        rw [Subgraph.degree_eq_one_iff_existsUnique_adj]
        exact hM hv
      omega
    · have hvdeg : M.degree v = 0 := Subgraph.degree_of_notMem_verts hv
      omega
  have hsum_le : (∑ v : Fin 4, M.degree v) ≤ 4 := by
    calc
      (∑ v : Fin 4, M.degree v) ≤ ∑ _v : Fin 4, 1 := by
        exact Finset.sum_le_sum (by intro v _; exact hdeg v)
      _ = 4 := by norm_num
  have hsum :
      ∑ v : Fin 4, M.degree v = 2 * M.edgeSet.ncard := by
    simpa [Subgraph.degree_spanningCoe, SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
      using (M.spanningCoe.sum_degrees_eq_twice_card_edges)
  have htwice : 2 * M.edgeSet.ncard ≤ 4 := by
    rw [← hsum]
    exact hsum_le
  have hcard_lt : M.edgeSet.ncard < 3 := by
    by_contra hlt
    have hge : 3 ≤ M.edgeSet.ncard := Nat.le_of_not_gt hlt
    omega
  exact Nat.le_of_lt_succ hcard_lt

example (M : Subgraph K4) (hM : M.IsMatching) :
    M.edgeSet.toFinset.card ≤ 2 := by
  rw [← Set.ncard_eq_toFinset_card']
  exact k4_matching_edge_ncard_le_two M hM

example : m K4 = 2 := by
  unfold m
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, ?_⟩
      refine ⟨⊥, ?_, ?_⟩
      · intro v hv
        simp at hv
      · simp
    · intro x hx
      rcases hx with ⟨M, hM, rfl⟩
      norm_num
      classical
      let F : Finset (Sym2 (Fin 4)) := Finset.filter (fun e => e ∈ M.edgeSet) Finset.univ
      have hcard : F.card = M.edgeSet.ncard := by
        have hcoe : (F : Set (Sym2 (Fin 4))) = M.edgeSet := by
          ext e
          simp [F]
        rw [← Set.ncard_coe_finset, hcoe]
      change F.card ≤ 2
      rw [hcard]
      exact k4_matching_edge_ncard_le_two M hM
  · apply le_csSup
    · refine ⟨2, ?_⟩
      intro x hx
      rcases hx with ⟨M, hM, rfl⟩
      norm_num
      classical
      let F : Finset (Sym2 (Fin 4)) := Finset.filter (fun e => e ∈ M.edgeSet) Finset.univ
      have hcard : F.card = M.edgeSet.ncard := by
        have hcoe : (F : Set (Sym2 (Fin 4))) = M.edgeSet := by
          ext e
          simp [F]
        rw [← Set.ncard_coe_finset, hcoe]
      change F.card ≤ 2
      rw [hcard]
      exact k4_matching_edge_ncard_le_two M hM
    · let h01 : K4.Adj (0 : Fin 4) (1 : Fin 4) := by simp [K4]
      let h23 : K4.Adj (2 : Fin 4) (3 : Fin 4) := by simp [K4]
      refine ⟨K4.subgraphOfAdj h01 ⊔ K4.subgraphOfAdj h23, ?_, ?_⟩
      · apply Subgraph.IsMatching.sup
        · exact Subgraph.IsMatching.subgraphOfAdj h01
        · exact Subgraph.IsMatching.subgraphOfAdj h23
        · rw [support_subgraphOfAdj h01, support_subgraphOfAdj h23]
          rw [Set.disjoint_left]
          intro x hx hx'
          fin_cases x <;> simp at hx hx'
      · dsimp
        rw [Subgraph.edgeSet_sup, edgeSet_subgraphOfAdj, edgeSet_subgraphOfAdj]
        norm_num
        have hne : s((2 : Fin 4), (3 : Fin 4)) ≠ s((0 : Fin 4), (1 : Fin 4)) := by
          decide +kernel
        simp [hne]

end WrittenOnTheWallII.Test
