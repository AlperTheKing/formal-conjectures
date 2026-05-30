import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph
namespace WrittenOnTheWallII.Test

private lemma c6_matching_edge_ncard_le_three (M : Subgraph C6) (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ 3 := by
  classical
  have hdeg : ∀ v : Fin 6, M.degree v ≤ 1 := by
    intro v
    by_cases hv : v ∈ M.verts
    · have hvdeg : M.degree v = 1 := by
        rw [Subgraph.degree_eq_one_iff_existsUnique_adj]
        exact hM hv
      omega
    · have hvdeg : M.degree v = 0 := Subgraph.degree_of_notMem_verts hv
      omega
  have hsum_le : (∑ v : Fin 6, M.degree v) ≤ 6 := by
    calc
      (∑ v : Fin 6, M.degree v) ≤ ∑ _v : Fin 6, 1 := by
        exact Finset.sum_le_sum (by intro v _; exact hdeg v)
      _ = 6 := by norm_num
  have hsum :
      ∑ v : Fin 6, M.degree v = 2 * M.edgeSet.ncard := by
    simpa [Subgraph.degree_spanningCoe, SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
      using (M.spanningCoe.sum_degrees_eq_twice_card_edges)
  have htwice : 2 * M.edgeSet.ncard ≤ 6 := by
    rw [← hsum]
    exact hsum_le
  have hcard_lt : M.edgeSet.ncard < 4 := by
    by_contra hlt
    have hge : 4 ≤ M.edgeSet.ncard := Nat.le_of_not_gt hlt
    omega
  exact Nat.le_of_lt_succ hcard_lt

example : m C6 = 3 := by
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
      let F : Finset (Sym2 (Fin 6)) := Finset.filter (fun e => e ∈ M.edgeSet) Finset.univ
      have hcard : F.card = M.edgeSet.ncard := by
        have hcoe : (F : Set (Sym2 (Fin 6))) = M.edgeSet := by
          ext e
          simp [F]
        rw [← Set.ncard_coe_finset, hcoe]
      change F.card ≤ 3
      rw [hcard]
      exact c6_matching_edge_ncard_le_three M hM
  · apply le_csSup
    · refine ⟨3, ?_⟩
      intro x hx
      rcases hx with ⟨M, hM, rfl⟩
      norm_num
      classical
      let F : Finset (Sym2 (Fin 6)) := Finset.filter (fun e => e ∈ M.edgeSet) Finset.univ
      have hcard : F.card = M.edgeSet.ncard := by
        have hcoe : (F : Set (Sym2 (Fin 6))) = M.edgeSet := by
          ext e
          simp [F]
        rw [← Set.ncard_coe_finset, hcoe]
      change F.card ≤ 3
      rw [hcard]
      exact c6_matching_edge_ncard_le_three M hM
    · let h01 : C6.Adj (0 : Fin 6) (1 : Fin 6) := by decide +kernel
      let h23 : C6.Adj (2 : Fin 6) (3 : Fin 6) := by decide +kernel
      let h45 : C6.Adj (4 : Fin 6) (5 : Fin 6) := by decide +kernel
      let M01 := C6.subgraphOfAdj h01
      let M23 := C6.subgraphOfAdj h23
      let M45 := C6.subgraphOfAdj h45
      refine ⟨(M01 ⊔ M23) ⊔ M45, ?_, ?_⟩
      · apply Subgraph.IsMatching.sup
        · apply Subgraph.IsMatching.sup
          · exact Subgraph.IsMatching.subgraphOfAdj h01
          · exact Subgraph.IsMatching.subgraphOfAdj h23
          · dsimp [M01, M23]
            rw [support_subgraphOfAdj h01, support_subgraphOfAdj h23]
            rw [Set.disjoint_left]
            intro x hx hx'
            fin_cases x <;> simp at hx hx'
        · exact Subgraph.IsMatching.subgraphOfAdj h45
        · dsimp [M01, M23, M45]
          rw [Set.disjoint_left]
          intro x hx hx'
          rw [Subgraph.mem_support] at hx
          rcases hx with ⟨y, hy⟩
          rw [Subgraph.sup_adj] at hy
          rcases hy with hy | hy
          · have hx01 : x ∈ (C6.subgraphOfAdj h01).support := by
              exact ⟨y, hy⟩
            rw [support_subgraphOfAdj h01] at hx01
            rw [support_subgraphOfAdj h45] at hx'
            fin_cases x <;> simp at hx01 hx'
          · have hx23 : x ∈ (C6.subgraphOfAdj h23).support := by
              exact ⟨y, hy⟩
            rw [support_subgraphOfAdj h23] at hx23
            rw [support_subgraphOfAdj h45] at hx'
            fin_cases x <;> simp at hx23 hx'
      · dsimp [M01, M23, M45]
        rw [Subgraph.edgeSet_sup, Subgraph.edgeSet_sup,
          edgeSet_subgraphOfAdj, edgeSet_subgraphOfAdj, edgeSet_subgraphOfAdj]
        norm_num
        have hne₁ : s((4 : Fin 6), (5 : Fin 6)) ≠ s((2 : Fin 6), (3 : Fin 6)) := by
          decide +kernel
        have hne₂ : s((4 : Fin 6), (5 : Fin 6)) ≠ s((0 : Fin 6), (1 : Fin 6)) := by
          decide +kernel
        have hne₃ : s((2 : Fin 6), (3 : Fin 6)) ≠ s((0 : Fin 6), (1 : Fin 6)) := by
          decide +kernel
        simp [hne₁, hne₂, hne₃]

end WrittenOnTheWallII.Test
