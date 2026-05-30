import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph
namespace WrittenOnTheWallII.Test

private def petersenOuter (i : Fin 5) : Fin 10 := ⟨i.val, by omega⟩
private def petersenInner (i : Fin 5) : Fin 10 := ⟨i.val + 5, by omega⟩

private lemma petersen_spoke_adj (i : Fin 5) :
    PetersenGraph.Adj (petersenOuter i) (petersenInner i) := by
  fin_cases i <;> decide +kernel

private def petersenSpoke (i : Fin 5) : Subgraph PetersenGraph :=
  PetersenGraph.subgraphOfAdj (petersen_spoke_adj i)

private lemma petersen_matching_edge_ncard_le_five (M : Subgraph PetersenGraph) (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ 5 := by
  classical
  have hdeg : ∀ v : Fin 10, M.degree v ≤ 1 := by
    intro v
    by_cases hv : v ∈ M.verts
    · have hvdeg : M.degree v = 1 := by
        rw [Subgraph.degree_eq_one_iff_existsUnique_adj]
        exact hM hv
      omega
    · have hvdeg : M.degree v = 0 := Subgraph.degree_of_notMem_verts hv
      omega
  have hsum_le : (∑ v : Fin 10, M.degree v) ≤ 10 := by
    calc
      (∑ v : Fin 10, M.degree v) ≤ ∑ _v : Fin 10, 1 := by
        exact Finset.sum_le_sum (by intro v _; exact hdeg v)
      _ = 10 := by norm_num
  have hsum :
      ∑ v : Fin 10, M.degree v = 2 * M.edgeSet.ncard := by
    simpa [Subgraph.degree_spanningCoe, SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
      using (M.spanningCoe.sum_degrees_eq_twice_card_edges)
  have htwice : 2 * M.edgeSet.ncard ≤ 10 := by
    rw [← hsum]
    exact hsum_le
  have hcard_lt : M.edgeSet.ncard < 6 := by
    by_contra hlt
    have hge : 6 ≤ M.edgeSet.ncard := Nat.le_of_not_gt hlt
    omega
  exact Nat.le_of_lt_succ hcard_lt

example : m PetersenGraph = 5 := by
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
      let F : Finset (Sym2 (Fin 10)) := Finset.filter (fun e => e ∈ M.edgeSet) Finset.univ
      have hcard : F.card = M.edgeSet.ncard := by
        have hcoe : (F : Set (Sym2 (Fin 10))) = M.edgeSet := by
          ext e
          simp [F]
        rw [← Set.ncard_coe_finset, hcoe]
      change F.card ≤ 5
      rw [hcard]
      exact petersen_matching_edge_ncard_le_five M hM
  · apply le_csSup
    · refine ⟨5, ?_⟩
      intro x hx
      rcases hx with ⟨M, hM, rfl⟩
      norm_num
      classical
      let F : Finset (Sym2 (Fin 10)) := Finset.filter (fun e => e ∈ M.edgeSet) Finset.univ
      have hcard : F.card = M.edgeSet.ncard := by
        have hcoe : (F : Set (Sym2 (Fin 10))) = M.edgeSet := by
          ext e
          simp [F]
        rw [← Set.ncard_coe_finset, hcoe]
      change F.card ≤ 5
      rw [hcard]
      exact petersen_matching_edge_ncard_le_five M hM
    · let M : Subgraph PetersenGraph := ⨆ i : Fin 5, petersenSpoke i
      have hM : M.IsMatching := by
        dsimp [M]
        apply Subgraph.IsMatching.iSup
        · intro i
          exact Subgraph.IsMatching.subgraphOfAdj (petersen_spoke_adj i)
        · intro i j hij
          dsimp [petersenSpoke]
          rw [support_subgraphOfAdj (petersen_spoke_adj i),
            support_subgraphOfAdj (petersen_spoke_adj j)]
          rw [Set.disjoint_left]
          intro x hx hx'
          fin_cases i <;> fin_cases j <;> fin_cases x <;>
            simp [petersenOuter, petersenInner] at hij hx hx'
      have hverts : M.verts = Set.univ := by
        dsimp [M]
        rw [Subgraph.verts_iSup]
        ext v
        constructor
        · intro hv
          simp
        · intro _hv
          fin_cases v
          · rw [Set.mem_iUnion]
            refine ⟨(0 : Fin 5), ?_⟩
            simp [petersenSpoke, petersenOuter, petersenInner]
          · rw [Set.mem_iUnion]
            refine ⟨(1 : Fin 5), ?_⟩
            simp [petersenSpoke, petersenOuter, petersenInner]
          · rw [Set.mem_iUnion]
            refine ⟨(2 : Fin 5), ?_⟩
            simp [petersenSpoke, petersenOuter, petersenInner]
          · rw [Set.mem_iUnion]
            refine ⟨(3 : Fin 5), ?_⟩
            simp [petersenSpoke, petersenOuter, petersenInner]
          · rw [Set.mem_iUnion]
            refine ⟨(4 : Fin 5), ?_⟩
            simp [petersenSpoke, petersenOuter, petersenInner]
          · rw [Set.mem_iUnion]
            refine ⟨(0 : Fin 5), ?_⟩
            simp [petersenSpoke, petersenOuter, petersenInner]
          · rw [Set.mem_iUnion]
            refine ⟨(1 : Fin 5), ?_⟩
            simp [petersenSpoke, petersenOuter, petersenInner]
          · rw [Set.mem_iUnion]
            refine ⟨(2 : Fin 5), ?_⟩
            simp [petersenSpoke, petersenOuter, petersenInner]
          · rw [Set.mem_iUnion]
            refine ⟨(3 : Fin 5), ?_⟩
            simp [petersenSpoke, petersenOuter, petersenInner]
          · rw [Set.mem_iUnion]
            refine ⟨(4 : Fin 5), ?_⟩
            simp [petersenSpoke, petersenOuter, petersenInner]
      have hedge : M.edgeSet.ncard = 5 := by
        classical
        have hdeg : ∀ v : Fin 10, M.degree v = 1 := by
          intro v
          have hv : v ∈ M.verts := by simp [hverts]
          rw [Subgraph.degree_eq_one_iff_existsUnique_adj]
          exact hM hv
        have hsum_left : (∑ v : Fin 10, M.degree v) = 10 := by
          simp [hdeg]
        have hsum :
            ∑ v : Fin 10, M.degree v = 2 * M.edgeSet.ncard := by
          simpa [Subgraph.degree_spanningCoe, SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
            using (M.spanningCoe.sum_degrees_eq_twice_card_edges)
        omega
      refine ⟨M, hM, ?_⟩
      dsimp
      rw [← Set.ncard_eq_toFinset_card', hedge]
      norm_num

end WrittenOnTheWallII.Test
