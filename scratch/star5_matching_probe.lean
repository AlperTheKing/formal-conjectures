import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph
open Classical

namespace WrittenOnTheWallII.Test

private lemma star5_adj_incident_center {x y : Fin 1 ⊕ Fin 5}
    (h : Star5.Adj x y) : x = Sum.inl (0 : Fin 1) ∨ y = Sum.inl (0 : Fin 1) := by
  cases x with
  | inl a =>
      left
      fin_cases a
      rfl
  | inr a =>
      cases y with
      | inl b =>
          right
          fin_cases b
          rfl
      | inr b =>
          simp [Star5] at h

private lemma star5_matching_edge_card_le_one (M : Subgraph Star5) (hM : M.IsMatching) :
    M.edgeSet.toFinset.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro e he f hf
  induction e using Sym2.ind with
  | h a b =>
      induction f using Sym2.ind with
      | h d e =>
          rw [Set.mem_toFinset, Subgraph.mem_edgeSet] at he hf
          rcases star5_adj_incident_center he.adj_sub with ha | hb
          · subst ha
            rcases star5_adj_incident_center hf.adj_sub with hd | hec
            · subst hd
              obtain ⟨w, _hw, huniq⟩ := hM (M.edge_vert he)
              have hbw : b = w := huniq b he
              have hew : e = w := huniq e hf
              subst hbw
              subst hew
              rfl
            · subst hec
              obtain ⟨w, _hw, huniq⟩ := hM (M.edge_vert he)
              have hbw : b = w := huniq b he
              have hdw : d = w := huniq d hf.symm
              subst hbw
              subst hdw
              exact Sym2.eq_swap
          · subst hb
            rcases star5_adj_incident_center hf.adj_sub with hd | hec
            · subst hd
              obtain ⟨w, _hw, huniq⟩ := hM (M.edge_vert he.symm)
              have haw : a = w := huniq a he.symm
              have hew : e = w := huniq e hf
              subst haw
              subst hew
              exact Sym2.eq_swap
            · subst hec
              obtain ⟨w, _hw, huniq⟩ := hM (M.edge_vert he.symm)
              have haw : a = w := huniq a he.symm
              have hdw : d = w := huniq d hf.symm
              subst haw
              subst hdw
              rfl

example : m Star5 = 1 := by
  unfold m
  let S : Set ℝ :=
    Set.image (fun M : Subgraph Star5 => (M.edgeSet.toFinset.card : ℝ))
      {M : Subgraph Star5 | M.IsMatching}
  change sSup S = 1
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
      simpa [Set.toFinset] using star5_matching_edge_card_le_one M hM
  · apply le_csSup
    · refine ⟨1, ?_⟩
      intro x hx
      rcases hx with ⟨M, hM, rfl⟩
      norm_num
      simpa [Set.toFinset] using star5_matching_edge_card_le_one M hM
    · let h : Star5.Adj (Sum.inl (0 : Fin 1)) (Sum.inr (0 : Fin 5)) := by simp [Star5]
      refine ⟨Star5.subgraphOfAdj h, ?_, ?_⟩
      · exact Subgraph.IsMatching.subgraphOfAdj h
      · change (((Star5.subgraphOfAdj h).edgeSet.toFinset.card : ℝ) = 1)
        rw [SimpleGraph.edgeSet_subgraphOfAdj]
        simp

end WrittenOnTheWallII.Test
