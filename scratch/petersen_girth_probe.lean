import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph
namespace WrittenOnTheWallII.Test

private lemma petersen_adj_no_common {a b c : Fin 10}
    (hab : PetersenGraph.Adj a b) (hac : PetersenGraph.Adj a c)
    (hbc : PetersenGraph.Adj b c) : False := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [PetersenGraph] at hab hac hbc

private lemma petersen_common_neighbor_unique {a b c d : Fin 10}
    (hab : a ≠ b) (hac : PetersenGraph.Adj a c) (hbc : PetersenGraph.Adj b c)
    (had : PetersenGraph.Adj a d) (hbd : PetersenGraph.Adj b d) : c = d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [PetersenGraph] at hab hac hbc had hbd ⊢

private lemma petersen_not_cycle_length_three {a : Fin 10}
    (w : PetersenGraph.Walk a a) (hw : w.IsCycle) : w.length ≠ 3 := by
  intro hlen
  have h01 : PetersenGraph.Adj a (w.getVert 1) := by
    simpa using w.adj_getVert_succ (i := 0) (by omega)
  have h12 : PetersenGraph.Adj (w.getVert 1) (w.getVert 2) := by
    exact w.adj_getVert_succ (by omega)
  have h20 : PetersenGraph.Adj (w.getVert 2) a := by
    have h20' : PetersenGraph.Adj (w.getVert 2) (w.getVert 3) :=
      w.adj_getVert_succ (i := 2) (by omega)
    have h3a : w.getVert 3 = a := by
      simpa [hlen] using w.getVert_length
    simpa [h3a] using h20'
  exact petersen_adj_no_common h01 h20.symm h12

private lemma petersen_not_cycle_length_four {a : Fin 10}
    (w : PetersenGraph.Walk a a) (hw : w.IsCycle) : w.length ≠ 4 := by
  intro hlen
  have h01 : PetersenGraph.Adj a (w.getVert 1) := by
    simpa using w.adj_getVert_succ (i := 0) (by omega)
  have h12 : PetersenGraph.Adj (w.getVert 1) (w.getVert 2) := by
    exact w.adj_getVert_succ (by omega)
  have h23 : PetersenGraph.Adj (w.getVert 2) (w.getVert 3) := by
    exact w.adj_getVert_succ (by omega)
  have h30 : PetersenGraph.Adj (w.getVert 3) a := by
    have h30' : PetersenGraph.Adj (w.getVert 3) (w.getVert 4) :=
      w.adj_getVert_succ (i := 3) (by omega)
    have h4a : w.getVert 4 = a := by
      simpa [hlen] using w.getVert_length
    simpa [h4a] using h30'
  have h01ne : a ≠ w.getVert 1 := h01.ne
  have h12ne : w.getVert 1 ≠ w.getVert 2 := h12.ne
  have h23ne : w.getVert 2 ≠ w.getVert 3 := h23.ne
  have h30ne : w.getVert 3 ≠ a := h30.ne
  have h02ne : a ≠ w.getVert 2 := by
    intro h02
    have hendpoint := (hw.getVert_endpoint_iff (i := 2) (by omega)).1 h02.symm
    omega
  have h13ne : w.getVert 1 ≠ w.getVert 3 := by
    intro h13
    have hidx := hw.getVert_injOn
      (by simp [hlen]) (by simp [hlen]) h13
    omega
  have hcommon : w.getVert 1 = w.getVert 3 :=
    petersen_common_neighbor_unique h02ne h01 h12.symm h30.symm h23
  exact h13ne hcommon

private lemma petersen_five_le_cycle_length {a : Fin 10}
    (w : PetersenGraph.Walk a a) (hw : w.IsCycle) : 5 ≤ w.length := by
  have h3 : 3 ≤ w.length := hw.three_le_length
  by_contra hlt
  have hlt5 : w.length < 5 := by omega
  interval_cases hlen : w.length
  · exact petersen_not_cycle_length_three w hw hlen
  · exact petersen_not_cycle_length_four w hw hlen

example : PetersenGraph.girth = 5 := by
  let h01 : PetersenGraph.Adj (0 : Fin 10) (1 : Fin 10) := by decide +kernel
  let h12 : PetersenGraph.Adj (1 : Fin 10) (2 : Fin 10) := by decide +kernel
  let h23 : PetersenGraph.Adj (2 : Fin 10) (3 : Fin 10) := by decide +kernel
  let h34 : PetersenGraph.Adj (3 : Fin 10) (4 : Fin 10) := by decide +kernel
  let h40 : PetersenGraph.Adj (4 : Fin 10) (0 : Fin 10) := by decide +kernel
  let w : PetersenGraph.Walk (0 : Fin 10) (0 : Fin 10) :=
    Walk.cons h01 (Walk.cons h12 (Walk.cons h23 (Walk.cons h34 (Walk.cons h40 Walk.nil))))
  have hw : w.IsCycle := by
    simp [w, Walk.isCycle_def]
  apply le_antisymm
  · simpa [w] using PetersenGraph.girth_le_length hw
  · have hleegirth : (5 : ℕ∞) ≤ PetersenGraph.egirth := by
      rw [SimpleGraph.le_egirth]
      intro a w hw
      exact_mod_cast petersen_five_le_cycle_length w hw
    have hne : PetersenGraph.egirth ≠ ⊤ := by
      have hle : PetersenGraph.egirth ≤ (5 : ℕ∞) := by
        simpa [w] using PetersenGraph.egirth_le_length hw
      intro htop
      rw [htop] at hle
      norm_num at hle
    unfold SimpleGraph.girth
    exact ENat.toNat_le_toNat hleegirth hne

end WrittenOnTheWallII.Test
