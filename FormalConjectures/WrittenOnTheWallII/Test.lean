/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Testing Graph Invariants

This file contains tests for graph invariants on 5 specific concrete graphs:
1. `HouseGraph`: A graph on 5 vertices.
2. `K4`: The complete graph on 4 vertices.
3. `PetersenGraph`: The Petersen graph on 10 vertices.
4. `C6`: The cycle graph on 6 vertices.
5. `Star5`: The star graph with 5 leaves (6 vertices total).

Tests cover:
independence_number, dominationNumber, average_distance, diameter, radius,
girth, order, size, szeged_index, wiener_index, min_degree, max_degree,
average_degree, matching_number, residue, annihilation_number, cvetkovic.
-/

open SimpleGraph

namespace WrittenOnTheWallII.Test

open Classical

-- Bridge theorems for Sym2/edist-based invariants:
-- All 6 (indep_num, dom_num, dist, wiener, avg_dist, szeged) are proved in
-- FormalConjecturesForMathlib/.../Invariants.lean and exported via that module.

/-  ### Graph Definitions -/

/-- House Graph: Square 0-1-2-3-0 with roof 4 connected to 2,3. -/
abbrev HouseGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet {
    s(0, 1), s(1, 2), s(2, 3), s(3, 0),
    s(2, 4), s(3, 4)
  }

/-- K4: Complete graph on 4 vertices. -/
abbrev K4 : SimpleGraph (Fin 4) := completeGraph (Fin 4)

/-- Petersen Graph on 10 vertices. -/
abbrev PetersenGraph : SimpleGraph (Fin 10) :=
  SimpleGraph.fromEdgeSet {
    -- Outer Cycle
    s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0),
    -- Spokes
    s(0, 5), s(1, 6), s(2, 7), s(3, 8), s(4, 9),
    -- Inner Star
    s(5, 7), s(7, 9), s(9, 6), s(6, 8), s(8, 5)
  }

/-- C6: Cycle graph on 6 vertices. -/
abbrev C6 : SimpleGraph (Fin 6) := cycleGraph 6

/-- Star5: Star graph with center 0 and 5 leaves. -/
abbrev Star5 : SimpleGraph (Fin 1 ⊕ Fin 5) := completeBipartiteGraph (Fin 1) (Fin 5)

instance : DecidableRel Star5.Adj := by unfold Star5 completeBipartiteGraph; infer_instance


/-  ### House Graph Tests -/

@[category test, AMS 5]
theorem house_indep : α(HouseGraph) = 2 := by
  rw [indep_num_eq_computable]; decide +native

@[category test, AMS 5]
theorem house_dom : dominationNumber HouseGraph = 2 := by
  rw [dom_num_eq_computable]; decide +native

@[category test, AMS 5]
theorem house_avg_dist : averageDistance HouseGraph = 7/5 := by
  rw [avg_dist_eq_computable, show computable_avg_dist HouseGraph = (7 / 5 : ℚ) from by decide +native]
  norm_num

@[category test, AMS 5]
theorem house_diameter : maxEccentricity HouseGraph = 2 := by
  have adj_le {a b : Fin 5} (h : HouseGraph.Adj a b) : HouseGraph.edist a b ≤ 2 := by
    have hed : HouseGraph.edist a b = 1 := by
      rwa [SimpleGraph.edist_eq_one_iff_adj]
    rw [hed]
    norm_num
  have via (c : Fin 5) {a b : Fin 5} (hac : HouseGraph.Adj a c) (hcb : HouseGraph.Adj c b) :
      HouseGraph.edist a b ≤ 2 := by
    have hed1 : HouseGraph.edist a c = 1 := by
      rwa [SimpleGraph.edist_eq_one_iff_adj]
    have hed2 : HouseGraph.edist c b = 1 := by
      rwa [SimpleGraph.edist_eq_one_iff_adj]
    calc
      HouseGraph.edist a b ≤ HouseGraph.edist a c + HouseGraph.edist c b :=
        SimpleGraph.edist_triangle (G := HouseGraph)
      _ = 2 := by
        rw [hed1, hed2]
        norm_num
  have hdist_le : ∀ a b : Fin 5, HouseGraph.edist a b ≤ 2 := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      first
      | exact adj_le (by decide +kernel)
      | exact via (0 : Fin 5) (by decide +kernel) (by decide +kernel)
      | exact via (1 : Fin 5) (by decide +kernel) (by decide +kernel)
      | exact via (2 : Fin 5) (by decide +kernel) (by decide +kernel)
      | exact via (3 : Fin 5) (by decide +kernel) (by decide +kernel)
  have two_le_dist {a b : Fin 5} (hnot : ¬ HouseGraph.edist a b ≤ 1) :
      (2 : ℕ∞) ≤ HouseGraph.edist a b := by
    have hlt : (1 : ℕ∞) < HouseGraph.edist a b := lt_of_not_ge hnot
    simpa using (ENat.add_one_le_iff (m := (1 : ℕ∞))
      (n := HouseGraph.edist a b) (ENat.coe_ne_top 1)).2 hlt
  have hdist_ge : ∀ a : Fin 5, ∃ b : Fin 5, (2 : ℕ∞) ≤ HouseGraph.edist a b := by
    intro a
    fin_cases a
    · refine ⟨2, two_le_dist ?_⟩
      rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
      simp [HouseGraph]
    · refine ⟨3, two_le_dist ?_⟩
      rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
      simp [HouseGraph]
    · refine ⟨0, two_le_dist ?_⟩
      rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
      simp [HouseGraph]
    · refine ⟨1, two_le_dist ?_⟩
      rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
      simp [HouseGraph]
    · refine ⟨0, two_le_dist ?_⟩
      rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
      simp [HouseGraph]
  have hecc : ∀ a : Fin 5, HouseGraph.eccentricity a = 2 := by
    intro a
    rw [show HouseGraph.eccentricity a = HouseGraph.eccent a by
      simp [SimpleGraph.eccentricity, SimpleGraph.eccent, sSup_range]]
    apply le_antisymm
    · rw [SimpleGraph.eccent_le_iff]
      intro b
      exact hdist_le a b
    · rcases hdist_ge a with ⟨b, hb⟩
      exact hb.trans (SimpleGraph.edist_le_eccent (G := HouseGraph) (u := a) (v := b))
  have hrange : Set.range (HouseGraph.eccentricity) = ({2} : Set ℕ∞) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      simp [hecc a]
    · intro hx
      refine ⟨0, ?_⟩
      simpa [hecc 0] using hx.symm
  rw [maxEccentricity, hrange]
  simp

@[category test, AMS 5]
theorem house_radius : minEccentricity HouseGraph = 2 := by
  have adj_le {a b : Fin 5} (h : HouseGraph.Adj a b) : HouseGraph.edist a b ≤ 2 := by
    have hed : HouseGraph.edist a b = 1 := by
      rwa [SimpleGraph.edist_eq_one_iff_adj]
    rw [hed]
    norm_num
  have via (c : Fin 5) {a b : Fin 5} (hac : HouseGraph.Adj a c) (hcb : HouseGraph.Adj c b) :
      HouseGraph.edist a b ≤ 2 := by
    have hed1 : HouseGraph.edist a c = 1 := by
      rwa [SimpleGraph.edist_eq_one_iff_adj]
    have hed2 : HouseGraph.edist c b = 1 := by
      rwa [SimpleGraph.edist_eq_one_iff_adj]
    calc
      HouseGraph.edist a b ≤ HouseGraph.edist a c + HouseGraph.edist c b :=
        SimpleGraph.edist_triangle (G := HouseGraph)
      _ = 2 := by
        rw [hed1, hed2]
        norm_num
  have hdist_le : ∀ a b : Fin 5, HouseGraph.edist a b ≤ 2 := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      first
      | exact adj_le (by decide +kernel)
      | exact via (0 : Fin 5) (by decide +kernel) (by decide +kernel)
      | exact via (1 : Fin 5) (by decide +kernel) (by decide +kernel)
      | exact via (2 : Fin 5) (by decide +kernel) (by decide +kernel)
      | exact via (3 : Fin 5) (by decide +kernel) (by decide +kernel)
  have two_le_dist {a b : Fin 5} (hnot : ¬ HouseGraph.edist a b ≤ 1) :
      (2 : ℕ∞) ≤ HouseGraph.edist a b := by
    have hlt : (1 : ℕ∞) < HouseGraph.edist a b := lt_of_not_ge hnot
    simpa using (ENat.add_one_le_iff (m := (1 : ℕ∞))
      (n := HouseGraph.edist a b) (ENat.coe_ne_top 1)).2 hlt
  have hdist_ge : ∀ a : Fin 5, ∃ b : Fin 5, (2 : ℕ∞) ≤ HouseGraph.edist a b := by
    intro a
    fin_cases a
    · refine ⟨2, two_le_dist ?_⟩
      rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
      simp [HouseGraph]
    · refine ⟨3, two_le_dist ?_⟩
      rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
      simp [HouseGraph]
    · refine ⟨0, two_le_dist ?_⟩
      rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
      simp [HouseGraph]
    · refine ⟨1, two_le_dist ?_⟩
      rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
      simp [HouseGraph]
    · refine ⟨0, two_le_dist ?_⟩
      rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
      simp [HouseGraph]
  have hecc : ∀ a : Fin 5, HouseGraph.eccentricity a = 2 := by
    intro a
    rw [show HouseGraph.eccentricity a = HouseGraph.eccent a by
      simp [SimpleGraph.eccentricity, SimpleGraph.eccent, sSup_range]]
    apply le_antisymm
    · rw [SimpleGraph.eccent_le_iff]
      intro b
      exact hdist_le a b
    · rcases hdist_ge a with ⟨b, hb⟩
      exact hb.trans (SimpleGraph.edist_le_eccent (G := HouseGraph) (u := a) (v := b))
  have hrange : Set.range (HouseGraph.eccentricity) = ({2} : Set ℕ∞) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      simp [hecc a]
    · intro hx
      refine ⟨0, ?_⟩
      simpa [hecc 0] using hx.symm
  rw [minEccentricity, hrange]
  simp

@[category test, AMS 5]
theorem house_girth : HouseGraph.girth = 3 := by
  have hclique : ∃ s : Finset (Fin 5), HouseGraph.IsNClique 3 s := by
    refine ⟨{2, 3, 4}, ?_⟩
    rw [SimpleGraph.is3Clique_triple_iff]
    simp [HouseGraph]
  obtain ⟨u, w, hwcycle, hwlen⟩ :=
    (SimpleGraph.is3Clique_iff_exists_cycle_length_three (G := HouseGraph)).mp hclique
  apply le_antisymm
  · simpa [hwlen] using HouseGraph.girth_le_length hwcycle
  · apply SimpleGraph.three_le_girth
    intro hacyclic
    exact hacyclic w hwcycle

@[category test, AMS 5]
theorem house_order : n HouseGraph = 5 := by simp [n]

@[category test, AMS 5]
theorem house_size : HouseGraph.edgeFinset.card = 6 := by
  decide +native

@[category test, AMS 5]
theorem house_szeged : szegedIndex HouseGraph = 24 := by
  rw [szeged_eq_computable]; decide +native

@[category test, AMS 5]
theorem house_wiener : wienerIndex HouseGraph = 14 := by
  rw [wiener_eq_computable]; decide +native

@[category test, AMS 5]
theorem house_min_deg : HouseGraph.minDegree = 2 := by
  decide +native

@[category test, AMS 5]
theorem house_max_deg : HouseGraph.maxDegree = 3 := by
  decide +native

@[category test, AMS 5]
theorem house_avg_deg : averageDegree HouseGraph = 12/5 := by
  unfold averageDegree; simp [Fintype.card_fin]; decide +native

@[category test, AMS 5]
private lemma house_matching_edge_ncard_le_two (M : Subgraph HouseGraph) (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ 2 := by
  classical
  have hdeg : ∀ v : Fin 5, M.degree v ≤ 1 := by
    intro v
    by_cases hv : v ∈ M.verts
    · have hvdeg : M.degree v = 1 := by
        rw [Subgraph.degree_eq_one_iff_existsUnique_adj]
        exact hM hv
      omega
    · have hvdeg : M.degree v = 0 := Subgraph.degree_of_notMem_verts hv
      omega
  have hsum_le : (∑ v : Fin 5, M.degree v) ≤ 5 := by
    calc
      (∑ v : Fin 5, M.degree v) ≤ ∑ _v : Fin 5, 1 := by
        exact Finset.sum_le_sum (by intro v _; exact hdeg v)
      _ = 5 := by norm_num
  have hsum :
      ∑ v : Fin 5, M.degree v = 2 * M.edgeSet.ncard := by
    simpa [Subgraph.degree_spanningCoe, SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
      using (M.spanningCoe.sum_degrees_eq_twice_card_edges)
  have htwice : 2 * M.edgeSet.ncard ≤ 5 := by
    rw [← hsum]
    exact hsum_le
  have hcard_lt : M.edgeSet.ncard < 3 := by
    by_contra hlt
    have hge : 3 ≤ M.edgeSet.ncard := Nat.le_of_not_gt hlt
    omega
  exact Nat.le_of_lt_succ hcard_lt

@[category test, AMS 5]
theorem house_matching : m HouseGraph = 2 := by
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
      let F : Finset (Sym2 (Fin 5)) := Finset.filter (fun e => e ∈ M.edgeSet) Finset.univ
      have hcard : F.card = M.edgeSet.ncard := by
        have hcoe : (F : Set (Sym2 (Fin 5))) = M.edgeSet := by
          ext e
          simp [F]
        rw [← Set.ncard_coe_finset, hcoe]
      change F.card ≤ 2
      rw [hcard]
      exact house_matching_edge_ncard_le_two M hM
  · apply le_csSup
    · refine ⟨2, ?_⟩
      intro x hx
      rcases hx with ⟨M, hM, rfl⟩
      norm_num
      classical
      let F : Finset (Sym2 (Fin 5)) := Finset.filter (fun e => e ∈ M.edgeSet) Finset.univ
      have hcard : F.card = M.edgeSet.ncard := by
        have hcoe : (F : Set (Sym2 (Fin 5))) = M.edgeSet := by
          ext e
          simp [F]
        rw [← Set.ncard_coe_finset, hcoe]
      change F.card ≤ 2
      rw [hcard]
      exact house_matching_edge_ncard_le_two M hM
    · let h01 : HouseGraph.Adj (0 : Fin 5) (1 : Fin 5) := by simp [HouseGraph]
      let h24 : HouseGraph.Adj (2 : Fin 5) (4 : Fin 5) := by simp [HouseGraph]
      refine ⟨HouseGraph.subgraphOfAdj h01 ⊔ HouseGraph.subgraphOfAdj h24, ?_, ?_⟩
      · apply Subgraph.IsMatching.sup
        · exact Subgraph.IsMatching.subgraphOfAdj h01
        · exact Subgraph.IsMatching.subgraphOfAdj h24
        · rw [support_subgraphOfAdj h01, support_subgraphOfAdj h24]
          rw [Set.disjoint_left]
          intro x hx hx'
          fin_cases x <;> simp at hx hx'
      · dsimp
        rw [Subgraph.edgeSet_sup, edgeSet_subgraphOfAdj, edgeSet_subgraphOfAdj]
        norm_num
        have hne : s((2 : Fin 5), (4 : Fin 5)) ≠ s((0 : Fin 5), (1 : Fin 5)) := by
          decide +kernel
        simp [hne]

@[category test, AMS 5]
theorem house_residue : residue HouseGraph = 0 := by
  unfold residue; decide +native

@[category test, AMS 5]
theorem house_annihilation : annihilationNumber HouseGraph = 3 := by
  decide +native

@[category test, AMS 5]
theorem house_cvetkovic : cvetkovic HouseGraph = 3 := by
  sorry


/-  ### K4 Tests -/

@[category test, AMS 5]
theorem K4_indep : α(K4) = 1 := by
  rw [indep_num_eq_computable]; decide +native

@[category test, AMS 5]
theorem K4_dom : dominationNumber K4 = 1 := by
  rw [dom_num_eq_computable]; decide +native

@[category test, AMS 5]
theorem K4_avg_dist : averageDistance K4 = 1 := by
  rw [avg_dist_eq_computable, show computable_avg_dist K4 = (1 : ℚ) from by decide +native]
  norm_num

@[category test, AMS 5]
theorem K4_diameter : maxEccentricity K4 = 1 := by
  have hecc : ∀ u : Fin 4, (⊤ : SimpleGraph (Fin 4)).eccentricity u = 1 := by
    intro u
    rw [show (⊤ : SimpleGraph (Fin 4)).eccentricity u =
        (⊤ : SimpleGraph (Fin 4)).eccent u by
      simp [SimpleGraph.eccentricity, SimpleGraph.eccent, sSup_range]]
    simp
  have hrange : Set.range ((⊤ : SimpleGraph (Fin 4)).eccentricity) = ({1} : Set ℕ∞) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      simp [hecc u]
    · intro hx
      refine ⟨0, ?_⟩
      simpa [hecc 0] using hx.symm
  rw [K4, maxEccentricity, hrange]
  simp

@[category test, AMS 5]
theorem K4_radius : minEccentricity K4 = 1 := by
  have hecc : ∀ u : Fin 4, (⊤ : SimpleGraph (Fin 4)).eccentricity u = 1 := by
    intro u
    rw [show (⊤ : SimpleGraph (Fin 4)).eccentricity u =
        (⊤ : SimpleGraph (Fin 4)).eccent u by
      simp [SimpleGraph.eccentricity, SimpleGraph.eccent, sSup_range]]
    simp
  have hrange : Set.range ((⊤ : SimpleGraph (Fin 4)).eccentricity) = ({1} : Set ℕ∞) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      simp [hecc u]
    · intro hx
      refine ⟨0, ?_⟩
      simpa [hecc 0] using hx.symm
  rw [K4, minEccentricity, hrange]
  simp

@[category test, AMS 5]
theorem K4_girth : K4.girth = 3 := by
  have hclique : ∃ s : Finset (Fin 4), K4.IsNClique 3 s := by
    refine ⟨{0, 1, 2}, ?_⟩
    rw [SimpleGraph.is3Clique_triple_iff]
    simp [K4]
  obtain ⟨u, w, hwcycle, hwlen⟩ :=
    (SimpleGraph.is3Clique_iff_exists_cycle_length_three (G := K4)).mp hclique
  apply le_antisymm
  · simpa [hwlen] using K4.girth_le_length hwcycle
  · apply SimpleGraph.three_le_girth
    intro hacyclic
    exact hacyclic w hwcycle

@[category test, AMS 5]
theorem K4_order : n K4 = 4 := by simp [n]

@[category test, AMS 5]
theorem K4_size : K4.edgeFinset.card = 6 := by
  decide +native

@[category test, AMS 5]
theorem K4_szeged : szegedIndex K4 = 6 := by
  rw [szeged_eq_computable]; decide +native

@[category test, AMS 5]
theorem K4_wiener : wienerIndex K4 = 6 := by
  rw [wiener_eq_computable]; decide +native

@[category test, AMS 5]
theorem K4_min_deg : K4.minDegree = 3 := by
  decide +native

@[category test, AMS 5]
theorem K4_max_deg : K4.maxDegree = 3 := by
  decide +native

@[category test, AMS 5]
theorem K4_avg_deg : averageDegree K4 = 3 := by
  unfold averageDegree; simp [Fintype.card_fin]

@[category test, AMS 5]
private lemma K4_matching_edge_ncard_le_two (M : Subgraph K4) (hM : M.IsMatching) :
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

@[category test, AMS 5]
theorem K4_matching : m K4 = 2 := by
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
      exact K4_matching_edge_ncard_le_two M hM
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
      exact K4_matching_edge_ncard_le_two M hM
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

@[category test, AMS 5]
theorem K4_residue : residue K4 = 0 := by
  unfold residue; decide +native

@[category test, AMS 5]
theorem K4_annihilation : annihilationNumber K4 = 2 := by
  decide +native

@[category test, AMS 5]
theorem K4_cvetkovic : cvetkovic K4 = 1 := by
  sorry


/-  ### Petersen Graph Tests -/

@[category test, AMS 5]
theorem petersen_indep : α(PetersenGraph) = 4 := by
  rw [indep_num_eq_computable]; decide +native

@[category test, AMS 5]
theorem petersen_dom : dominationNumber PetersenGraph = 3 := by
  rw [dom_num_eq_computable]; decide +native

@[category test, AMS 5]
theorem petersen_avg_dist : averageDistance PetersenGraph = 5/3 := by
  rw [avg_dist_eq_computable, show computable_avg_dist PetersenGraph = (5 / 3 : ℚ) from by decide +native]
  norm_num

@[category test, AMS 5]
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

@[category test, AMS 5]
private lemma petersen_two_le_dist {a b : Fin 10}
    (hnot : ¬ PetersenGraph.edist a b ≤ 1) :
    (2 : ℕ∞) ≤ PetersenGraph.edist a b := by
  have hlt : (1 : ℕ∞) < PetersenGraph.edist a b := lt_of_not_ge hnot
  simpa using (ENat.add_one_le_iff (m := (1 : ℕ∞))
    (n := PetersenGraph.edist a b) (ENat.coe_ne_top 1)).2 hlt

@[category test, AMS 5]
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

@[category test, AMS 5]
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

@[category test, AMS 5]
theorem petersen_diameter : maxEccentricity PetersenGraph = 2 := by
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

@[category test, AMS 5]
theorem petersen_radius : minEccentricity PetersenGraph = 2 := by
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

@[category test, AMS 5]
theorem petersen_girth : PetersenGraph.girth = 5 := by
  sorry

@[category test, AMS 5]
theorem petersen_order : n PetersenGraph = 10 := by simp [n]

@[category test, AMS 5]
theorem petersen_size : PetersenGraph.edgeFinset.card = 15 := by
  decide +native

@[category test, AMS 5]
theorem petersen_szeged : szegedIndex PetersenGraph = 135 := by
  rw [szeged_eq_computable]; decide +native

@[category test, AMS 5]
theorem petersen_wiener : wienerIndex PetersenGraph = 75 := by
  rw [wiener_eq_computable]; decide +native

@[category test, AMS 5]
theorem petersen_min_deg : PetersenGraph.minDegree = 3 := by
  decide +native

@[category test, AMS 5]
theorem petersen_max_deg : PetersenGraph.maxDegree = 3 := by
  decide +native

@[category test, AMS 5]
theorem petersen_avg_deg : averageDegree PetersenGraph = 3 := by
  unfold averageDegree; simp [Fintype.card_fin]; decide +native

@[category test, AMS 5]
private def petersenOuter (i : Fin 5) : Fin 10 := ⟨i.val, by omega⟩

@[category test, AMS 5]
private def petersenInner (i : Fin 5) : Fin 10 := ⟨i.val + 5, by omega⟩

@[category test, AMS 5]
private lemma petersen_spoke_adj (i : Fin 5) :
    PetersenGraph.Adj (petersenOuter i) (petersenInner i) := by
  fin_cases i <;> decide +kernel

@[category test, AMS 5]
private def petersenSpoke (i : Fin 5) : Subgraph PetersenGraph :=
  PetersenGraph.subgraphOfAdj (petersen_spoke_adj i)

@[category test, AMS 5]
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

@[category test, AMS 5]
theorem petersen_matching : m PetersenGraph = 5 := by
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

@[category test, AMS 5]
theorem petersen_residue : residue PetersenGraph = 0 := by
  unfold residue; decide +native

@[category test, AMS 5]
theorem petersen_annihilation : annihilationNumber PetersenGraph = 5 := by
  decide +native

@[category test, AMS 5]
theorem petersen_cvetkovic : cvetkovic PetersenGraph = 4 := by
  sorry


/-  ### C6 Tests -/

@[category test, AMS 5]
theorem C6_indep : α(C6) = 3 := by
  rw [indep_num_eq_computable]; decide +native

@[category test, AMS 5]
theorem C6_dom : dominationNumber C6 = 2 := by
  rw [dom_num_eq_computable]; decide +native

@[category test, AMS 5]
theorem C6_avg_dist : averageDistance C6 = 9/5 := by
  rw [avg_dist_eq_computable, show computable_avg_dist C6 = (9 / 5 : ℚ) from by decide +native]
  norm_num

@[category test, AMS 5]
private lemma C6_connected : C6.Connected := by
  simpa [C6] using (cycleGraph_connected (n := 5))

@[category test, AMS 5]
private lemma C6_edist_eq_dist (u v : Fin 6) : C6.edist u v = C6.dist u v := by
  exact (C6_connected u v).coe_dist_eq_edist.symm

@[category test, AMS 5]
private lemma C6_dist_le_three (u v : Fin 6) : C6.dist u v ≤ 3 := by
  rw [dist_eq_computable]
  fin_cases u <;> fin_cases v <;> decide +kernel

@[category test, AMS 5]
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

@[category test, AMS 5]
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

@[category test, AMS 5]
theorem C6_diameter : maxEccentricity C6 = 3 := by
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

@[category test, AMS 5]
theorem C6_radius : minEccentricity C6 = 3 := by
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

@[category test, AMS 5]
theorem C6_girth : C6.girth = 6 := by
  sorry

@[category test, AMS 5]
theorem C6_order : n C6 = 6 := by simp [n]

@[category test, AMS 5]
theorem C6_size : C6.edgeFinset.card = 6 := by
  decide +native

@[category test, AMS 5]
theorem C6_szeged : szegedIndex C6 = 54 := by
  rw [szeged_eq_computable]; decide +native

@[category test, AMS 5]
theorem C6_wiener : wienerIndex C6 = 27 := by
  rw [wiener_eq_computable]; decide +native

@[category test, AMS 5]
theorem C6_min_deg : C6.minDegree = 2 := by
  decide +native

@[category test, AMS 5]
theorem C6_max_deg : C6.maxDegree = 2 := by
  decide +native

@[category test, AMS 5]
theorem C6_avg_deg : averageDegree C6 = 2 := by
  unfold averageDegree; simp [Fintype.card_fin]; decide +native

@[category test, AMS 5]
private lemma C6_matching_edge_ncard_le_three (M : Subgraph C6) (hM : M.IsMatching) :
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

@[category test, AMS 5]
theorem C6_matching : m C6 = 3 := by
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
      exact C6_matching_edge_ncard_le_three M hM
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
      exact C6_matching_edge_ncard_le_three M hM
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

@[category test, AMS 5]
theorem C6_residue : residue C6 = 0 := by
  unfold residue; decide +native

@[category test, AMS 5]
theorem C6_annihilation : annihilationNumber C6 = 3 := by
  decide +native

@[category test, AMS 5]
theorem C6_cvetkovic : cvetkovic C6 = 3 := by
  sorry

/-  ### Star5 Tests -/

@[category test, AMS 5]
theorem Star5_indep : α(Star5) = 5 := by
  rw [indep_num_eq_computable]; decide +native

@[category test, AMS 5]
theorem Star5_dom : dominationNumber Star5 = 1 := by
  rw [dom_num_eq_computable]; decide +native

@[category test, AMS 5]
theorem Star5_avg_dist : averageDistance Star5 = 5/3 := by
  rw [avg_dist_eq_computable, show computable_avg_dist Star5 = (5 / 3 : ℚ) from by decide +native]
  norm_num

@[category test, AMS 5]
theorem Star5_diameter : maxEccentricity Star5 = 2 := by
  have hleaf : Star5.eccentricity (Sum.inr (0 : Fin 5)) = 2 := by
    rw [show Star5.eccentricity (Sum.inr (0 : Fin 5)) =
        Star5.eccent (Sum.inr (0 : Fin 5)) by
      simp [SimpleGraph.eccentricity, SimpleGraph.eccent, sSup_range]]
    apply le_antisymm
    · rw [SimpleGraph.eccent_le_iff]
      intro v
      cases v with
      | inl a =>
          have h : Star5.Adj (Sum.inr (0 : Fin 5)) (Sum.inl a) := by
            simp [Star5]
          have hed : Star5.edist (Sum.inr (0 : Fin 5)) (Sum.inl a) = 1 := by
            rwa [SimpleGraph.edist_eq_one_iff_adj]
          rw [hed]
          norm_num
      | inr b =>
          have h1 : Star5.Adj (Sum.inr (0 : Fin 5)) (Sum.inl (0 : Fin 1)) := by
            simp [Star5]
          have h2 : Star5.Adj (Sum.inl (0 : Fin 1)) (Sum.inr b) := by
            simp [Star5]
          have hed1 : Star5.edist (Sum.inr (0 : Fin 5)) (Sum.inl (0 : Fin 1)) = 1 := by
            rwa [SimpleGraph.edist_eq_one_iff_adj]
          have hed2 : Star5.edist (Sum.inl (0 : Fin 1)) (Sum.inr b) = 1 := by
            rwa [SimpleGraph.edist_eq_one_iff_adj]
          calc
            Star5.edist (Sum.inr (0 : Fin 5)) (Sum.inr b)
                ≤ Star5.edist (Sum.inr (0 : Fin 5)) (Sum.inl (0 : Fin 1)) +
                  Star5.edist (Sum.inl (0 : Fin 1)) (Sum.inr b) :=
              SimpleGraph.edist_triangle (G := Star5)
            _ = 2 := by
              rw [hed1, hed2]
              norm_num
    · have hnot : ¬ Star5.edist (Sum.inr (0 : Fin 5)) (Sum.inr (1 : Fin 5)) ≤ 1 := by
        rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
        simp [Star5]
      have hlt : (1 : ℕ∞) < Star5.edist (Sum.inr (0 : Fin 5)) (Sum.inr (1 : Fin 5)) :=
        lt_of_not_ge hnot
      have hle : (2 : ℕ∞) ≤ Star5.edist (Sum.inr (0 : Fin 5)) (Sum.inr (1 : Fin 5)) := by
        simpa using (ENat.add_one_le_iff (m := (1 : ℕ∞))
          (n := Star5.edist (Sum.inr (0 : Fin 5)) (Sum.inr (1 : Fin 5)))
          (ENat.coe_ne_top 1)).2 hlt
      exact hle.trans (SimpleGraph.edist_le_eccent (G := Star5)
        (u := Sum.inr (0 : Fin 5)) (v := Sum.inr (1 : Fin 5)))
  have hle_ecc : ∀ v, Star5.eccentricity v ≤ 2 := by
    intro v
    rw [show Star5.eccentricity v = Star5.eccent v by
      simp [SimpleGraph.eccentricity, SimpleGraph.eccent, sSup_range]]
    rw [SimpleGraph.eccent_le_iff]
    intro w
    cases v with
    | inl a =>
        cases w with
        | inl b =>
            fin_cases a
            fin_cases b
            simp
        | inr c =>
            have h : Star5.Adj (Sum.inl a) (Sum.inr c) := by
              simp [Star5]
            have hed : Star5.edist (Sum.inl a) (Sum.inr c) = 1 := by
              rwa [SimpleGraph.edist_eq_one_iff_adj]
            rw [hed]
            norm_num
    | inr b =>
        cases w with
        | inl a =>
            have h : Star5.Adj (Sum.inr b) (Sum.inl a) := by
              simp [Star5]
            have hed : Star5.edist (Sum.inr b) (Sum.inl a) = 1 := by
              rwa [SimpleGraph.edist_eq_one_iff_adj]
            rw [hed]
            norm_num
        | inr c =>
            have h1 : Star5.Adj (Sum.inr b) (Sum.inl (0 : Fin 1)) := by
              simp [Star5]
            have h2 : Star5.Adj (Sum.inl (0 : Fin 1)) (Sum.inr c) := by
              simp [Star5]
            have hed1 : Star5.edist (Sum.inr b) (Sum.inl (0 : Fin 1)) = 1 := by
              rwa [SimpleGraph.edist_eq_one_iff_adj]
            have hed2 : Star5.edist (Sum.inl (0 : Fin 1)) (Sum.inr c) = 1 := by
              rwa [SimpleGraph.edist_eq_one_iff_adj]
            calc
              Star5.edist (Sum.inr b) (Sum.inr c)
                  ≤ Star5.edist (Sum.inr b) (Sum.inl (0 : Fin 1)) +
                    Star5.edist (Sum.inl (0 : Fin 1)) (Sum.inr c) :=
                SimpleGraph.edist_triangle (G := Star5)
              _ = 2 := by
                rw [hed1, hed2]
                norm_num
  apply le_antisymm
  · rw [maxEccentricity]
    exact sSup_le (by
      rintro x ⟨v, rfl⟩
      exact hle_ecc v)
  · rw [maxEccentricity]
    exact le_sSup ⟨Sum.inr (0 : Fin 5), hleaf⟩

@[category test, AMS 5]
theorem Star5_radius : minEccentricity Star5 = 1 := by
  have hcenter : Star5.eccentricity (Sum.inl (0 : Fin 1)) = 1 := by
    rw [show Star5.eccentricity (Sum.inl (0 : Fin 1)) =
        Star5.eccent (Sum.inl (0 : Fin 1)) by
      simp [SimpleGraph.eccentricity, SimpleGraph.eccent, sSup_range]]
    apply le_antisymm
    · rw [SimpleGraph.eccent_le_iff]
      intro v
      cases v with
      | inl a =>
          fin_cases a
          simp
      | inr b =>
          have h : Star5.Adj (Sum.inl (0 : Fin 1)) (Sum.inr b) := by
            simp [Star5]
          rw [← SimpleGraph.edist_eq_one_iff_adj] at h
          simp [h]
    · have h : Star5.Adj (Sum.inl (0 : Fin 1)) (Sum.inr (0 : Fin 5)) := by
        simp [Star5]
      have hed : Star5.edist (Sum.inl (0 : Fin 1)) (Sum.inr (0 : Fin 5)) = 1 := by
        rwa [SimpleGraph.edist_eq_one_iff_adj]
      simpa [hed] using (SimpleGraph.edist_le_eccent (G := Star5)
        (u := Sum.inl (0 : Fin 1)) (v := Sum.inr (0 : Fin 5)))
  have hge : ∀ v, (1 : ℕ∞) ≤ Star5.eccentricity v := by
    intro v
    rw [show Star5.eccentricity v = Star5.eccent v by
      simp [SimpleGraph.eccentricity, SimpleGraph.eccent, sSup_range]]
    cases v with
    | inl a =>
        have h : Star5.Adj (Sum.inl a) (Sum.inr (0 : Fin 5)) := by
          simp [Star5]
        have hed : Star5.edist (Sum.inl a) (Sum.inr (0 : Fin 5)) = 1 := by
          rwa [SimpleGraph.edist_eq_one_iff_adj]
        simpa [hed] using (SimpleGraph.edist_le_eccent (G := Star5)
          (u := Sum.inl a) (v := Sum.inr (0 : Fin 5)))
    | inr b =>
        have h : Star5.Adj (Sum.inr b) (Sum.inl (0 : Fin 1)) := by
          simp [Star5]
        have hed : Star5.edist (Sum.inr b) (Sum.inl (0 : Fin 1)) = 1 := by
          rwa [SimpleGraph.edist_eq_one_iff_adj]
        simpa [hed] using (SimpleGraph.edist_le_eccent (G := Star5)
          (u := Sum.inr b) (v := Sum.inl (0 : Fin 1)))
  apply le_antisymm
  · rw [minEccentricity]
    exact sInf_le ⟨Sum.inl (0 : Fin 1), hcenter⟩
  · rw [minEccentricity]
    exact le_sInf (by
      rintro x ⟨v, rfl⟩
      exact hge v)

@[category test, AMS 5]
theorem Star5_girth : Star5.egirth = ⊤ := by
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

@[category test, AMS 5]
theorem Star5_order : n Star5 = 6 := by simp [n, Fintype.card_sum]

@[category test, AMS 5]
theorem Star5_size : Star5.edgeFinset.card = 5 := by
  decide +native

@[category test, AMS 5]
theorem Star5_szeged : szegedIndex Star5 = 25 := by
  rw [szeged_eq_computable]; decide +native

@[category test, AMS 5]
theorem Star5_wiener : wienerIndex Star5 = 25 := by
  rw [wiener_eq_computable]; decide +native

@[category test, AMS 5]
theorem Star5_min_deg : Star5.minDegree = 1 := by
  decide +native

@[category test, AMS 5]
theorem Star5_max_deg : Star5.maxDegree = 5 := by
  decide +native

@[category test, AMS 5]
theorem Star5_avg_deg : averageDegree Star5 = 5/3 := by
  unfold averageDegree
  simp [Star5, Fintype.card_sum]
  decide +kernel

@[category test, AMS 5]
private lemma star5_adj_incident_center {x y : Fin 1 ⊕ Fin 5}
    (h : Star5.Adj x y) : x = Sum.inl (0 : Fin 1) ∨ y = Sum.inl (0 : Fin 1) := by
  cases x with
  | inl a =>
      left
      fin_cases a
      rfl
  | inr _ =>
      cases y with
      | inl b =>
          right
          fin_cases b
          rfl
      | inr _ =>
          simp [Star5] at h

@[category test, AMS 5]
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

@[category test, AMS 5]
theorem Star5_matching : m Star5 = 1 := by
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

@[category test, AMS 5]
theorem Star5_residue : residue Star5 = 5 := by
  sorry

@[category test, AMS 5]
theorem Star5_annihilation : annihilationNumber Star5 = 5 := by
  decide +native

@[category test, AMS 5]
theorem Star5_cvetkovic : cvetkovic Star5 = 5 := by
  sorry

end WrittenOnTheWallII.Test
