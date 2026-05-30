/-
Copyright 2026 The Formal Conjectures Authors.

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
# Erdős Problem 885

*References:*
- [erdosproblems.com/885](https://www.erdosproblems.com/885)
- [ErRo97] Erdős, P. and Rosenfeld, M., The factor-difference set of integers. (1997)
- [Ji99] Jiménez-Urroz, J., A note on a conjecture of Erdős and {R}osenfeld. (1999)
- [Br19] Bremner, A., On a problem of Erdős related to common factor differences. (2019)
-/

open Nat Set Finset

namespace Erdos885

/--
For integer $n \geq 1$ we define the factor difference set of $n$ by
$D(n) = \{|a-b| : n=ab\}$.
-/
def factorDifferenceSet (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, n = a * b ∧ (d : ℤ) = |(a : ℤ) - b|}

lemma factorDifferenceSet_finite_of_pos {n : ℕ} (hn : 0 < n) :
    (factorDifferenceSet n).Finite := by
  refine (Set.finite_Icc 0 n).subset ?_
  intro d hd
  rcases hd with ⟨a, b, hnab, hdiff⟩
  have ha_le : a ≤ n := Nat.le_of_dvd hn ⟨b, hnab⟩
  have hb_le : b ≤ n := Nat.le_of_dvd hn ⟨a, by rw [Nat.mul_comm]; exact hnab⟩
  have h_abs : |(a : ℤ) - b| ≤ (n : ℤ) := by
    rw [abs_le]
    omega
  exact ⟨Nat.zero_le d, by
    have : (d : ℤ) ≤ (n : ℤ) := by simpa [hdiff] using h_abs
    exact_mod_cast this⟩

/--
Is it true that, for every $k \geq 1$, there exist integers $N_1 < \dots < N_k$ such that
$|\cap_i D(N_i)| \geq k$?
-/
@[category research open, AMS 11]
theorem erdos_885 : answer(sorry) ↔ ∀ k ≥ 1,
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = k ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ k := by
  sorry

/--
Erdős and Rosenfeld [ErRo97] proved this is true for $k=2$.
-/
@[category research solved, AMS 11]
theorem erdos_885.variants.k_eq_2 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 2 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 2 := by
  refine ⟨{8, 120}, ?_, by norm_num, ?_⟩
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl <;> norm_num
  · have hsub : ({2, 7} : Set ℕ) ⊆
        ⋂ n ∈ ({8, 120} : Finset ℕ), factorDifferenceSet n := by
      intro d hd
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      simp only [Set.mem_iInter]
      intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl <;> rcases hd with rfl | rfl
      · exact ⟨2, 4, by norm_num, by norm_num⟩
      · exact ⟨1, 8, by norm_num, by norm_num⟩
      · exact ⟨10, 12, by norm_num, by norm_num⟩
      · exact ⟨8, 15, by norm_num, by norm_num⟩
    have hfin : (⋂ n ∈ ({8, 120} : Finset ℕ), factorDifferenceSet n).Finite :=
      (factorDifferenceSet_finite_of_pos (by norm_num : 0 < 8)).subset (by
        intro d hd
        simp only [Set.mem_iInter] at hd
        exact hd 8 (by simp))
    simpa [Set.ncard_pair (by norm_num : (2 : ℕ) ≠ 7)] using
      Set.ncard_le_ncard hsub hfin

/--
Jiménez-Urroz [Ji99] proved this for $k=3$.
-/
@[category research solved, AMS 11]
theorem erdos_885.variants.k_eq_3 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 3 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 3 := by
  refine ⟨{120, 528, 4488}, ?_, by norm_num, ?_⟩
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl <;> norm_num
  · have hsub : ({2, 37, 58} : Set ℕ) ⊆
        ⋂ n ∈ ({120, 528, 4488} : Finset ℕ), factorDifferenceSet n := by
      intro d hd
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      simp only [Set.mem_iInter]
      intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl
      · exact ⟨10, 12, by norm_num, by norm_num⟩
      · exact ⟨3, 40, by norm_num, by norm_num⟩
      · exact ⟨2, 60, by norm_num, by norm_num⟩
      · exact ⟨22, 24, by norm_num, by norm_num⟩
      · exact ⟨11, 48, by norm_num, by norm_num⟩
      · exact ⟨8, 66, by norm_num, by norm_num⟩
      · exact ⟨66, 68, by norm_num, by norm_num⟩
      · exact ⟨51, 88, by norm_num, by norm_num⟩
      · exact ⟨44, 102, by norm_num, by norm_num⟩
    have hfin : (⋂ n ∈ ({120, 528, 4488} : Finset ℕ), factorDifferenceSet n).Finite :=
      (factorDifferenceSet_finite_of_pos (by norm_num : 0 < 120)).subset (by
        intro d hd
        simp only [Set.mem_iInter] at hd
        exact hd 120 (by simp))
    have hcard : ({2, 37, 58} : Set ℕ).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp : (2 : ℕ) ∉ ({37, 58} : Set ℕ))]
      rw [Set.ncard_pair (by norm_num : (37 : ℕ) ≠ 58)]
    simpa [hcard] using Set.ncard_le_ncard hsub hfin

/--
Bremner [Br19] proved this for $k=4$.
-/
@[category research solved, AMS 11]
theorem erdos_885.variants.k_eq_4 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 4 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 4 := by
  sorry

end Erdos885
