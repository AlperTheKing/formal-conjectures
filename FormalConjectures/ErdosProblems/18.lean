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
# Erdős Problem 18

*Reference:*
* [erdosproblems.com/18](https://www.erdosproblems.com/18)
* [ErGr80] Erdős, P. and Graham, R. L. (1980). Old and New Problems and Results in Combinatorial Number
Theory. Monographies de L'Enseignement Mathématique, 28. Université de Genève. (See the
sections on Egyptian fractions or practical numbers).
* [Vo85] Vose, Michael D., Egyptian fractions. Bull. London Math. Soc. (1985), 21-24.
-/

open Filter Asymptotics Real

namespace Erdos18

/-- For a practical number $n$, $h(n)$ is the maximum over all $1 ≤ m ≤ n$ of
the minimum number of divisors of $n$ needed to represent $m$ as a sum of
distinct divisors. -/
noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧ m ∈ subsetSums D}

/- ### Examples for `practicalH` -/

/-- $h(1) = 1$: we need the single divisor {1} to represent 1. -/
@[category test, AMS 11]
theorem practicalH_one : practicalH 1 = 1 := by
  norm_num [subsetSums, practicalH]

/-- $h(2) = 1$: divisors are {1, 2}, each of m=1,2 needs only 1 divisor. -/
@[category test, AMS 11]
theorem practicalH_two : practicalH 2 = 1 := by
  simp only [practicalH, (by decide : Finset.Icc 1 2 = ({1, 2} : Finset ℕ)),
    (by decide : Nat.divisors 2 = ({1, 2} : Finset ℕ)), Finset.sup_insert, Finset.sup_singleton]
  have h1 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2} ∧ D.card = k ∧ 1 ∈ subsetSums D} = 1 :=
    le_antisymm (Nat.sInf_le ⟨{1}, by simp, rfl, {1}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {1}, by simp, rfl, {1}, rfl.subset, by simp⟩ fun k ⟨D, _, hD, B, hB, hm⟩ =>
        hD ▸ Finset.one_le_card.mpr ((Finset.nonempty_iff_ne_empty.mpr fun h => by simp [h] at hm).mono hB))
  have h2 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2} ∧ D.card = k ∧ 2 ∈ subsetSums D} = 1 :=
    le_antisymm (Nat.sInf_le ⟨{2}, by simp, rfl, {2}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {2}, by simp, rfl, {2}, rfl.subset, by simp⟩ fun k ⟨D, _, hD, B, hB, hm⟩ =>
        hD ▸ Finset.one_le_card.mpr ((Finset.nonempty_iff_ne_empty.mpr fun h => by simp [h] at hm).mono hB))
  simp [h1, h2]

/-- $h(6) = 2$: divisors are {1, 2, 3, 6}. The hardest m to represent is
m=4 or m=5, each requiring 2 divisors: 4=1+3, 5=2+3. -/
@[category test, AMS 11]
theorem practicalH_six : practicalH 6 = 2 := by
  simp only [practicalH, (by decide : Finset.Icc 1 6 = ({1, 2, 3, 4, 5, 6} : Finset ℕ)),
    (by decide : Nat.divisors 6 = ({1, 2, 3, 6} : Finset ℕ)), Finset.sup_insert,
    Finset.sup_singleton]
  have one_le_of_subset_sum_singleton_bound {m k : ℕ}
      (hm0 : m ≠ 0)
      (hk : ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 6} ∧ D.card = k ∧ m ∈ subsetSums D) :
      1 ≤ k := by
    rcases hk with ⟨D, _hDsub, hDcard, B, hBsub, hsum⟩
    subst k
    exact Finset.one_le_card.mpr
      ((Finset.nonempty_iff_ne_empty.mpr fun hB => by
        simp [hB] at hsum
        exact hm0 hsum).mono hBsub)
  have two_le_of_not_single {m k : ℕ}
      (hm : m ≠ 0) (hm1 : m ≠ 1) (hm2 : m ≠ 2) (hm3 : m ≠ 3) (hm6 : m ≠ 6)
      (hk : ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 6} ∧ D.card = k ∧ m ∈ subsetSums D) :
      2 ≤ k := by
    have hkpos : 1 ≤ k := one_le_of_subset_sum_singleton_bound hm hk
    by_contra hnot
    have hk_le_one : k ≤ 1 := by omega
    have hk_eq : k = 1 := by omega
    rcases hk with ⟨D, hDsub, hDcard, B, hBsub, hsum⟩
    subst k
    obtain ⟨d, hD_eq⟩ := Finset.card_eq_one.mp hDcard
    subst D
    have hd_cases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 := by simpa using hDsub (by simp)
    by_cases hdB : d ∈ B
    · have hB_eq : B = {d} := by
        apply Finset.Subset.antisymm hBsub
        intro x hx
        rw [Finset.mem_singleton.mp hx]
        exact hdB
      rw [hB_eq] at hsum
      simp at hsum
      rcases hd_cases with rfl | rfl | rfl | rfl <;> omega
    · have hB_eq : B = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx' := hBsub hx
        have hx_eq : x = d := by simpa using hx'
        subst x
        exact hdB hx
      rw [hB_eq] at hsum
      simp at hsum
      exact hm hsum
  have h1 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 6} ∧ D.card = k ∧
      1 ∈ subsetSums D} = 1 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{1}, by simp, rfl, {1}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {1}, by simp, rfl, {1}, rfl.subset, by simp⟩
          (fun k hk => one_le_of_subset_sum_singleton_bound (by norm_num) hk))
  have h2 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 6} ∧ D.card = k ∧
      2 ∈ subsetSums D} = 1 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{2}, by simp, rfl, {2}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {2}, by simp, rfl, {2}, rfl.subset, by simp⟩
          (fun k hk => one_le_of_subset_sum_singleton_bound (by norm_num) hk))
  have h3 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 6} ∧ D.card = k ∧
      3 ∈ subsetSums D} = 1 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{3}, by simp, rfl, {3}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {3}, by simp, rfl, {3}, rfl.subset, by simp⟩
          (fun k hk => one_le_of_subset_sum_singleton_bound (by norm_num) hk))
  have h4 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 6} ∧ D.card = k ∧
      4 ∈ subsetSums D} = 2 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{1, 3}, by simp, rfl, {1, 3}, rfl.subset, by simp⟩)
      (le_csInf ⟨2, {1, 3}, by simp, rfl, {1, 3}, rfl.subset, by simp⟩
          (fun k hk => two_le_of_not_single (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) hk))
  have h5 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 6} ∧ D.card = k ∧
      5 ∈ subsetSums D} = 2 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{2, 3}, by decide, rfl, {2, 3}, rfl.subset, by norm_num⟩)
      (le_csInf ⟨2, {2, 3}, by decide, rfl, {2, 3}, rfl.subset, by norm_num⟩
          (fun k hk => two_le_of_not_single (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) hk))
  have h6 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 6} ∧ D.card = k ∧
      6 ∈ subsetSums D} = 1 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{6}, by simp, rfl, {6}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {6}, by simp, rfl, {6}, rfl.subset, by simp⟩
          (fun k hk => one_le_of_subset_sum_singleton_bound (by norm_num) hk))
  simp [h1, h2, h3, h4, h5, h6]

/-- $h(12) = 3$: divisors are {1, 2, 3, 4, 6, 12}. The hardest m is
m=11, requiring 3 divisors: 11=1+4+6. -/
@[category test, AMS 11]
theorem practicalH_twelve : practicalH 12 = 3 := by
  simp only [practicalH,
    (by decide : Finset.Icc 1 12 =
      ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} : Finset ℕ)),
    (by decide : Nat.divisors 12 = ({1, 2, 3, 4, 6, 12} : Finset ℕ)),
    Finset.sup_insert, Finset.sup_singleton]
  have one_le_of_subset_sum_nonzero {m k : ℕ}
      (hm0 : m ≠ 0)
      (hk : ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 4, 6, 12} ∧ D.card = k ∧ m ∈ subsetSums D) :
      1 ≤ k := by
    rcases hk with ⟨D, _hDsub, hDcard, B, hBsub, hsum⟩
    subst k
    exact Finset.one_le_card.mpr
      ((Finset.nonempty_iff_ne_empty.mpr fun hB => by
        simp [hB] at hsum
        exact hm0 hsum).mono hBsub)
  have two_le_of_not_single {m k : ℕ}
      (hm0 : m ≠ 0) (hm1 : m ≠ 1) (hm2 : m ≠ 2) (hm3 : m ≠ 3)
      (hm4 : m ≠ 4) (hm6 : m ≠ 6) (hm12 : m ≠ 12)
      (hk : ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 4, 6, 12} ∧ D.card = k ∧
        m ∈ subsetSums D) :
      2 ≤ k := by
    have hkpos : 1 ≤ k := one_le_of_subset_sum_nonzero hm0 hk
    by_contra hnot
    have hk_eq : k = 1 := by omega
    rcases hk with ⟨D, hDsub, hDcard, B, hBsub, hsum⟩
    subst k
    obtain ⟨d, hD_eq⟩ := Finset.card_eq_one.mp hDcard
    subst D
    have hd_cases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 6 ∨ d = 12 := by
      simpa using hDsub (by simp)
    by_cases hdB : d ∈ B
    · have hB_eq : B = {d} := by
        apply Finset.Subset.antisymm hBsub
        intro x hx
        rw [Finset.mem_singleton.mp hx]
        exact hdB
      rw [hB_eq] at hsum
      simp at hsum
      rcases hd_cases with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · have hB_eq : B = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx' := hBsub hx
        have hx_eq : x = d := by simpa using hx'
        subst x
        exact hdB hx
      rw [hB_eq] at hsum
      simp at hsum
      exact hm0 hsum
  have three_le_for_eleven {k : ℕ}
      (hk : ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 4, 6, 12} ∧ D.card = k ∧
        11 ∈ subsetSums D) :
      3 ≤ k := by
    have hkpos : 1 ≤ k := one_le_of_subset_sum_nonzero (by norm_num) hk
    by_contra hnot
    have hk_le_two : k ≤ 2 := by omega
    rcases hk with ⟨D, hDsub, hDcard, B, hBsub, hsum⟩
    subst k
    have hBsub_all : B ⊆ ({1, 2, 3, 4, 6, 12} : Finset ℕ) := hBsub.trans hDsub
    have hBcard_le : B.card ≤ 2 := by
      exact (Finset.card_le_card hBsub).trans hk_le_two
    have hBmem : B ∈ (({1, 2, 3, 4, 6, 12} : Finset ℕ).powerset.filter
        (fun S => S.card ≤ 2)) := by
      simp [hBsub_all, hBcard_le]
    fin_cases hBmem <;> norm_num at hsum
  have h1 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 4, 6, 12} ∧ D.card = k ∧
      1 ∈ subsetSums D} = 1 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{1}, by simp, rfl, {1}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {1}, by simp, rfl, {1}, rfl.subset, by simp⟩
          (fun k hk => one_le_of_subset_sum_nonzero (by norm_num) hk))
  have h2 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 4, 6, 12} ∧ D.card = k ∧
      2 ∈ subsetSums D} = 1 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{2}, by simp, rfl, {2}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {2}, by simp, rfl, {2}, rfl.subset, by simp⟩
          (fun k hk => one_le_of_subset_sum_nonzero (by norm_num) hk))
  have h3 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 4, 6, 12} ∧ D.card = k ∧
      3 ∈ subsetSums D} = 1 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{3}, by simp, rfl, {3}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {3}, by simp, rfl, {3}, rfl.subset, by simp⟩
          (fun k hk => one_le_of_subset_sum_nonzero (by norm_num) hk))
  have h4 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 4, 6, 12} ∧ D.card = k ∧
      4 ∈ subsetSums D} = 1 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{4}, by simp, rfl, {4}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {4}, by simp, rfl, {4}, rfl.subset, by simp⟩
          (fun k hk => one_le_of_subset_sum_nonzero (by norm_num) hk))
  have h5 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 4, 6, 12} ∧ D.card = k ∧
      5 ∈ subsetSums D} = 2 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{1, 4}, by simp, rfl, {1, 4}, rfl.subset, by simp⟩)
      (le_csInf ⟨2, {1, 4}, by simp, rfl, {1, 4}, rfl.subset, by simp⟩
          (fun k hk => two_le_of_not_single (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk))
  have h6 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 4, 6, 12} ∧ D.card = k ∧
      6 ∈ subsetSums D} = 1 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{6}, by simp, rfl, {6}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {6}, by simp, rfl, {6}, rfl.subset, by simp⟩
          (fun k hk => one_le_of_subset_sum_nonzero (by norm_num) hk))
  have h7 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 4, 6, 12} ∧ D.card = k ∧
      7 ∈ subsetSums D} = 2 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{1, 6}, by simp, rfl, {1, 6}, rfl.subset, by simp⟩)
      (le_csInf ⟨2, {1, 6}, by simp, rfl, {1, 6}, rfl.subset, by simp⟩
          (fun k hk => two_le_of_not_single (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk))
  have h8 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 4, 6, 12} ∧ D.card = k ∧
      8 ∈ subsetSums D} = 2 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{2, 6}, by decide, rfl, {2, 6}, rfl.subset, by norm_num⟩)
      (le_csInf ⟨2, {2, 6}, by decide, rfl, {2, 6}, rfl.subset, by norm_num⟩
          (fun k hk => two_le_of_not_single (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk))
  have h9 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 4, 6, 12} ∧ D.card = k ∧
      9 ∈ subsetSums D} = 2 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{3, 6}, by decide, rfl, {3, 6}, rfl.subset, by norm_num⟩)
      (le_csInf ⟨2, {3, 6}, by decide, rfl, {3, 6}, rfl.subset, by norm_num⟩
          (fun k hk => two_le_of_not_single (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk))
  have h10 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 4, 6, 12} ∧ D.card = k ∧
      10 ∈ subsetSums D} = 2 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{4, 6}, by decide, rfl, {4, 6}, rfl.subset, by norm_num⟩)
      (le_csInf ⟨2, {4, 6}, by decide, rfl, {4, 6}, rfl.subset, by norm_num⟩
          (fun k hk => two_le_of_not_single (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk))
  have h11 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 4, 6, 12} ∧ D.card = k ∧
      11 ∈ subsetSums D} = 3 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{1, 4, 6}, by decide, rfl, {1, 4, 6}, rfl.subset, by norm_num⟩)
      (le_csInf ⟨3, {1, 4, 6}, by decide, rfl, {1, 4, 6}, rfl.subset, by norm_num⟩
          (fun k hk => three_le_for_eleven hk))
  have h12 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2, 3, 4, 6, 12} ∧ D.card = k ∧
      12 ∈ subsetSums D} = 1 := by
    exact le_antisymm
      (Nat.sInf_le ⟨{12}, by simp, rfl, {12}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {12}, by simp, rfl, {12}, rfl.subset, by simp⟩
          (fun k hk => one_le_of_subset_sum_nonzero (by norm_num) hk))
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

/-- For any practical number $n$, $h(n) ≤ number of divisors of $n$. -/
@[category test, AMS 11]
theorem practicalH_le_divisors (n : ℕ) (hn : Nat.IsPractical n) :
    practicalH n ≤ n.divisors.card := by
  simp only [practicalH, Finset.sup_le_iff, Finset.mem_Icc]
  exact fun m ⟨_, hm⟩ => Nat.sInf_le ⟨n.divisors, Finset.Subset.refl _, rfl, hn m hm⟩

/-- $h(n!)$ is well-defined since $n!$ is practical for $n ≥ 1$. -/
@[category textbook, AMS 11]
theorem factorial_isPractical (n : ℕ) : Nat.IsPractical n.factorial := by
    induction n with
  | zero =>
    intro m hm; simp at hm; interval_cases m
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by simp, by simp⟩
  | succ n ih =>
    intro m hm
    by_cases hle : m ≤ n.factorial
    · exact subsetSums_mono (by exact_mod_cast (Nat.divisors_subset_of_dvd
        (Nat.factorial_ne_zero _) (Nat.factorial_dvd_factorial n.le_succ))) (ih m hle)
    · push_neg at hle; rw [Nat.factorial_succ] at hm
      set q := m / (n + 1); set r := m % (n + 1)
      have h_div : m = (n + 1) * q + r := (Nat.div_add_mod m (n + 1)).symm
      have h_r_lt : r < n + 1 := Nat.mod_lt m (Nat.succ_pos n)
      obtain ⟨B, hB_sub, hB_sum⟩ := ih q (Nat.div_le_of_le_mul (by linarith))
      have hdvd : ∀ d ∈ B, d * (n + 1) ∈ (n + 1).factorial.divisors := fun d hd => by
        refine Nat.mem_divisors.mpr ⟨?_, Nat.factorial_ne_zero _⟩
        rw [mul_comm, Nat.factorial_succ]
        exact mul_dvd_mul_left _ (Nat.dvd_of_mem_divisors (by exact_mod_cast hB_sub hd))
      have hB'_sum : (B.image (· * (n + 1))).sum id = (n + 1) * q := by
        rw [Finset.sum_image (fun a _ b _ h => mul_right_cancel₀ (by omega) h)]
        simp [Finset.mul_sum, mul_comm, hB_sum]
      by_cases hr : r = 0
      · rw [show m = (B.image (· * (n + 1))).sum id from by rw [hB'_sum]; omega]
        exact ⟨_, fun x hx => by
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx; exact hdvd d hd, rfl⟩
      · have h_disj : Disjoint (B.image (· * (n + 1))) {r} := by
          rw [Finset.disjoint_singleton_right, Finset.mem_image]; rintro ⟨d, hd, hdr⟩
          have : 0 < d := Nat.pos_of_dvd_of_pos
            (Nat.dvd_of_mem_divisors (by exact_mod_cast hB_sub hd)) (Nat.factorial_pos n)
          have := le_mul_of_one_le_left (Nat.zero_le (n + 1)) this
          omega
        rw [show m = (B.image (· * (n + 1)) ∪ {r}).sum id from by
          rw [Finset.sum_union h_disj, Finset.sum_singleton, hB'_sum, id_eq]; exact h_div]
        exact ⟨_, fun x hx => by
          rcases Finset.mem_union.mp hx with h | h
          · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp h; exact hdvd d hd
          · rw [Finset.mem_singleton.mp h]; exact Nat.mem_divisors.mpr
              ⟨(Nat.dvd_factorial (by omega) (by omega)).trans
                (Nat.factorial_dvd_factorial n.le_succ), Nat.factorial_ne_zero _⟩, rfl⟩

/- ### Erdős's Conjectures -/

/--
**Conjecture 1.**
Are there infinitely many practical numbers $m$ such that $h(m) < (\log \log m)^{O(1)}$?

More precisely: does there exist a constant $C > 0$ such that for infinitely many
practical numbers $m$, we have $h(m) < (\log \log m)^C$?
-/
@[category research open, AMS 11]
theorem erdos_18a : answer(sorry) ↔
    ∃ C : ℝ, 0 < C ∧ ∃ᶠ m in atTop, Nat.IsPractical m ∧
      (practicalH m : ℝ) < (log (log m)) ^ C := by
  sorry

/--
**Conjecture 2.**
Is it true that $h(n!) < n^{o(1)}$? That is, for all $\varepsilon > 0$,
is $h(n!) < n^\varepsilon$ for sufficiently large $n$?
-/
@[category research open, AMS 11]
theorem erdos_18b : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (practicalH n.factorial : ℝ) < (n : ℝ) ^ ε := by
  sorry

/--
**Conjecture 3.**
Or perhaps even $h(n!) < (\log n)^{O(1)}$?

Erdős offered \$250 for a proof or disproof.
-/
@[category research open, AMS 11]
theorem erdos_18c : answer(sorry) ↔
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (practicalH n.factorial : ℝ) < (log n) ^ C := by
  sorry

/--
**Erdős's Theorem.**
Erdős proved that $h(n!) < n$ for all $n \ge 1$.
-/
@[category research solved, AMS 11]
theorem erdos_18_upper_bound :
    ∀ᶠ n : ℕ in atTop, practicalH (Nat.factorial n) < n := by
  sorry

/--
**Vose's Theorem.**
Vose proved the existence of infinitely many practical numbers $m$ such that
$h(m) \ll (\log m)^{1/2}$. This gives a positive answer to a weaker form of Conjecture 1.
-/
@[category research solved, AMS 11]
theorem erdos_18_vose :
    ∃ C : ℝ, 0 < C ∧ ∃ᶠ m in atTop, Nat.IsPractical m ∧
      (practicalH m : ℝ) < C * (log m) ^ (1 / 2 : ℝ) := by
  sorry

end Erdos18
