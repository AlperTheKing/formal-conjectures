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
# Erdős Problem 23

*References:*
* [erdosproblems.com/23](https://www.erdosproblems.com/23)
* [OEIS A389646](https://oeis.org/A389646)
-/

open SimpleGraph BigOperators Classical

namespace Erdos23

/--
Every triangle-free graph on $5$ vertices can be made bipartite by removing at most $1$ edge.
This is the $n = 1$ case of Erdős Problem 23.
-/
@[category test, AMS 5]
theorem erdos_23.variants.n1 :
    ∀ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 5)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
  sorry

/--
There exists a triangle-free graph on $5$ vertices such that at least $1$ edge must be removed
to make it bipartite. This shows the bound in `erdos_23_n1` is tight.
-/
@[category test, AMS 5]
theorem erdos_23.variants.n1_tight :
    ∃ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 5)),
        H ≤ G → H.IsBipartite → 1 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  sorry

/--
The blow-up of the 5-cycle $C_5$: replace each vertex of $C_5$ with an independent set of $n$
vertices, and connect two vertices iff their corresponding vertices in $C_5$ are adjacent.
The vertex set is $\mathbb{Z}/5\mathbb{Z} \times \{0, \ldots, n-1\}$, where $(i, a)$ and $(j, b)$
are adjacent iff $j = i + 1$ or $i = j + 1$ in $\mathbb{Z}/5\mathbb{Z}$.
-/
def blowupC5 (n : ℕ) : SimpleGraph (ZMod 5 × Fin n) :=
  SimpleGraph.fromRel fun (i, _) (j, _) => i + 1 = j ∨ j + 1 = i

/- BEGIN blowupC5_tight double-counting certificate -/
def vtx (n : ℕ) (a : ZMod 5 → Fin n) (i : ZMod 5) : ZMod 5 × Fin n := (i, a i)
def cycleEdge (n : ℕ) (a : ZMod 5 → Fin n) (i : ZMod 5) : Sym2 (ZMod 5 × Fin n) :=
  s(vtx n a i, vtx n a (i + 1))

lemma succ_ne (i : ZMod 5) : i ≠ i + 1 := by revert i; decide

-- Milestone 1: each cycle edge is a blowupC5 edge
lemma cycleEdge_mem (n : ℕ) (a : ZMod 5 → Fin n) (i : ZMod 5) :
    cycleEdge n a i ∈ (blowupC5 n).edgeFinset := by
  rw [cycleEdge, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, blowupC5,
    SimpleGraph.fromRel_adj]
  refine ⟨fun h => ?_, Or.inl (Or.inl rfl)⟩
  rw [vtx, vtx, Prod.ext_iff] at h
  exact succ_ne i h.1

-- Milestone 2+3: bipartite subgraph misses some cycle edge of every tuple
lemma missing_exists (n : ℕ) (H : SimpleGraph (ZMod 5 × Fin n))
    (hBip : H.IsBipartite) (a : ZMod 5 → Fin n) :
    ∃ i : ZMod 5, cycleEdge n a i ∈ (blowupC5 n).edgeFinset \ H.edgeFinset := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨c⟩ := hBip
  have hadj : ∀ i : ZMod 5, H.Adj (vtx n a i) (vtx n a (i + 1)) := by
    intro i
    have h2 := hcon i
    rw [Finset.mem_sdiff, not_and, not_not] at h2
    have hmem := h2 (cycleEdge_mem n a i)
    rw [cycleEdge, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hmem
    exact hmem
  have hne : ∀ i : ZMod 5, c (vtx n a i) ≠ c (vtx n a (i + 1)) := fun i => c.valid (hadj i)
  have key : ∀ i j : ZMod 5, j = i + 1 → (c (vtx n a i)).val ≠ (c (vtx n a j)).val := by
    intro i j hij h
    exact hne i (Fin.ext (hij ▸ h))
  have h01 := key 0 1 (by decide)
  have h12 := key 1 2 (by decide)
  have h23 := key 2 3 (by decide)
  have h34 := key 3 4 (by decide)
  have h40 := key 4 0 (by decide)
  have b0 := (c (vtx n a 0)).isLt
  have b1 := (c (vtx n a 1)).isLt
  have b2 := (c (vtx n a 2)).isLt
  have b3 := (c (vtx n a 3)).isLt
  have b4 := (c (vtx n a 4)).isLt
  omega

-- the "swapped" case of a cycle-edge collision is impossible in ZMod 5
lemma no_caseB (i i' : ZMod 5) (hi1 : i = i' + 1) (hi2 : i + 1 = i') : False := by
  revert hi1 hi2; revert i i'; decide

-- a cycle edge + its 3 free coordinates determine the whole tuple and the position
lemma cycleEdge_inj (n : ℕ) (a a' : ZMod 5 → Fin n) (i i' : ZMod 5)
    (hedge : cycleEdge n a i = cycleEdge n a' i')
    (h2 : a (i + 2) = a' (i' + 2)) (h3 : a (i + 3) = a' (i' + 3))
    (h4 : a (i + 4) = a' (i' + 4)) : a = a' ∧ i = i' := by
  rw [cycleEdge, cycleEdge, Sym2.mk_eq_mk_iff] at hedge
  rcases hedge with hc | hc
  · simp only [vtx, Prod.mk.injEq] at hc
    obtain ⟨⟨hi, hai⟩, ⟨_, hai1⟩⟩ := hc
    subst hi
    refine ⟨?_, rfl⟩
    funext x
    obtain ⟨k, rfl⟩ : ∃ k : ZMod 5, x = i + k := ⟨x - i, by ring⟩
    fin_cases k <;> simp_all
  · exfalso
    simp only [Prod.swap_prod_mk, vtx, Prod.mk.injEq] at hc
    obtain ⟨⟨hi1, _⟩, ⟨hi2, _⟩⟩ := hc
    exact no_caseB i i' hi1 hi2

-- Double-counting: n^2 ≤ #(missing edges)
theorem blowupC5_tight' (n : ℕ) (hn : 0 < n) (H : SimpleGraph (ZMod 5 × Fin n))
    (hBip : H.IsBipartite) :
    n ^ 2 ≤ ((blowupC5 n).edgeFinset \ H.edgeFinset).card := by
  classical
  have hlow : n ^ 5 ≤ (Finset.univ.filter (fun p : (ZMod 5 → Fin n) × ZMod 5 =>
      cycleEdge n p.1 p.2 ∈ (blowupC5 n).edgeFinset \ H.edgeFinset)).card := by
    have h := Finset.card_le_card_of_surjOn
      (s := Finset.univ.filter (fun p : (ZMod 5 → Fin n) × ZMod 5 =>
        cycleEdge n p.1 p.2 ∈ (blowupC5 n).edgeFinset \ H.edgeFinset))
      (t := (Finset.univ : Finset (ZMod 5 → Fin n))) Prod.fst (by
        intro a _
        obtain ⟨i, hi⟩ := missing_exists n H hBip a
        refine ⟨(a, i), ?_, rfl⟩
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hi)
    rwa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card] at h
  have hupp : (Finset.univ.filter (fun p : (ZMod 5 → Fin n) × ZMod 5 =>
      cycleEdge n p.1 p.2 ∈ (blowupC5 n).edgeFinset \ H.edgeFinset)).card
      ≤ ((blowupC5 n).edgeFinset \ H.edgeFinset).card * n ^ 3 := by
    have hPcard := Finset.card_le_card_of_injOn
      (s := Finset.univ.filter (fun p : (ZMod 5 → Fin n) × ZMod 5 =>
        cycleEdge n p.1 p.2 ∈ (blowupC5 n).edgeFinset \ H.edgeFinset))
      (t := ((blowupC5 n).edgeFinset \ H.edgeFinset) ×ˢ
        (Finset.univ : Finset (Fin n × Fin n × Fin n)))
      (fun p => (cycleEdge n p.1 p.2, p.1 (p.2 + 2), p.1 (p.2 + 3), p.1 (p.2 + 4)))
      (by
        intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true]
        exact hp)
      (by
        intro p _ q _ heq
        obtain ⟨a, i⟩ := p; obtain ⟨a', i'⟩ := q
        simp only [Prod.mk.injEq] at heq
        obtain ⟨he, h2, h3, h4⟩ := heq
        obtain ⟨ha, hi⟩ := cycleEdge_inj n a a' i i' he h2 h3 h4
        rw [ha, hi])
    rw [Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
      Fintype.card_fin] at hPcard
    exact le_trans hPcard (le_of_eq (by ring))
  have hcomb : n ^ 2 * n ^ 3 ≤ ((blowupC5 n).edgeFinset \ H.edgeFinset).card * n ^ 3 :=
    calc n ^ 2 * n ^ 3 = n ^ 5 := by ring
      _ ≤ _ := hlow
      _ ≤ _ := hupp
  exact le_of_mul_le_mul_right hcomb (pow_pos hn 3)

/- END blowupC5_tight certificate -/

/--
The blow-up of $C_5$ shows that the bound $n^2$ in Erdős Problem 23 is tight:
any bipartite subgraph must omit at least $n^2$ edges.
-/
@[category test, AMS 5]
theorem blowupC5_tight (n : ℕ) (_hn : 0 < n) (H : SimpleGraph (ZMod 5 × Fin n))
    (hH : H ≤ blowupC5 n) (hBip : H.IsBipartite) :
    n ^ 2 ≤ ((blowupC5 n).edgeFinset \ H.edgeFinset).card := by
  exact blowupC5_tight' n _hn H hBip

end Erdos23

#print axioms Erdos23.blowupC5_tight
