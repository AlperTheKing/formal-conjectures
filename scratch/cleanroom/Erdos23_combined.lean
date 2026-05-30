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

/- ===== n1 certificate helpers (private) ===== -/
set_option maxRecDepth 10000

private def bN (n i : ℕ) : Bool := (n / 2 ^ i) % 2 == 1
private def trisN : List (ℕ × ℕ × ℕ) :=
  [(0,1,4),(0,2,5),(0,3,6),(1,2,7),(1,3,8),(2,3,9),(4,5,7),(4,6,8),(5,6,9),(7,8,9)]
private def triFreeN (n : ℕ) : Bool := trisN.all (fun t => !(bN n t.1 && bN n t.2.1 && bN n t.2.2))
private def edgeU : Fin 10 → ℕ := ![0,0,0,0,1,1,1,2,2,3]
private def edgeV : Fin 10 → ℕ := ![1,2,3,4,2,3,4,3,4,4]
private def sameColorAt (c : ℕ) (i : Fin 10) : Bool := bN c (edgeU i) == bN c (edgeV i)
-- Fin 5 endpoints
private def eU : Fin 10 → Fin 5 := ![0,0,0,0,1,1,1,2,2,3]
private def eV : Fin 10 → Fin 5 := ![1,2,3,4,2,3,4,3,4,4]
set_option maxHeartbeats 4000000

private theorem n1_core_strong : ∀ n : Fin 1024, triFreeN n.val = true →
    ∃ c : Fin 32, ∃ bad : Option (Fin 10), ∀ i : Fin 10,
      bN n.val i.val = true → sameColorAt c.val i = true → bad = some i := by decide

private theorem n1_of_core
    (hcore : ∀ n : Fin 1024, triFreeN n.val = true → ∃ c : Fin 32, ∃ bad : Option (Fin 10),
      ∀ i : Fin 10, bN n.val i.val = true → sameColorAt c.val i = true → bad = some i) :
    ∀ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 5)),
      H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
  classical
  intro G htri
  set n : ℕ :=
      (if G.Adj 0 1 then 1 else 0) + 2*(if G.Adj 0 2 then 1 else 0) + 4*(if G.Adj 0 3 then 1 else 0)
    + 8*(if G.Adj 0 4 then 1 else 0) + 16*(if G.Adj 1 2 then 1 else 0) + 32*(if G.Adj 1 3 then 1 else 0)
    + 64*(if G.Adj 1 4 then 1 else 0) + 128*(if G.Adj 2 3 then 1 else 0) + 256*(if G.Adj 2 4 then 1 else 0)
    + 512*(if G.Adj 3 4 then 1 else 0) with hn
  have a01 : (if G.Adj 0 1 then (1:ℕ) else 0) ≤ 1 := by split <;> norm_num
  have a02 : (if G.Adj 0 2 then (1:ℕ) else 0) ≤ 1 := by split <;> norm_num
  have a03 : (if G.Adj 0 3 then (1:ℕ) else 0) ≤ 1 := by split <;> norm_num
  have a04 : (if G.Adj 0 4 then (1:ℕ) else 0) ≤ 1 := by split <;> norm_num
  have a12 : (if G.Adj 1 2 then (1:ℕ) else 0) ≤ 1 := by split <;> norm_num
  have a13 : (if G.Adj 1 3 then (1:ℕ) else 0) ≤ 1 := by split <;> norm_num
  have a14 : (if G.Adj 1 4 then (1:ℕ) else 0) ≤ 1 := by split <;> norm_num
  have a23 : (if G.Adj 2 3 then (1:ℕ) else 0) ≤ 1 := by split <;> norm_num
  have a24 : (if G.Adj 2 4 then (1:ℕ) else 0) ≤ 1 := by split <;> norm_num
  have a34 : (if G.Adj 3 4 then (1:ℕ) else 0) ≤ 1 := by split <;> norm_num
  have hlt : n < 1024 := by rw [hn]; omega
  -- bit lemmas
  have B0 : bN n 0 = decide (G.Adj 0 1) := by
    unfold bN; rw [show (n/2^0)%2 = (if G.Adj 0 1 then 1 else 0) from by rw [hn]; omega]
    by_cases h : G.Adj 0 1 <;> simp [h]
  have B1 : bN n 1 = decide (G.Adj 0 2) := by
    unfold bN; rw [show (n/2^1)%2 = (if G.Adj 0 2 then 1 else 0) from by rw [hn]; omega]
    by_cases h : G.Adj 0 2 <;> simp [h]
  have B2 : bN n 2 = decide (G.Adj 0 3) := by
    unfold bN; rw [show (n/2^2)%2 = (if G.Adj 0 3 then 1 else 0) from by rw [hn]; omega]
    by_cases h : G.Adj 0 3 <;> simp [h]
  have B3 : bN n 3 = decide (G.Adj 0 4) := by
    unfold bN; rw [show (n/2^3)%2 = (if G.Adj 0 4 then 1 else 0) from by rw [hn]; omega]
    by_cases h : G.Adj 0 4 <;> simp [h]
  have B4 : bN n 4 = decide (G.Adj 1 2) := by
    unfold bN; rw [show (n/2^4)%2 = (if G.Adj 1 2 then 1 else 0) from by rw [hn]; omega]
    by_cases h : G.Adj 1 2 <;> simp [h]
  have B5 : bN n 5 = decide (G.Adj 1 3) := by
    unfold bN; rw [show (n/2^5)%2 = (if G.Adj 1 3 then 1 else 0) from by rw [hn]; omega]
    by_cases h : G.Adj 1 3 <;> simp [h]
  have B6 : bN n 6 = decide (G.Adj 1 4) := by
    unfold bN; rw [show (n/2^6)%2 = (if G.Adj 1 4 then 1 else 0) from by rw [hn]; omega]
    by_cases h : G.Adj 1 4 <;> simp [h]
  have B7 : bN n 7 = decide (G.Adj 2 3) := by
    unfold bN; rw [show (n/2^7)%2 = (if G.Adj 2 3 then 1 else 0) from by rw [hn]; omega]
    by_cases h : G.Adj 2 3 <;> simp [h]
  have B8 : bN n 8 = decide (G.Adj 2 4) := by
    unfold bN; rw [show (n/2^8)%2 = (if G.Adj 2 4 then 1 else 0) from by rw [hn]; omega]
    by_cases h : G.Adj 2 4 <;> simp [h]
  have B9 : bN n 9 = decide (G.Adj 3 4) := by
    unfold bN; rw [show (n/2^9)%2 = (if G.Adj 3 4 then 1 else 0) from by rw [hn]; omega]
    by_cases h : G.Adj 3 4 <;> simp [h]
  -- triangle-free transfer
  have notTri : ∀ a b c : Fin 5, G.Adj a b → G.Adj a c → G.Adj b c → False :=
    fun a b c hab hac hbc => htri _ (is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)
  have hh : ∀ a b c : Fin 5,
      (!(decide (G.Adj a b) && decide (G.Adj a c) && decide (G.Adj b c))) = true := by
    intro a b c
    by_cases h1 : G.Adj a b
    · by_cases h2 : G.Adj a c
      · by_cases h3 : G.Adj b c
        · exact (notTri a b c h1 h2 h3).elim
        · simp [h1, h2, h3]
      · simp [h1, h2]
    · simp [h1]
  have htf : triFreeN n = true := by
    rw [triFreeN, List.all_eq_true]
    intro t ht
    fin_cases ht <;> simp only [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9] <;> apply hh
  -- apply core
  obtain ⟨cc, bad, hbad⟩ := hcore ⟨n, hlt⟩ htf
  set L : Set (Fin 5) := {v | bN cc.val v.val = false} with hLdef
  set R : Set (Fin 5) := {v | bN cc.val v.val = true} with hRdef
  have hdisj : Disjoint L R := by
    rw [Set.disjoint_left]
    intro v hv hv'
    rw [hLdef, Set.mem_setOf_eq] at hv
    rw [hRdef, Set.mem_setOf_eq] at hv'
    rw [hv] at hv'; exact Bool.noConfusion hv'
  refine ⟨G.between L R, between_le, between_isBipartite hdisj, ?_⟩
  -- card bound: deleted edges ⊆ {bad edge}, which has card ≤ 1
  set badFs : Finset (Sym2 (Fin 5)) := bad.elim ∅ (fun i => {s(eU i, eV i)}) with hbadFs
  have hcard1 : badFs.card ≤ 1 := by
    rw [hbadFs]; cases bad with
    | none => simp
    | some i => simp
  have keyMem : ∀ u v : Fin 5, G.Adj u v → bN cc.val u.val = bN cc.val v.val →
      s(u, v) ∈ badFs := by
    intro u v hadj hsame
    fin_cases u <;> fin_cases v <;>
      first
        | exact (hadj.ne rfl).elim
        | (have h : bad = some 0 := hbad 0 (by show bN n 0 = true; rw [B0]; first | simpa using hadj | simpa using hadj.symm)
            (by simp only [sameColorAt, edgeU, edgeV]; first | simpa using hsame | simpa using hsame.symm); rw [hbadFs, h]; decide)
        | (have h : bad = some 1 := hbad 1 (by show bN n 1 = true; rw [B1]; first | simpa using hadj | simpa using hadj.symm)
            (by simp only [sameColorAt, edgeU, edgeV]; first | simpa using hsame | simpa using hsame.symm); rw [hbadFs, h]; decide)
        | (have h : bad = some 2 := hbad 2 (by show bN n 2 = true; rw [B2]; first | simpa using hadj | simpa using hadj.symm)
            (by simp only [sameColorAt, edgeU, edgeV]; first | simpa using hsame | simpa using hsame.symm); rw [hbadFs, h]; decide)
        | (have h : bad = some 3 := hbad 3 (by show bN n 3 = true; rw [B3]; first | simpa using hadj | simpa using hadj.symm)
            (by simp only [sameColorAt, edgeU, edgeV]; first | simpa using hsame | simpa using hsame.symm); rw [hbadFs, h]; decide)
        | (have h : bad = some 4 := hbad 4 (by show bN n 4 = true; rw [B4]; first | simpa using hadj | simpa using hadj.symm)
            (by simp only [sameColorAt, edgeU, edgeV]; first | simpa using hsame | simpa using hsame.symm); rw [hbadFs, h]; decide)
        | (have h : bad = some 5 := hbad 5 (by show bN n 5 = true; rw [B5]; first | simpa using hadj | simpa using hadj.symm)
            (by simp only [sameColorAt, edgeU, edgeV]; first | simpa using hsame | simpa using hsame.symm); rw [hbadFs, h]; decide)
        | (have h : bad = some 6 := hbad 6 (by show bN n 6 = true; rw [B6]; first | simpa using hadj | simpa using hadj.symm)
            (by simp only [sameColorAt, edgeU, edgeV]; first | simpa using hsame | simpa using hsame.symm); rw [hbadFs, h]; decide)
        | (have h : bad = some 7 := hbad 7 (by show bN n 7 = true; rw [B7]; first | simpa using hadj | simpa using hadj.symm)
            (by simp only [sameColorAt, edgeU, edgeV]; first | simpa using hsame | simpa using hsame.symm); rw [hbadFs, h]; decide)
        | (have h : bad = some 8 := hbad 8 (by show bN n 8 = true; rw [B8]; first | simpa using hadj | simpa using hadj.symm)
            (by simp only [sameColorAt, edgeU, edgeV]; first | simpa using hsame | simpa using hsame.symm); rw [hbadFs, h]; decide)
        | (have h : bad = some 9 := hbad 9 (by show bN n 9 = true; rw [B9]; first | simpa using hadj | simpa using hadj.symm)
            (by simp only [sameColorAt, edgeU, edgeV]; first | simpa using hsame | simpa using hsame.symm); rw [hbadFs, h]; decide)
  refine le_trans (Finset.card_le_card ?_) hcard1
  intro e he
  revert he
  refine Sym2.inductionOn e (fun u v he => ?_)
  rw [Finset.mem_sdiff] at he
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
  obtain ⟨heG, heH⟩ := he
  have hsame : bN cc.val u.val = bN cc.val v.val := by
    have hcross : ¬ ((u ∈ L ∧ v ∈ R) ∨ (u ∈ R ∧ v ∈ L)) := fun hc =>
      heH (by rw [between_adj]; exact ⟨heG, hc⟩)
    simp only [hLdef, hRdef, Set.mem_setOf_eq, not_or, not_and] at hcross
    obtain ⟨hc1, hc2⟩ := hcross
    cases hu : bN cc.val u.val <;> cases hv : bN cc.val v.val <;> simp_all
  exact keyMem u v heG hsame

/- ===== end n1 helpers ===== -/

/--
Every triangle-free graph on $5$ vertices can be made bipartite by removing at most $1$ edge.
This is the $n = 1$ case of Erdős Problem 23.
-/
@[category test, AMS 5]
theorem erdos_23.variants.n1 :
    ∀ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 5)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
  exact n1_of_core n1_core_strong

-- use propDecidable consistently for `cycleGraph` edge sets in the n1_tight proof below
attribute [-instance] instDecidableRelFinAdjCycleGraph

/--
There exists a triangle-free graph on $5$ vertices such that at least $1$ edge must be removed
to make it bipartite. This shows the bound in `erdos_23_n1` is tight.
-/
@[category test, AMS 5]
theorem erdos_23.variants.n1_tight :
    ∃ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 5)),
        H ≤ G → H.IsBipartite → 1 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  have not_bip : ¬ (cycleGraph 5).IsBipartite := by
    rintro ⟨c⟩
    have e01 : (cycleGraph 5).Adj 0 1 := by rw [cycleGraph_adj']; decide
    have e12 : (cycleGraph 5).Adj 1 2 := by rw [cycleGraph_adj']; decide
    have e23 : (cycleGraph 5).Adj 2 3 := by rw [cycleGraph_adj']; decide
    have e34 : (cycleGraph 5).Adj 3 4 := by rw [cycleGraph_adj']; decide
    have e40 : (cycleGraph 5).Adj 4 0 := by rw [cycleGraph_adj']; decide
    have h01 : (c 0).val ≠ (c 1).val := fun h => c.valid e01 (Fin.ext h)
    have h12 : (c 1).val ≠ (c 2).val := fun h => c.valid e12 (Fin.ext h)
    have h23 : (c 2).val ≠ (c 3).val := fun h => c.valid e23 (Fin.ext h)
    have h34 : (c 3).val ≠ (c 4).val := fun h => c.valid e34 (Fin.ext h)
    have h40 : (c 4).val ≠ (c 0).val := fun h => c.valid e40 (Fin.ext h)
    have b0 := (c 0).isLt; have b1 := (c 1).isLt; have b2 := (c 2).isLt
    have b3 := (c 3).isLt; have b4 := (c 4).isLt
    omega
  refine ⟨cycleGraph 5, ?_, ?_⟩
  · intro t ht
    rw [is3Clique_iff] at ht
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
    rw [cycleGraph_adj'] at hab hac hbc
    fin_cases a <;> fin_cases b <;> fin_cases c <;> revert hab hac hbc <;> decide
  · intro H hHle hHbip
    rcases eq_or_ne H (cycleGraph 5) with rfl | hne
    · exact absurd hHbip not_bip
    · by_contra hcc
      push_neg at hcc
      rw [Nat.lt_one_iff, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hcc
      exact hne (le_antisymm hHle (edgeFinset_subset_edgeFinset.mp hcc))


/--
The blow-up of the 5-cycle $C_5$: replace each vertex of $C_5$ with an independent set of $n$
vertices, and connect two vertices iff their corresponding vertices in $C_5$ are adjacent.
The vertex set is $\mathbb{Z}/5\mathbb{Z} \times \{0, \ldots, n-1\}$, where $(i, a)$ and $(j, b)$
are adjacent iff $j = i + 1$ or $i = j + 1$ in $\mathbb{Z}/5\mathbb{Z}$.
-/
def blowupC5 (n : ℕ) : SimpleGraph (ZMod 5 × Fin n) :=
  SimpleGraph.fromRel fun (i, _) (j, _) => i + 1 = j ∨ j + 1 = i

/- ===== blowupC5_tight certificate helpers (private) ===== -/
private def vtx (n : ℕ) (a : ZMod 5 → Fin n) (i : ZMod 5) : ZMod 5 × Fin n := (i, a i)
private def cycleEdge (n : ℕ) (a : ZMod 5 → Fin n) (i : ZMod 5) : Sym2 (ZMod 5 × Fin n) :=
  s(vtx n a i, vtx n a (i + 1))

private lemma succ_ne (i : ZMod 5) : i ≠ i + 1 := by revert i; decide

-- Milestone 1: each cycle edge is a blowupC5 edge
private lemma cycleEdge_mem (n : ℕ) (a : ZMod 5 → Fin n) (i : ZMod 5) :
    cycleEdge n a i ∈ (blowupC5 n).edgeFinset := by
  rw [cycleEdge, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, blowupC5,
    SimpleGraph.fromRel_adj]
  refine ⟨fun h => ?_, Or.inl (Or.inl rfl)⟩
  rw [vtx, vtx, Prod.ext_iff] at h
  exact succ_ne i h.1

-- Milestone 2+3: bipartite subgraph misses some cycle edge of every tuple
private lemma missing_exists (n : ℕ) (H : SimpleGraph (ZMod 5 × Fin n))
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
private lemma no_caseB (i i' : ZMod 5) (hi1 : i = i' + 1) (hi2 : i + 1 = i') : False := by
  revert hi1 hi2; revert i i'; decide

-- a cycle edge + its 3 free coordinates determine the whole tuple and the position
private lemma cycleEdge_inj (n : ℕ) (a a' : ZMod 5 → Fin n) (i i' : ZMod 5)
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
private theorem blowupC5_tight' (n : ℕ) (hn : 0 < n) (H : SimpleGraph (ZMod 5 × Fin n))
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

/- ===== end blowupC5_tight helpers ===== -/

/--
The blow-up of $C_5$ shows that the bound $n^2$ in Erdős Problem 23 is tight:
any bipartite subgraph must omit at least $n^2$ edges.
-/
@[category test, AMS 5]
theorem blowupC5_tight (n : ℕ) (_hn : 0 < n) (H : SimpleGraph (ZMod 5 × Fin n))
    (hH : H ≤ blowupC5 n) (hBip : H.IsBipartite) :
    n ^ 2 ≤ ((blowupC5 n).edgeFinset \ H.edgeFinset).card := by
  exact blowupC5_tight' n _hn H hBip


/--
Can every triangle-free graph on $5n$ vertices be made bipartite by deleting at most $n^2$ edges?
-/
@[category research open, AMS 5]
theorem erdos_23 : answer(sorry) ↔
    ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        ∃ (H : SimpleGraph V),
          H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ n^2 := by
  sorry

-- TODO: add the remaining variants/statements/comments

end Erdos23

#print axioms Erdos23.erdos_23.variants.n1_tight
#print axioms Erdos23.erdos_23.variants.n1
#print axioms Erdos23.blowupC5_tight
