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

set_option maxRecDepth 10000
open SimpleGraph Finset

def bN (n i : ℕ) : Bool := (n / 2 ^ i) % 2 == 1
def trisN : List (ℕ × ℕ × ℕ) :=
  [(0,1,4),(0,2,5),(0,3,6),(1,2,7),(1,3,8),(2,3,9),(4,5,7),(4,6,8),(5,6,9),(7,8,9)]
def triFreeN (n : ℕ) : Bool := trisN.all (fun t => !(bN n t.1 && bN n t.2.1 && bN n t.2.2))
def edgeU : Fin 10 → ℕ := ![0,0,0,0,1,1,1,2,2,3]
def edgeV : Fin 10 → ℕ := ![1,2,3,4,2,3,4,3,4,4]
def sameColorAt (c : ℕ) (i : Fin 10) : Bool := bN c (edgeU i) == bN c (edgeV i)
-- Fin 5 endpoints
def eU : Fin 10 → Fin 5 := ![0,0,0,0,1,1,1,2,2,3]
def eV : Fin 10 → Fin 5 := ![1,2,3,4,2,3,4,3,4,4]
set_option maxHeartbeats 4000000

theorem n1_core_strong : ∀ n : Fin 1024, triFreeN n.val = true →
    ∃ c : Fin 32, ∃ bad : Option (Fin 10), ∀ i : Fin 10,
      bN n.val i.val = true → sameColorAt c.val i = true → bad = some i := by decide

theorem n1_of_core
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


/--
Every triangle-free graph on $5$ vertices can be made bipartite by removing at most $1$ edge.
This is the $n = 1$ case of Erdős Problem 23.
-/
@[category test, AMS 5]
theorem erdos_23.variants.n1 :
    ∀ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 5)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
  exact n1_of_core n1_core_strong

end Erdos23

#print axioms Erdos23.erdos_23.variants.n1
