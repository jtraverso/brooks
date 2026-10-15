/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import BrooksLib.BrooksCore
public import BrooksLib.Cycle

/-!
# Auxiliary results for the connected form of Brooks' theorem

* a connected graph containing a clique of size `Δ + 1` (with `Δ` a degree bound) is complete;
* greedy colouring of a connected graph with a vertex of degree `< k`;
* colouring of connected `2`-regular graphs that are not odd cycles.
-/

@[expose] public section

open SimpleGraph Finset

namespace BrooksTheorem
namespace Aux

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- In a connected graph, a set containing a vertex and closed under adjacency is everything. -/
lemma mem_of_closed (G : SimpleGraph V) (hconn : G.Connected) (C : Set V) {v0 : V}
    (hv0 : v0 ∈ C) (hC : ∀ u ∈ C, ∀ w, G.Adj u w → w ∈ C) (w : V) : w ∈ C := by
  have key : ∀ {a b : V} (p : G.Walk a b), a ∈ C → b ∈ C := by
    intro a b p
    induction p with
    | nil => exact id
    | cons h _ ihp => exact fun ha => ihp (hC _ ha _ h)
  exact key (hconn.preconnected v0 w).some hv0

/-- A connected graph with all degrees at most `d` containing a `(d + 1)`-clique is complete. -/
lemma top_of_clique (G : SimpleGraph V) (hconn : G.Connected) {d : ℕ}
    (hdeg : ∀ v, (nb G v).card ≤ d) (K : Finset V) (hK : G.IsNClique (d + 1) K) : G = ⊤ := by
  classical
  rw [isNClique_iff] at hK
  obtain ⟨hKc, hKcard⟩ := hK
  have hnbK : ∀ v ∈ K, nb G v = K.erase v := by
    intro v hv
    symm
    apply eq_of_subset_of_card_le
    · intro u hu
      rw [mem_erase] at hu
      exact mem_nb.2 (hKc hv hu.2 hu.1.symm)
    · rw [card_erase_of_mem hv, hKcard]
      exact hdeg v
  obtain ⟨v0, hv0⟩ : K.Nonempty := by rw [← card_pos, hKcard]; omega
  have hall : ∀ w, w ∈ (K : Set V) := by
    refine mem_of_closed G hconn (K : Set V) hv0 ?_
    intro u hu w huw
    have : w ∈ nb G u := mem_nb.2 huw
    rw [hnbK u hu] at this
    exact (mem_erase.1 this).2
  ext u w
  simp only [top_adj]
  constructor
  · exact G.ne_of_adj
  · intro huw
    exact hKc (hall u) (hall w) huw

/-- A connected graph with all degrees at most `d ≤ 1` and a vertex of degree `d` is complete. -/
lemma top_of_low (G : SimpleGraph V) (hconn : G.Connected) {d : ℕ} (hd : d ≤ 1)
    (hdeg : ∀ v, (nb G v).card ≤ d) (v : V) (hv : (nb G v).card = d) : G = ⊤ := by
  classical
  refine top_of_clique G hconn hdeg (insert v (nb G v)) ?_
  rw [isNClique_iff]
  refine ⟨?_, ?_⟩
  · rw [coe_insert, isClique_insert]
    refine ⟨fun a ha b hb hab => ?_, fun b hb _ => mem_nb.1 hb⟩
    exact absurd (card_le_one.1 (hv ▸ hd) a ha b hb) hab
  · rw [card_insert_of_notMem (by simp), hv]

/-- Greedy colouring of a connected graph having a vertex of degree less than `k`. -/
lemma greedy_connected (G : SimpleGraph V) (hconn : G.Connected) (k : ℕ)
    (hdeg : ∀ v, (nb G v).card ≤ k) (hdef : ∃ v0, (nb G v0).card < k) :
    ∃ f : V → Fin k, Proper G f := by
  classical
  obtain ⟨v0, hv0⟩ := hdef
  have hk : 0 < k := by omega
  have key : ∀ {a b : V} (p : G.Walk a b), (nb G b).card < k →
      near G ∅ (fun w => (nb G w).card < k) p.length a := by
    intro a b p
    induction p with
    | nil => exact id
    | cons h _ ihp => exact fun hb => ⟨_, h, by simp, ihp hb⟩
  obtain ⟨g, -, hg⟩ := greedy_reach G k hdeg ∅ (fun _ => ⟨0, hk⟩) (by simp)
    (fun w => (nb G w).card < k) (fun w _ hw => by simpa using hw)
    (fun w _ => ⟨_, key (hconn.preconnected w v0).some hv0⟩)
  exact ⟨g, hg⟩

/-- A connected graph with all degrees equal to two which is not an odd cycle is
`2`-colourable. -/
lemma two_regular_colorable (G : SimpleGraph V) (hconn : G.Connected)
    (h2 : ∀ v, (nb G v).card = 2) (hC : ∀ n, Odd n → IsEmpty (G ≃g cycleGraph n)) :
    G.Colorable 2 := by
  obtain ⟨n, e, he⟩ := exists_cycle_equiv G hconn h2
  obtain ⟨φ⟩ := cycle_iso G h2 n e he
  rcases Nat.even_or_odd (n + 3) with hev | hodd
  · exact (IsBipartite.cycleGraph_of_even hev).of_hom φ.toEmbedding.toHom
  · exact ((hC _ hodd).false φ).elim

end Aux
end BrooksTheorem
