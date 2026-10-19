/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import ChoosabilityLib.ERTChoosable
public import ChoosabilityLib.ERTGallai

/-!
# Degree-choosability: the Erdős–Rubin–Taylor theorem and Brooks' theorem for lists

A finite graph `G` is *degree-choosable* if, whenever every vertex `v` receives a list of at least
`deg v` colours, `G` has a proper colouring choosing the colour of every vertex from its list. A
*Gallai tree* is a connected graph each of whose blocks is a complete graph or an odd cycle;
equivalently, every vertex set `S` with `|S| ≥ 3` that induces a 2-connected subgraph (`G[S − x]`
connected for every `x ∈ S`) induces a complete graph or an odd cycle.

* `ErdosRubinTaylor.degree_choosable_iff`: **Erdős–Rubin–Taylor (1979), Borodin (1977).** A finite
  connected graph is degree-choosable (with colours in `ℕ`) if and only if it is not a Gallai tree,
  i.e. some vertex set `S` with `|S| ≥ 3` induces a 2-connected subgraph that is neither complete
  nor an odd cycle.
* `ErdosRubinTaylor.list_brooks`: **Brooks' theorem for lists (Vizing 1976; Erdős–Rubin–Taylor
  1979).** A finite connected graph that is neither complete nor an odd cycle has a proper
  colouring from any lists of at least `Δ(G)` colours.
-/

@[expose] public section

open Finset SimpleGraph

namespace ErdosRubinTaylor

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- If no vertex set witnesses that `G` is not a Gallai tree, then `G` is a Gallai set. -/
lemma gallai_univ_of_not (G : SimpleGraph V)
    (h : ¬ ∃ S : Set V, 3 ≤ S.ncard ∧ (∀ x ∈ S, (G.induce (S \ {x})).Connected) ∧
        ¬ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) ∧
        ∀ n, Odd n → IsEmpty (G.induce S ≃g cycleGraph n)) : Gallai G Set.univ := by
  intro S _ h3 h2
  by_cases hK : IsCliqueOn G S
  · exact Or.inl hK
  · right
    by_contra hC
    push Not at hC
    exact h ⟨S, h3, h2, hK, hC⟩

/-- **Erdős–Rubin–Taylor (1979), Borodin (1977).** A finite connected graph is degree-choosable if
and only if some vertex set `S` with at least three vertices induces a 2-connected subgraph which
is neither complete nor an odd cycle (that is, the graph is not a Gallai tree). -/
theorem degree_choosable_iff (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) :
    (∀ L : V → Finset ℕ, (∀ v, G.degree v ≤ (L v).card) →
        ∃ f : V → ℕ, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v) ↔
      ∃ S : Set V, 3 ≤ S.ncard ∧ (∀ x ∈ S, (G.induce (S \ {x})).Connected) ∧
        ¬ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) ∧
        ∀ n, Odd n → IsEmpty (G.induce S ≃g cycleGraph n) := by
  constructor
  · intro hDC
    by_contra hno
    obtain ⟨L, hL, hbad⟩ :=
      bad_lists G _ Set.univ rfl (sconn_univ hconn) (gallai_univ_of_not G hno)
    obtain ⟨f, hf1, hf2⟩ := hDC L (fun v => by rw [← dIn_univ]; exact hL v trivial)
    exact hbad ⟨f, fun v _ => hf1 v, fun u _ v _ h => hf2 u v h⟩
  · rintro ⟨S, h3, h2, hK, hC⟩ L hL
    exact choosable_of_not_gallai G hconn S h3 h2 hK hC L hL

/-- **Brooks' theorem for lists (Vizing 1976; Erdős–Rubin–Taylor 1979).** A finite connected graph
that is neither complete nor an odd cycle can be properly coloured from any lists of at least
`Δ(G)` colours. -/
theorem list_brooks {Color : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hK : G ≠ ⊤) (hC : ∀ n, Odd n → IsEmpty (G ≃g cycleGraph n))
    (L : V → Finset Color) (hL : ∀ v, G.maxDegree ≤ (L v).card) :
    ∃ f : V → Color, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v := by
  classical
  obtain ⟨v0⟩ := hconn.nonempty
  have hdeg : ∀ v, G.degree v ≤ (L v).card := fun v => (G.degree_le_maxDegree v).trans (hL v)
  have hCne : Nonempty Color := by
    by_contra hCe
    rw [not_nonempty_iff] at hCe
    have h0 : ∀ v, (BrooksTheorem.Aux.nb G v).card ≤ 0 := by
      intro v
      have hLv : (L v).card = 0 := by simp [Finset.eq_empty_of_isEmpty (L v)]
      have hnb : BrooksTheorem.Aux.nb G v = G.neighborFinset v := by
        ext u; simp [BrooksTheorem.Aux.nb]
      rw [hnb, card_neighborFinset_eq_degree]
      have := hdeg v
      omega
    exact hK (BrooksTheorem.Aux.top_of_low G hconn zero_le_one h0 v0 (Nat.le_zero.1 (h0 v0)))
  by_cases hdef : ∃ w, G.degree w < G.maxDegree
  · obtain ⟨w, hw⟩ := hdef
    obtain ⟨f, hf1, hf2⟩ := slack_colour G Set.univ (sconn_univ hconn) (Set.mem_univ w) L
      (fun v _ => by rw [dIn_univ]; exact hdeg v)
      (by rw [dIn_univ]; exact lt_of_lt_of_le hw (hL w))
    exact ⟨f, fun v => hf1 v trivial, fun u v h => hf2 u trivial v trivial h⟩
  · push Not at hdef
    have hreg : ∀ v, G.degree v = G.maxDegree :=
      fun v => le_antisymm (G.degree_le_maxDegree v) (hdef v)
    have hNG : ∃ S : Set V, 3 ≤ S.ncard ∧ (∀ x ∈ S, (G.induce (S \ {x})).Connected) ∧
        ¬ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) ∧
        ∀ n, Odd n → IsEmpty (G.induce S ≃g cycleGraph n) := by
      by_contra hno
      rcases regular_gallai_block G G.maxDegree _ Set.univ v0 rfl (sconn_univ hconn)
          (gallai_univ_of_not G hno) (fun v _ => by rw [dIn_univ, hreg])
          (fun v _ _ => by rw [dIn_univ, hreg]) with hcl | ⟨m, hm, ⟨e⟩⟩
      · apply hK
        ext u w
        simp only [top_adj]
        exact ⟨G.ne_of_adj, fun h => hcl u trivial w trivial h⟩
      · exact (hC m hm).false ((G.induceUnivIso).symm.trans e)
    obtain ⟨S, h3, h2, hK', hC'⟩ := hNG
    exact choosable_of_not_gallai G hconn S h3 h2 hK' hC' L hdeg

end ErdosRubinTaylor
