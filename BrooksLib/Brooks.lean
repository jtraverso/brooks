/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import BrooksLib.BrooksLow

/-!
# Brooks' theorem

For finite simple graphs:

* `BrooksTheorem.colorable_of_cliqueFree`: if `k ≥ 3`, the maximum degree is at most `k` and there
  is no clique on `k + 1` vertices, then the graph is `k`-colourable (no connectedness needed).
* `BrooksTheorem.brooks`: **Brooks (1941).** A connected graph that is neither complete nor an odd
  cycle is `Δ`-colourable, where `Δ` is its maximum degree.

An odd cycle is a graph isomorphic to Mathlib's `cycleGraph n` for an odd `n`.
-/

@[expose] public section

open SimpleGraph

namespace BrooksTheorem

variable {V : Type*}

/-- **Brooks' theorem, clique form.** For `k ≥ 3`, a finite graph of maximum degree at most `k`
without a `(k + 1)`-clique is `k`-colourable. -/
theorem colorable_of_cliqueFree [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hk : 3 ≤ k) (hΔ : G.maxDegree ≤ k) (hK : G.CliqueFree (k + 1)) : G.Colorable k := by
  classical
  have hnb : ∀ v, Aux.nb G v = G.neighborFinset v := by intro v; ext u; simp [Aux.nb]
  obtain ⟨f, hf⟩ := Aux.exists_proper k hk G
    (fun v => by rw [hnb, card_neighborFinset_eq_degree]; exact (G.degree_le_maxDegree v).trans hΔ)
    hK
  exact ⟨Coloring.mk f (fun h => hf _ _ h)⟩

/-- **Brooks' theorem (1941).** A finite connected graph that is neither complete nor an odd
cycle can be coloured with as many colours as its maximum degree. -/
theorem brooks [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hK : G ≠ ⊤) (hC : ∀ n, Odd n → IsEmpty (G ≃g cycleGraph n)) :
    G.Colorable G.maxDegree := by
  classical
  have hnb : ∀ v, Aux.nb G v = G.neighborFinset v := by intro v; ext u; simp [Aux.nb]
  have hdeg : ∀ v, (Aux.nb G v).card ≤ G.maxDegree := fun v => by
    rw [hnb, card_neighborFinset_eq_degree]; exact G.degree_le_maxDegree v
  have := hconn.nonempty
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hvd : (Aux.nb G v).card = G.maxDegree := by
    rw [hnb, card_neighborFinset_eq_degree, hv]
  rcases le_or_gt 3 G.maxDegree with h3 | h3
  · exact colorable_of_cliqueFree G _ h3 le_rfl
      (fun K hKc => hK (Aux.top_of_clique G hconn hdeg K hKc))
  · by_cases hdef : ∃ v0, (Aux.nb G v0).card < G.maxDegree
    · obtain ⟨f, hf⟩ := Aux.greedy_connected G hconn _ hdeg hdef
      exact ⟨Coloring.mk f (fun h => hf _ _ h)⟩
    · push Not at hdef
      rcases le_or_gt G.maxDegree 1 with h1 | h1
      · exact absurd (Aux.top_of_low G hconn h1 hdeg v hvd) hK
      · have h2 : G.maxDegree = 2 := by omega
        rw [h2]
        exact Aux.two_regular_colorable G hconn
          (fun w => h2 ▸ le_antisymm (hdeg w) (hdef w)) hC

end BrooksTheorem
