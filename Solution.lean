/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import BrooksLib.Brooks

/-!
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `BrooksLib/` (namespace `BrooksTheorem`): a greedy colouring lemma
(`Greedy.lean`), the clique form by strong induction on the number of edges with a two-vertex
separation-and-gluing step (`BrooksCore.lean`), and the classical form, reducing maximum degree at
least 3 to the clique form and treating maximum degree at most 2 directly (`BrooksLow.lean`,
`Cycle.lean`).
-/

@[expose] public section

open SimpleGraph

namespace BrooksColouring

variable {V : Type*}

/-- **Brooks' theorem, clique form.** For `k ≥ 3`, a finite graph of maximum degree at most `k`
without a `(k + 1)`-clique is `k`-colourable. -/
theorem colorable_of_cliqueFree [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hk : 3 ≤ k) (hΔ : G.maxDegree ≤ k) (hK : G.CliqueFree (k + 1)) : G.Colorable k :=
  BrooksTheorem.colorable_of_cliqueFree G k hk hΔ hK

/-- **Brooks' theorem (1941).** A finite connected graph that is neither complete nor an odd
cycle can be coloured with as many colours as its maximum degree. -/
theorem brooks [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hK : G ≠ ⊤) (hC : ∀ n, Odd n → IsEmpty (G ≃g cycleGraph n)) :
    G.Colorable G.maxDegree :=
  BrooksTheorem.brooks G hconn hK hC

end BrooksColouring
