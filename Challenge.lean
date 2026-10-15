/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Brooks' theorem

For finite simple graphs:

* `BrooksColouring.colorable_of_cliqueFree`: if `k ≥ 3`, the maximum degree is at most `k` and there
  is no clique on `k + 1` vertices, then the graph is `k`-colourable (no connectedness needed).
* `BrooksColouring.brooks`: **Brooks (1941).** A connected graph that is neither complete nor an odd
  cycle is `Δ`-colourable, where `Δ` is its maximum degree.

An odd cycle is a graph isomorphic to Mathlib's `cycleGraph n` for an odd `n`.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

open SimpleGraph

namespace BrooksColouring

variable {V : Type*}

/-- **Brooks' theorem, clique form.** For `k ≥ 3`, a finite graph of maximum degree at most `k`
without a `(k + 1)`-clique is `k`-colourable. -/
theorem colorable_of_cliqueFree [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hk : 3 ≤ k) (hΔ : G.maxDegree ≤ k) (hK : G.CliqueFree (k + 1)) : G.Colorable k := by
  sorry

/-- **Brooks' theorem (1941).** A finite connected graph that is neither complete nor an odd
cycle can be coloured with as many colours as its maximum degree. -/
theorem brooks [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hK : G ≠ ⊤) (hC : ∀ n, Odd n → IsEmpty (G ≃g cycleGraph n)) :
    G.Colorable G.maxDegree := by
  sorry

end BrooksColouring
