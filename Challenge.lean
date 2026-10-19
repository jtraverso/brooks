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

Version 2 adds degree-choosability and a library of blocks:

* `DegreeChoosability.degree_choosable_iff` and `DegreeChoosability.degree_choosable_iff_blocks`:
  **Erdős–Rubin–Taylor (1979), Borodin (1977).** A finite connected graph is degree-choosable
  (from any lists with `|L v| ≥ deg v`, colours in `ℕ`) if and only if it is not a Gallai tree,
  i.e. some block is neither complete nor an odd cycle (equivalently, some vertex set with at least
  three vertices induces a 2-connected subgraph that is neither complete nor an odd cycle).
* `DegreeChoosability.list_brooks`: **Brooks' theorem for lists (Vizing 1976).** A connected graph
  that is neither complete nor an odd cycle is colourable from any lists of at least `Δ(G)`
  colours.
* `BlockStructure.*`: blocks (`GraphBlocks.IsBlock`, maximal vertex sets inducing a connected
  subgraph without a cut vertex): every edge lies in exactly one block, two blocks share at most
  one vertex, every nonseparable set lies in a block, cut vertices (`GraphBlocks.IsCutVertex`) are
  exactly the vertices in two blocks, the block–cut graph (`GraphBlocks.blockCutGraph`) of a
  connected graph is a tree, and the block and induced-subgraph descriptions of Gallai trees agree.
  The definitions are stated below verbatim, with the same names as in the library.
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

/-! ### Blocks (version 2): definitions, verbatim from `ChoosabilityLib/Blocks.lean` -/

open Finset

namespace GraphBlocks

variable {V : Type*} (G : SimpleGraph V)

/-- `S` is nonseparable: `G[S]` is connected and, if `S` has at least three vertices, removing any
single vertex of `S` leaves `G[S]` connected. -/
def IsNonseparable (S : Set V) : Prop :=
  (G.induce S).Connected ∧ ∀ x ∈ S, 3 ≤ S.ncard → (G.induce (S \ {x})).Connected

/-- A block of `G`: a maximal nonseparable vertex set. -/
def IsBlock (S : Set V) : Prop :=
  IsNonseparable G S ∧ ∀ T : Set V, S ⊆ T → IsNonseparable G T → T = S

/-- `v` is a cut vertex: two vertices other than `v` are joined by a walk of `G` but not by a walk
avoiding `v`. -/
def IsCutVertex (v : V) : Prop :=
  ∃ a b : ↥({v}ᶜ : Set V), G.Reachable a b ∧ ¬ (G.induce ({v}ᶜ : Set V)).Reachable a b

/-- The block–cut graph: its vertices are the blocks and the cut vertices of `G`, and a block is
adjacent to the cut vertices it contains. -/
def blockCutGraph : SimpleGraph ({B : Set V // IsBlock G B} ⊕ {v : V // IsCutVertex G v}) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | Sum.inl B, Sum.inr v => v.1 ∈ B.1
    | _, _ => False

end GraphBlocks

/-! ### Block structure (version 2) -/

namespace BlockStructure

open GraphBlocks

variable {V : Type*} (G : SimpleGraph V)

/-- Every edge lies in exactly one block. -/
theorem exists_unique_block_of_adj [Finite V] {u v : V} (h : G.Adj u v) :
    ∃! B : Set V, IsBlock G B ∧ u ∈ B ∧ v ∈ B := by
  sorry

/-- Two distinct blocks share at most one vertex. -/
theorem inter_subsingleton [Finite V] {B B' : Set V} (hB : IsBlock G B) (hB' : IsBlock G B')
    (hne : B ≠ B') : (B ∩ B').Subsingleton := by
  sorry

/-- Every nonseparable vertex set is contained in a block. -/
theorem exists_isBlock_superset [Finite V] {S : Set V} (hS : IsNonseparable G S) :
    ∃ B : Set V, IsBlock G B ∧ S ⊆ B := by
  sorry

/-- A vertex is a cut vertex if and only if it lies in two distinct blocks. -/
theorem isCutVertex_iff [Finite V] (v : V) :
    IsCutVertex G v ↔ ∃ B B' : Set V, IsBlock G B ∧ IsBlock G B' ∧ B ≠ B' ∧ v ∈ B ∧ v ∈ B' := by
  sorry

/-- The block–cut graph of a finite connected graph is a tree. -/
theorem blockCutGraph_isTree [Finite V] (hconn : G.Connected) : (blockCutGraph G).IsTree := by
  sorry

/-- Every block is complete or an odd cycle if and only if every vertex set with at least three
vertices that induces a 2-connected subgraph induces a complete graph or an odd cycle. -/
theorem gallai_iff [Finite V] :
    (∀ B : Set V, IsBlock G B →
        (∀ x ∈ B, ∀ y ∈ B, x ≠ y → G.Adj x y) ∨
          ∃ n, Odd n ∧ Nonempty (G.induce B ≃g cycleGraph n)) ↔
      ¬ ∃ S : Set V, 3 ≤ S.ncard ∧ (∀ x ∈ S, (G.induce (S \ {x})).Connected) ∧
        ¬ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) ∧
        ∀ n, Odd n → IsEmpty (G.induce S ≃g cycleGraph n) := by
  sorry

end BlockStructure

/-! ### Degree-choosability and Brooks' theorem for lists (version 2) -/

namespace DegreeChoosability

open GraphBlocks

variable {V : Type*} [Fintype V]

/-- **Erdős–Rubin–Taylor (1979), Borodin (1977).** A finite connected graph is degree-choosable if
and only if some vertex set `S` with at least three vertices induces a 2-connected subgraph which
is neither complete nor an odd cycle (that is, the graph is not a Gallai tree). -/
theorem degree_choosable_iff (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) :
    (∀ L : V → Finset ℕ, (∀ v, G.degree v ≤ (L v).card) →
        ∃ f : V → ℕ, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v) ↔
      ∃ S : Set V, 3 ≤ S.ncard ∧ (∀ x ∈ S, (G.induce (S \ {x})).Connected) ∧
        ¬ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) ∧
        ∀ n, Odd n → IsEmpty (G.induce S ≃g cycleGraph n) := by
  sorry

/-- **Erdős–Rubin–Taylor (1979), Borodin (1977), block form.** A finite connected graph is
degree-choosable if and only if some block of it is neither complete nor an odd cycle. -/
theorem degree_choosable_iff_blocks (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    (∀ L : V → Finset ℕ, (∀ v, G.degree v ≤ (L v).card) →
        ∃ f : V → ℕ, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v) ↔
      ∃ B : Set V, IsBlock G B ∧ ¬ (∀ x ∈ B, ∀ y ∈ B, x ≠ y → G.Adj x y) ∧
        ∀ n, Odd n → IsEmpty (G.induce B ≃g cycleGraph n) := by
  sorry

/-- **Brooks' theorem for lists (Vizing 1976; Erdős–Rubin–Taylor 1979).** A finite connected graph
that is neither complete nor an odd cycle can be properly coloured from any lists of at least
`Δ(G)` colours. -/
theorem list_brooks {Color : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hK : G ≠ ⊤) (hC : ∀ n, Odd n → IsEmpty (G ≃g cycleGraph n))
    (L : V → Finset Color) (hL : ∀ v, G.maxDegree ≤ (L v).card) :
    ∃ f : V → Color, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v := by
  sorry

end DegreeChoosability
