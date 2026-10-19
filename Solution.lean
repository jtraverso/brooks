/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import BrooksLib.Brooks
public import ChoosabilityLib.Blocks

/-!
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `BrooksLib/` (namespace `BrooksTheorem`): a greedy colouring lemma
(`Greedy.lean`), the clique form by strong induction on the number of edges with a two-vertex
separation-and-gluing step (`BrooksCore.lean`), and the classical form, reducing maximum degree at
least 3 to the clique form and treating maximum degree at most 2 directly (`BrooksLow.lean`,
`Cycle.lean`).

The version-2 results are proved in `ChoosabilityLib/` (namespaces `ErdosRubinTaylor` and
`GraphBlocks`), on top of `BrooksLib/`; the block definitions are the library's own and are
reproduced verbatim in `Challenge.lean`.
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

/-! ### Block structure (version 2) -/

namespace BlockStructure

open GraphBlocks

variable {V : Type*} (G : SimpleGraph V)

/-- Every edge lies in exactly one block. -/
theorem exists_unique_block_of_adj [Finite V] {u v : V} (h : G.Adj u v) :
    ∃! B : Set V, IsBlock G B ∧ u ∈ B ∧ v ∈ B :=
  GraphBlocks.exists_unique_block_of_adj G h

/-- Two distinct blocks share at most one vertex. -/
theorem inter_subsingleton [Finite V] {B B' : Set V} (hB : IsBlock G B) (hB' : IsBlock G B')
    (hne : B ≠ B') : (B ∩ B').Subsingleton :=
  GraphBlocks.inter_subsingleton G hB hB' hne

/-- Every nonseparable vertex set is contained in a block. -/
theorem exists_isBlock_superset [Finite V] {S : Set V} (hS : IsNonseparable G S) :
    ∃ B : Set V, IsBlock G B ∧ S ⊆ B :=
  GraphBlocks.exists_isBlock_superset G hS

/-- A vertex is a cut vertex if and only if it lies in two distinct blocks. -/
theorem isCutVertex_iff [Finite V] (v : V) :
    IsCutVertex G v ↔ ∃ B B' : Set V, IsBlock G B ∧ IsBlock G B' ∧ B ≠ B' ∧ v ∈ B ∧ v ∈ B' :=
  GraphBlocks.isCutVertex_iff G v

/-- The block–cut graph of a finite connected graph is a tree. -/
theorem blockCutGraph_isTree [Finite V] (hconn : G.Connected) : (blockCutGraph G).IsTree :=
  GraphBlocks.blockCutGraph_isTree G hconn

/-- Every block is complete or an odd cycle if and only if every vertex set with at least three
vertices that induces a 2-connected subgraph induces a complete graph or an odd cycle. -/
theorem gallai_iff [Finite V] :
    (∀ B : Set V, IsBlock G B →
        (∀ x ∈ B, ∀ y ∈ B, x ≠ y → G.Adj x y) ∨
          ∃ n, Odd n ∧ Nonempty (G.induce B ≃g cycleGraph n)) ↔
      ¬ ∃ S : Set V, 3 ≤ S.ncard ∧ (∀ x ∈ S, (G.induce (S \ {x})).Connected) ∧
        ¬ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) ∧
        ∀ n, Odd n → IsEmpty (G.induce S ≃g cycleGraph n) :=
  GraphBlocks.gallai_iff G

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
        ∀ n, Odd n → IsEmpty (G.induce S ≃g cycleGraph n) :=
  ErdosRubinTaylor.degree_choosable_iff G hconn

/-- **Erdős–Rubin–Taylor (1979), Borodin (1977), block form.** A finite connected graph is
degree-choosable if and only if some block of it is neither complete nor an odd cycle. -/
theorem degree_choosable_iff_blocks (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    (∀ L : V → Finset ℕ, (∀ v, G.degree v ≤ (L v).card) →
        ∃ f : V → ℕ, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v) ↔
      ∃ B : Set V, IsBlock G B ∧ ¬ (∀ x ∈ B, ∀ y ∈ B, x ≠ y → G.Adj x y) ∧
        ∀ n, Odd n → IsEmpty (G.induce B ≃g cycleGraph n) :=
  GraphBlocks.degree_choosable_iff_blocks G hconn

/-- **Brooks' theorem for lists (Vizing 1976; Erdős–Rubin–Taylor 1979).** A finite connected graph
that is neither complete nor an odd cycle can be properly coloured from any lists of at least
`Δ(G)` colours. -/
theorem list_brooks {Color : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hK : G ≠ ⊤) (hC : ∀ n, Odd n → IsEmpty (G ≃g cycleGraph n))
    (L : V → Finset Color) (hL : ∀ v, G.maxDegree ≤ (L v).card) :
    ∃ f : V → Color, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v :=
  ErdosRubinTaylor.list_brooks G hconn hK hC L hL

end DegreeChoosability
