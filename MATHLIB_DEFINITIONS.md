# Mathlib definitions used in Challenge.lean (Brooks' theorem)

Verbatim excerpts of the Mathlib definitions used by the statements in `Challenge.lean`, at the
pinned Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`, repository
https://github.com/leanprover-community/mathlib4). Mathlib is released under the Apache-2.0
licence. Each excerpt gives the file and line at that revision; the complete source is at
`https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/<file>`.

These excerpts are provided so that the meaning of every imported notion used by the
Challenge can be audited without fetching Mathlib.

## SimpleGraph

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 95:

```lean
/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
@[ext, aesop safe constructors (rule_sets := [SimpleGraph]), wikidata Q141488]
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph
```

## Top graph (complete graph)

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 338:

```lean
@[simp]
theorem top_adj (v w : V) : (⊤ : SimpleGraph V).Adj v w ↔ v ≠ w :=
  Iff.rfl
```

## Graph homomorphisms `G →g H`

`Mathlib/Combinatorics/SimpleGraph/Maps.lean`, line 293:

```lean
/-- A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms. -/
abbrev Hom :=
  RelHom G.Adj G'.Adj
```

## SimpleGraph.Coloring

`Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`, line 74:

```lean
/-- An `α`-coloring of a simple graph `G` is a homomorphism of `G` into the complete graph on `α`.
This is also known as a proper coloring.
-/
abbrev Coloring (α : Type v) := G →g completeGraph α
```

## SimpleGraph.Colorable

`Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`, line 163:

```lean
/-- Whether a graph can be colored by at most `n` colors. -/
def Colorable (n : ℕ) : Prop := Nonempty (G.Coloring (Fin n))
```

## SimpleGraph.Connected

`Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`, line 314:

```lean
/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.

There is a `CoeFun` instance so that `h u v` can be used instead of `h.Preconnected u v`. -/
@[mk_iff]
structure Connected : Prop where
  protected preconnected : G.Preconnected
  protected [nonempty : Nonempty V]
```

## SimpleGraph.Preconnected

`Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`, line 228:

```lean
/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def Preconnected : Prop := ∀ u v : V, G.Reachable u v
```

## SimpleGraph.Reachable

`Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`, line 52:

```lean
/-- Two vertices are *reachable* if there is a walk between them.
This is equivalent to `Relation.ReflTransGen` of `G.Adj`.
See `SimpleGraph.reachable_iff_reflTransGen`. -/
def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)
```

## SimpleGraph.Walk

`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`, line 54:

```lean
/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `SimpleGraph.Walk.support`.

See `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive Walk : V → V → Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq
```

## SimpleGraph.neighborFinset

`Mathlib/Combinatorics/SimpleGraph/Finite.lean`, line 169:

```lean
/-- `G.neighborFinset v` is the `Finset` version of `G.neighborSet v` in case `G` is
locally finite at `v`. -/
def neighborFinset : Finset V :=
  (G.neighborSet v).toFinset
```

## SimpleGraph.degree

`Mathlib/Combinatorics/SimpleGraph/Finite.lean`, line 242:

```lean
/-- `G.degree v` is the number of vertices adjacent to `v`. -/
def degree : ℕ := #(G.neighborFinset v)
```

## SimpleGraph.maxDegree

`Mathlib/Combinatorics/SimpleGraph/Finite.lean`, line 496:

```lean
/-- The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_maxDegree`
and `maxDegree_le_of_forall_degree_le`. -/
def maxDegree [DecidableRel G.Adj] : ℕ :=
  WithBot.unbotD 0 (univ.image fun v => G.degree v).max
```

## SimpleGraph.IsClique

`Mathlib/Combinatorics/SimpleGraph/Clique.lean`, line 48:

```lean
/-- A clique in a graph is a set of vertices that are pairwise adjacent. -/
abbrev IsClique (s : Set α) : Prop :=
  s.Pairwise G.Adj
```

## SimpleGraph.IsNClique

`Mathlib/Combinatorics/SimpleGraph/Clique.lean`, line 246:

```lean
/-- An `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
structure IsNClique (n : ℕ) (s : Finset α) : Prop where
  isClique : G.IsClique s
  card_eq : #s = n
```

## SimpleGraph.CliqueFree

`Mathlib/Combinatorics/SimpleGraph/Clique.lean`, line 379:

```lean
/-- `G.CliqueFree n` means that `G` has no `n`-cliques. -/
def CliqueFree (n : ℕ) : Prop :=
  ∀ t, ¬G.IsNClique n t
```

## SimpleGraph.cycleGraph

`Mathlib/Combinatorics/SimpleGraph/CycleGraph.lean`, line 29:

```lean
/-- Cycle graph over `Fin n` -/
def cycleGraph : (n : ℕ) → SimpleGraph (Fin n)
  | 0 | 1 => ⊥
  | _ + 2 => {
    Adj a b := a - b = 1 ∨ b - a = 1
  }
```

## SimpleGraph.Iso (`G ≃g H`)

`Mathlib/Combinatorics/SimpleGraph/Maps.lean`, line 307:

```lean
/-- A graph isomorphism is a bijective map on vertex sets that respects adjacency relations.

The notation `G ≃g G'` represents the type of graph isomorphisms.
-/
abbrev Iso :=
  RelIso G.Adj G'.Adj
```

## Fintype.card

`Mathlib/Data/Fintype/Card.lean`, line 40:

```lean
/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [Fintype α] : ℕ :=
  (@univ α _).card
```
