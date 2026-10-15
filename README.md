# Brooks' theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

This repository formalizes Brooks' theorem for finite simple graphs in two forms:

1. **Clique form.** If `k ≥ 3`, the maximum degree is at most `k`, and there is no clique on
   `k + 1` vertices, then the graph is `k`-colourable (`BrooksColouring.colorable_of_cliqueFree`).
   The graph need not be connected.
2. **Brooks (1941).** A connected graph that is neither complete nor an odd cycle is
   `Δ`-colourable, where `Δ` is its maximum degree (`BrooksColouring.brooks`).

"Odd cycle" means a graph isomorphic to Mathlib's `cycleGraph n` with `n` odd. The second form
also covers maximum degree at most 2. The clique form generalizes the author's subcubic version
(`k = 3`) in Lean Pool (`BrooksSubcubic`).

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean) and `BrooksLib/`: the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proof goes

* **Greedy colouring** (`Greedy.lean`). Colour the vertices in decreasing order of a rank, where
  every vertex has fewer than `k` earlier-coloured neighbours. One variant starts from a
  precoloured pair. Another colours along paths towards a terminal vertex where a colour is
  guaranteed to be free.
* **Clique form** (`BrooksCore.lean`). The proof is by strong induction on the number of edges.
  1. If no vertex has degree `k`, colour greedily.
  2. Otherwise take `y` of degree `k`. Since there is no `(k+1)`-clique, `y` has two
     non-adjacent neighbours `x` and `z`. Give `x` and `z` the same colour and colour greedily
     towards `y` (Lovász's argument).
  3. If some vertices cannot be reached this way, `{x, z}`, or a single vertex, separates the
     graph. Colour both sides by induction, adding the edge `xz` on each side when needed, then
     permute the colours and glue.
* **Classical form** (`BrooksLow.lean`, `Cycle.lean`).
  - If `Δ ≥ 3`: a connected graph with a `(Δ+1)`-clique is complete, so the clique form applies.
  - If `Δ ≤ 2`: a connected graph with `Δ ≤ 1` is complete. If some vertex has degree less than
    `Δ`, colour greedily. A connected 2-regular graph is a cycle: an even cycle is 2-coloured,
    and an odd cycle is excluded by hypothesis.

## Sources

* R. L. Brooks, *On colouring the nodes of a network*, Proc. Cambridge Philos. Soc. 37 (1941)
  194–197, doi:10.1017/S030500410002168X.
* L. Lovász, *Three short proofs in graph theory*, J. Combin. Theory Ser. B 19 (1975) 269–271,
  doi:10.1016/0095-8956(75)90089-1.

## Authorship and use of AI

The author chose the result. The statements and proof plan were written with Claude in Claude
Code. Harmonic's Aristotle produced the proofs, which were audited and rebuilt locally. Lean
checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
