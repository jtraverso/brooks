# Brooks' theorem, degree-choosability and blocks in Lean 4

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

**Version 2** adds list colouring and a library of blocks:

3. **Erdős–Rubin–Taylor (1979), Borodin (1977).** A connected graph is *degree-choosable*
   (colourable from any lists with `|L(v)| ≥ deg(v)`) if and only if it is not a *Gallai tree*,
   i.e. some block is neither complete nor an odd cycle
   (`DegreeChoosability.degree_choosable_iff_blocks`); equivalently, some vertex set with at least
   three vertices induces a 2-connected subgraph that is neither complete nor an odd cycle
   (`DegreeChoosability.degree_choosable_iff`).
4. **Brooks' theorem for lists (Vizing 1976).** A connected graph that is neither complete nor an
   odd cycle is colourable from any lists of at least `Δ` colours (`DegreeChoosability.list_brooks`).
5. **Blocks** (`BlockStructure.*`). A block (`GraphBlocks.IsBlock`) is a maximal vertex set
   inducing a connected subgraph without a cut vertex (so bridges and isolated vertices are
   blocks). Every edge lies in exactly one block; two blocks share at most one vertex; every
   nonseparable set lies in a block; cut vertices (`GraphBlocks.IsCutVertex`) are exactly the
   vertices lying in two blocks; the block–cut graph (`GraphBlocks.blockCutGraph`) of a connected
   graph is a tree; and the block and induced-subgraph descriptions of Gallai trees agree. Mathlib
   has no blocks; the definitions are stated in `Challenge.lean` verbatim, with the same names as
   in the library. `comparator.json` selects only the theorems; the definitions are not selected
   separately and enter the check only as part of the theorem statements that use them.

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean), `BrooksLib/` and (version 2) `ChoosabilityLib/`: the proofs.
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
* **Degree-choosability** (version 2, `ChoosabilityLib/ERT*.lean`).
  - Slack and extension lemmas: a connected graph is colourable if some vertex has more colours
    than neighbours, and a colouring of an induced connected subgraph extends greedily.
  - Not a Gallai tree ⇒ degree-choosable: in a 2-connected witness set `S`, either some vertex has
    slack, or two adjacent vertices have different lists (fix a colour and use the slack lemma),
    or all lists coincide, so `G[S]` is regular and the version-1 Brooks theorem applies.
  - Gallai tree ⇒ bad lists, by induction splitting at a cut vertex (cliques get `|S| − 1` colours,
    odd cycles two, and the two sides are combined with disjoint palettes).
  - Brooks for lists: either some vertex has degree below `Δ`, or `G` is regular, and a connected
    regular Gallai tree is complete or an odd cycle.
* **Blocks** (version 2, `ChoosabilityLib/Blocks.lean`): a union lemma (nonseparable sets sharing
  two vertices have a nonseparable union) and an ear lemma (adding a path between two vertices of a
  nonseparable set keeps it nonseparable) give uniqueness of blocks per edge, the intersection
  property and the characterization of cut vertices; the block–cut graph is connected and each of
  its edges is a bridge.

## Sources

* R. L. Brooks, *On colouring the nodes of a network*, Proc. Cambridge Philos. Soc. 37 (1941)
  194–197, doi:10.1017/S030500410002168X.
* L. Lovász, *Three short proofs in graph theory*, J. Combin. Theory Ser. B 19 (1975) 269–271,
  doi:10.1016/0095-8956(75)90089-1.
* P. Erdős, A. L. Rubin, H. Taylor, *Choosability in graphs*, Congr. Numer. 26 (1979) 125–157.
* O. V. Borodin, *Criteria of chromaticity of a degree prescription* (in Russian), Abstracts of
  the IV All-Union Conference on Theoretical Cybernetics, Novosibirsk (1977) 127–128.
* V. G. Vizing, *Vertex colorings with given colors* (in Russian), Metody Diskret. Analiz. 29
  (1976) 3–10.
* A. V. Kostochka, M. Stiebitz, B. Wirth, *The colour theorems of Brooks and Gallai extended*,
  Discrete Math. 162 (1996) 299–303, doi:10.1016/0012-365X(95)00294-7.
* R. Diestel, *Graph Theory*, 5th ed., GTM 173, Springer (2017), doi:10.1007/978-3-662-53622-3
  (blocks, Section 3.1).

## Authorship and use of AI

The author chose the results (and proposed building the block library). The statements and proof
plans were written with Claude in Claude Code. Harmonic's Aristotle produced the proofs (one run for
version 1, two runs for version 2), which were audited and rebuilt locally. Lean
checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
