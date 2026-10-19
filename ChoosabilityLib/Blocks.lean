/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import ChoosabilityLib.ErdosRubinTaylor

/-!
# Blocks of a graph, the block–cut tree, and Gallai trees

A vertex set `S` of a simple graph `G` is *nonseparable* if `G[S]` is connected and has no cut
vertex (when `|S| ≥ 3`, `G[S − x]` is connected for every `x ∈ S`). A *block* is a maximal
nonseparable vertex set: a maximal 2-connected subgraph, a bridge (`K₂`) or an isolated vertex.
A *cut vertex* is a vertex `v` such that two vertices other than `v` are joined by a walk of `G`
but not by a walk of `G − v`.

* `GraphBlocks.exists_unique_block_of_adj`: every edge lies in exactly one block.
* `GraphBlocks.inter_subsingleton`: two distinct blocks share at most one vertex.
* `GraphBlocks.exists_isBlock_superset`: every nonseparable set lies in a block.
* `GraphBlocks.isCutVertex_iff`: a vertex is a cut vertex if and only if it lies in two distinct
  blocks.
* `GraphBlocks.blockCutGraph_isTree`: the block–cut graph of a finite connected graph (blocks and
  cut vertices, a block adjacent to the cut vertices it contains) is a tree.
* `GraphBlocks.gallai_iff`: every block is complete or an odd cycle (a *Gallai tree*, for connected
  `G`) if and only if every vertex set `S` with `|S| ≥ 3` inducing a 2-connected subgraph induces a
  complete graph or an odd cycle.
* `GraphBlocks.degree_choosable_iff_blocks`: **Erdős–Rubin–Taylor (1979), Borodin (1977), block
  form.** A finite connected graph is degree-choosable if and only if some block is neither
  complete nor an odd cycle.
-/

@[expose] public section

open Finset SimpleGraph

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


/-! ### Auxiliary lemmas -/

open ErdosRubinTaylor

section aux

variable {G}

lemma sconn_union {S T : Set V} (hS : SConn G S) (hT : SConn G T) (h : (S ∩ T).Nonempty) :
    SConn G (S ∪ T) := by
  obtain ⟨z, hzS, hzT⟩ := h
  refine sconn_of_hub (Or.inl hzS) fun v hv => ?_
  rcases hv with hv | hv
  · exact rtg_mono Set.subset_union_left (hS.rtg hzS hv)
  · exact rtg_mono Set.subset_union_right (hT.rtg hzT hv)

lemma sconn_singleton (a : V) : SConn G {a} :=
  sconn_of_hub rfl fun v hv => by rw [Set.mem_singleton_iff.1 hv]

lemma sconn_pair {a b : V} (h : G.Adj a b) : SConn G {a, b} :=
  sconn_of_hub (Set.mem_insert a _) fun v hv => by
    rcases hv with rfl | rfl
    · exact .refl
    · exact .single ⟨Set.mem_insert _ _, Set.mem_insert_of_mem _ rfl, h⟩

lemma rtg_reachable {U : Set V} {a b : V} (h : Relation.ReflTransGen (adjIn G U) a b) :
    G.Reachable a b := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans hbc.2.2.reachable

lemma induce_reachable_iff {T : Set V} (x y : T) :
    (G.induce T).Reachable x y ↔ Relation.ReflTransGen (adjIn G T) x.1 y.1 := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact .refl
    | cons h _ ih => exact .head ⟨Subtype.prop _, Subtype.prop _, h⟩ ih
  · intro h
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    have key : ∀ a b, Relation.ReflTransGen (adjIn G T) a b → ∀ (ha : a ∈ T) (hb : b ∈ T),
        (G.induce T).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
      intro a b hab
      induction hab with
      | refl => intro _ _; exact Reachable.refl _
      | tail _ hbc ih =>
        intro ha _
        exact (ih ha hbc.1).trans (Adj.reachable hbc.2.2)
    exact key x y h hx hy

lemma exists_walk_of_rtg {U : Set V} {a b : V} (h : Relation.ReflTransGen (adjIn G U) a b)
    (ha : a ∈ U) : ∃ p : G.Walk a b, ∀ z ∈ p.support, z ∈ U := by
  induction h with
  | refl =>
    exact ⟨.nil, fun z hz => by rw [Walk.support_nil, List.mem_singleton] at hz; exact hz ▸ ha⟩
  | tail _ hbc ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.concat hbc.2.2, fun z hz => ?_⟩
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hp z hz
    · exact hbc.2.1

lemma rtg_of_walk {U : Set V} {a b : V} (p : G.Walk a b) (hU : ∀ z ∈ p.support, z ∈ U) :
    ∀ y ∈ p.support, Relation.ReflTransGen (adjIn G U) y b := by
  induction p with
  | nil => intro y hy; rw [Walk.support_nil, List.mem_singleton] at hy; subst hy; exact .refl
  | cons h p ih =>
    intro y hy
    have hU' : ∀ z ∈ p.support, z ∈ U := fun z hz => hU z (by simp [hz])
    rw [Walk.support_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact .head ⟨hU _ (by simp), hU' _ p.start_mem_support, h⟩ (ih hU' _ p.start_mem_support)
    · exact ih hU' y hy

/-- Removing a vertex `x` from a path leaves every remaining vertex joined to one of the two
endpoints. -/
lemma path_reach {U : Set V} (x : V) {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hU : ∀ z ∈ p.support, z ≠ x → z ∈ U) :
    ∀ y ∈ p.support, y ≠ x → Relation.ReflTransGen (adjIn G U) y a ∨
      Relation.ReflTransGen (adjIn G U) y b := by
  induction p with
  | nil =>
    intro y hy _
    rw [Walk.support_nil, List.mem_singleton] at hy
    subst hy
    exact Or.inl .refl
  | @cons a c b h p ih =>
    intro y hy hyx
    rw [Walk.cons_isPath_iff] at hp
    have hU' : ∀ z ∈ p.support, z ≠ x → z ∈ U := fun z hz => hU z (by simp [hz])
    rw [Walk.support_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact Or.inl .refl
    · rcases ih hp.1 hU' y hy hyx with h1 | h1
      · by_cases hax : a = x
        · subst hax
          right
          exact rtg_of_walk p (fun z hz => hU' z hz (fun h => hp.2 (h ▸ hz))) y hy
        · left
          have hcU : c ∈ U := rtg_mem h1 (hU' y hy hyx)
          exact h1.tail ⟨hcU, hU a (by simp) hax, h.symm⟩
      · exact Or.inr h1

lemma three_le_ncard_of_mem [Finite V] {S : Set V} {x y z : V} (hx : x ∈ S) (hy : y ∈ S)
    (hz : z ∈ S) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : 3 ≤ S.ncard := by
  have hsub : ({x, y, z} : Set V) ⊆ S := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem (by simp [hxy, hxz]), Set.ncard_pair hyz] at this
  exact this

lemma two_le_ncard_of_mem [Finite V] {S : Set V} {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : x ≠ y) : 2 ≤ S.ncard := by
  have hsub : ({x, y} : Set V) ⊆ S := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl <;> assumption
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_pair hxy] at this

lemma isNonseparable_iff {S : Set V} : IsNonseparable G S ↔
    SConn G S ∧ ∀ x ∈ S, 3 ≤ S.ncard → SConn G (S \ {x}) := by
  simp only [IsNonseparable, connected_iff_sconn]

lemma IsNonseparable.sconn {S : Set V} (hS : IsNonseparable G S) : SConn G S :=
  (isNonseparable_iff.1 hS).1

/-- Removing a vertex from a nonseparable set leaves a connected set (unless nothing is left). -/
lemma IsNonseparable.sconn_diff [Finite V] {S : Set V} (hS : IsNonseparable G S) (x : V)
    (hne : (S \ {x}).Nonempty) : SConn G (S \ {x}) := by
  rw [isNonseparable_iff] at hS
  by_cases hx : x ∈ S
  · by_cases h3 : 3 ≤ S.ncard
    · exact hS.2 x hx h3
    · obtain ⟨a, ha⟩ := hne
      have h1 : (S \ {x}).ncard ≤ 1 := by
        rw [Set.ncard_sdiff_singleton_of_mem hx]; omega
      rcases (Set.ncard_le_one_iff_eq (Set.toFinite _)).1 h1 with h | ⟨b, hb⟩
      · rw [h] at ha; exact absurd ha (Set.notMem_empty a)
      · rw [hb]; exact sconn_singleton b
  · rw [Set.sdiff_singleton_eq_self hx]; exact hS.1

lemma isNonseparable_singleton (a : V) : IsNonseparable G {a} := by
  rw [isNonseparable_iff]
  refine ⟨sconn_singleton a, fun x _ h => ?_⟩
  simp at h

lemma isNonseparable_pair {a b : V} (h : G.Adj a b) : IsNonseparable G {a, b} := by
  rw [isNonseparable_iff]
  refine ⟨sconn_pair h, fun x _ h3 => ?_⟩
  have := Set.ncard_insert_le a {b}
  rw [Set.ncard_singleton] at this
  omega

/-- **Union lemma.** Two nonseparable sets sharing at least two vertices have a nonseparable
union. -/
lemma IsNonseparable.union [Finite V] {S T : Set V} (hS : IsNonseparable G S)
    (hT : IsNonseparable G T) (h2 : 2 ≤ (S ∩ T).ncard) : IsNonseparable G (S ∪ T) := by
  have hST : ∀ x, ((S ∩ T) \ {x}).Nonempty := fun x => by
    apply Set.nonempty_of_ncard_ne_zero
    have := Set.le_ncard_sdiff {x} (S ∩ T)
    rw [Set.ncard_singleton] at this
    omega
  rw [isNonseparable_iff]
  refine ⟨sconn_union hS.sconn hT.sconn ?_, fun x _ _ => ?_⟩
  · exact Set.nonempty_of_ncard_ne_zero (by omega)
  · obtain ⟨z, ⟨hzS, hzT⟩, hzx⟩ := hST x
    rw [Set.union_sdiff_distrib]
    exact sconn_union (hS.sconn_diff x ⟨z, hzS, hzx⟩) (hT.sconn_diff x ⟨z, hzT, hzx⟩)
      ⟨z, ⟨hzS, hzx⟩, hzT, hzx⟩

/-- **Ear lemma.** Adding a path between two distinct vertices of a nonseparable set keeps it
nonseparable. -/
lemma IsNonseparable.union_path [Finite V] {S : Set V} (hS : IsNonseparable G S) {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (p : G.Walk a b) (hp : p.IsPath) :
    IsNonseparable G (S ∪ {z | z ∈ p.support}) := by
  have hdiff : ∀ x, SConn G ((S ∪ {z | z ∈ p.support}) \ {x}) := by
    intro x
    have hne : (S \ {x}).Nonempty := by
      by_cases hax : a = x
      · exact ⟨b, hb, fun h => hab (hax.trans h.symm)⟩
      · exact ⟨a, ha, hax⟩
    obtain ⟨z, hz⟩ := hne
    have hSx := hS.sconn_diff x ⟨z, hz⟩
    have hsub : S \ {x} ⊆ (S ∪ {z | z ∈ p.support}) \ {x} :=
      Set.sdiff_subset_sdiff_left Set.subset_union_left
    refine sconn_of_hub (hsub hz) fun v hv => ?_
    rcases hv.1 with hvS | hvp
    · exact rtg_mono hsub (hSx.rtg hz ⟨hvS, hv.2⟩)
    · have hU : ∀ w ∈ p.support, w ≠ x → w ∈ (S ∪ {z | z ∈ p.support}) \ {x} :=
        fun w hw hwx => ⟨Or.inr hw, hwx⟩
      have hend : ∀ e ∈ S, Relation.ReflTransGen
          (adjIn G ((S ∪ {z | z ∈ p.support}) \ {x})) v e →
          Relation.ReflTransGen (adjIn G ((S ∪ {z | z ∈ p.support}) \ {x})) z v := by
        intro e he hve
        have heU := rtg_mem hve hv
        exact (rtg_mono hsub (hSx.rtg hz ⟨he, heU.2⟩)).trans (rtg_symm hve)
      rcases path_reach x p hp hU v hvp hv.2 with h1 | h1
      · exact hend a ha h1
      · exact hend b hb h1
  rw [isNonseparable_iff]
  refine ⟨sconn_of_hub (Or.inl ha) fun v hv => ?_, fun x _ _ => hdiff x⟩
  rcases hv with hvS | hvp
  · exact rtg_mono Set.subset_union_left (hS.sconn.rtg ha hvS)
  · exact (rtg_mono Set.subset_union_left (hS.sconn.rtg ha hb)).trans
      (rtg_symm (rtg_of_walk p (fun w hw => Or.inr hw) v hvp))

lemma exists_block_aux [Finite V] {S : Set V} (hS : IsNonseparable G S) :
    ∃ B : Set V, IsBlock G B ∧ S ⊆ B := by
  obtain ⟨B, hB⟩ := (Set.toFinite {T : Set V | S ⊆ T ∧ IsNonseparable G T}).exists_maximal
    ⟨S, subset_rfl, hS⟩
  exact ⟨B, ⟨hB.prop.2, fun T hBT hT => hB.eq_of_ge ⟨hB.prop.1.trans hBT, hT⟩ hBT⟩, hB.prop.1⟩

lemma IsBlock.eq_of_two_le_inter [Finite V] {B B' : Set V} (hB : IsBlock G B)
    (hB' : IsBlock G B') (h2 : 2 ≤ (B ∩ B').ncard) : B = B' := by
  have hU := hB.1.union hB'.1 h2
  exact (hB.2 _ Set.subset_union_left hU).symm.trans (hB'.2 _ Set.subset_union_right hU)

lemma IsBlock.eq_of_mem_of_mem [Finite V] {B B' : Set V} (hB : IsBlock G B)
    (hB' : IsBlock G B') {x y : V} (hx : x ∈ B) (hx' : x ∈ B') (hy : y ∈ B) (hy' : y ∈ B')
    (hxy : x ≠ y) : B = B' :=
  hB.eq_of_two_le_inter hB' (two_le_ncard_of_mem ⟨hx, hx'⟩ ⟨hy, hy'⟩ hxy)

/-- A block containing `v` and different from another block containing `v` has another
vertex. -/
lemma IsBlock.exists_ne {B B' : Set V} (hB : IsBlock G B) (hB' : IsBlock G B') (hne : B ≠ B')
    {v : V} (hv' : v ∈ B') : ∃ a ∈ B, a ≠ v := by
  by_contra h
  push Not at h
  exact hne (hB.2 B' (fun a ha => h a ha ▸ hv') hB'.1).symm

lemma exists_adj_of_sconn {S : Set V} (hS : SConn G S) {v a : V} (hv : v ∈ S) (ha : a ∈ S)
    (hav : a ≠ v) : ∃ c ∈ S, G.Adj v c := by
  rcases (hS.rtg hv ha).cases_head with h | ⟨c, hc, -⟩
  · exact absurd h hav.symm
  · exact ⟨c, hc.2.1, hc.2.2⟩

/-- A path whose endpoints are distinct vertices of a block lies in the block. -/
lemma IsBlock.support_subset [Finite V] {B : Set V} (hB : IsBlock G B) {a b : V} (ha : a ∈ B)
    (hb : b ∈ B) (hab : a ≠ b) (p : G.Walk a b) (hp : p.IsPath) : ∀ z ∈ p.support, z ∈ B := by
  have := hB.2 _ Set.subset_union_left (hB.1.union_path ha hb hab p hp)
  intro z hz
  rw [← this]
  exact Or.inr hz

/-- If `v` lies in two distinct blocks `B`, `B'`, then vertices of `B − v` and of `B' − v` are not
joined by a walk avoiding `v`. -/
lemma not_rtg_of_blocks [Finite V] {B B' : Set V} (hB : IsBlock G B) (hB' : IsBlock G B')
    (hne : B ≠ B') {v a b : V} (hvB : v ∈ B) (hvB' : v ∈ B') (haB : a ∈ B) (hav : a ≠ v)
    (hbB' : b ∈ B') (hbv : b ≠ v) : ¬ Relation.ReflTransGen (adjIn G {v}ᶜ) a b := by
  classical
  intro h
  obtain ⟨c, hcB, hvc⟩ := exists_adj_of_sconn hB.1.sconn hvB haB hav
  have hcv : c ≠ v := (G.ne_of_adj hvc).symm
  have hBv := hB.1.sconn_diff v ⟨a, haB, hav⟩
  have hca : Relation.ReflTransGen (adjIn G {v}ᶜ) c a :=
    rtg_mono (fun x hx => hx.2) (hBv.rtg ⟨hcB, hcv⟩ ⟨haB, hav⟩)
  obtain ⟨p, hp⟩ := exists_walk_of_rtg (hca.trans h) hcv
  have hq : (Walk.cons hvc p.bypass).IsPath := by
    rw [Walk.cons_isPath_iff]
    exact ⟨p.bypass_isPath, fun hm => hp v (p.support_bypass_subset_support hm) rfl⟩
  have hcB' := hB'.support_subset hvB' hbB' hbv.symm _ hq c (by simp)
  exact hcv (by_contra fun h' => hne (hB.eq_of_mem_of_mem hB' hcB hcB' hvB hvB' h'))

lemma edge_out {S B : Set V} (hB : SConn G B) {s0 y0 : V} (hs0 : s0 ∈ S) (hSB : S ⊆ B)
    (hy0 : y0 ∈ B) (hy0S : y0 ∉ S) : ∃ s ∈ S, ∃ y ∈ B, y ∉ S ∧ G.Adj s y := by
  by_contra hno
  push Not at hno
  have hcl : ∀ u ∈ S, ∀ v ∈ B, G.Adj u v → v ∈ S := fun u hu v hv huv =>
    by_contra fun h => hno u hu v hv h huv
  exact hy0S (rtg_closed hcl (hB.rtg (hSB hs0) hy0) hs0).2

lemma two_nbrs [Finite V] {S : Set V} (hS : IsNonseparable G S) (h3 : 3 ≤ S.ncard) {s : V}
    (hs : s ∈ S) : ∃ u ∈ S, ∃ u' ∈ S, u ≠ u' ∧ G.Adj s u ∧ G.Adj s u' := by
  obtain ⟨w, hw, hws, -⟩ := exists_third h3 s s
  obtain ⟨u, huS, hsu⟩ := exists_adj_of_sconn hS.sconn hs hw hws
  obtain ⟨w', hw', hw's, hw'u⟩ := exists_third h3 s u
  have hSu := (isNonseparable_iff.1 hS).2 u huS h3
  obtain ⟨u', hu', hsu'⟩ := exists_adj_of_sconn hSu ⟨hs, (G.ne_of_adj hsu)⟩ ⟨hw', hw'u⟩ hw's
  exact ⟨u, huS, u', hu'.1, fun h => hu'.2 h.symm, hsu, hsu'⟩

/-- A nonseparable set with at least three vertices inside a connected set inducing an odd cycle
is the whole cycle. -/
lemma eq_of_subset_cycle [Finite V] {S B : Set V} (hS : IsNonseparable G S) (h3 : 3 ≤ S.ncard)
    (hSB : S ⊆ B) (hB : SConn G B) {n : ℕ} (hn : Odd n) (e : G.induce B ≃g cycleGraph n) :
    S = B := by
  classical
  have := Fintype.ofFinite V
  by_contra hne
  obtain ⟨y0, hy0, hy0S⟩ : ∃ y ∈ B, y ∉ S := by
    by_contra h
    push Not at h
    exact hne (Set.Subset.antisymm hSB h)
  obtain ⟨s0, hs0⟩ := Set.nonempty_of_ncard_ne_zero (s := S) (by omega)
  obtain ⟨s, hs, y, hyB, hyS, hsy⟩ := edge_out hB hs0 hSB hy0 hy0S
  obtain ⟨u, hu, u', hu', huu', hsu, hsu'⟩ := two_nbrs hS h3 hs
  have h2 : 2 ≤ B.ncard := le_trans (by omega) (Set.ncard_le_ncard hSB (Set.toFinite _))
  have hd := dIn_cycle e hn h2 (hSB hs)
  rw [dIn_eq] at hd
  have : 2 < (univ.filter (fun w => w ∈ B ∧ G.Adj s w)).card := by
    rw [Finset.two_lt_card]
    refine ⟨u, by simp [hSB hu, hsu], u', by simp [hSB hu', hsu'], y, by simp [hyB, hsy],
      huu', fun h => hyS (h ▸ hu), fun h => hyS (h ▸ hu')⟩
  omega

variable (G) in
lemma witness_iff [Finite V] :
    (∃ S : Set V, 3 ≤ S.ncard ∧ (∀ x ∈ S, (G.induce (S \ {x})).Connected) ∧
        ¬ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) ∧
        ∀ n, Odd n → IsEmpty (G.induce S ≃g cycleGraph n)) ↔
      ∃ B : Set V, IsBlock G B ∧ ¬ (∀ x ∈ B, ∀ y ∈ B, x ≠ y → G.Adj x y) ∧
        ∀ n, Odd n → IsEmpty (G.induce B ≃g cycleGraph n) := by
  constructor
  · rintro ⟨S, h3, h2, hK, hC⟩
    have h2' : ∀ x ∈ S, SConn G (S \ {x}) := fun x hx => connected_iff_sconn.1 (h2 x hx)
    have hS : IsNonseparable G S :=
      isNonseparable_iff.2 ⟨sconn_of_two_conn h3 h2', fun x hx _ => h2' x hx⟩
    obtain ⟨B, hB, hSB⟩ := exists_block_aux hS
    refine ⟨B, hB, fun hK' => hK fun x hx y hy => hK' x (hSB hx) y (hSB hy),
      fun n hn => ⟨fun e => ?_⟩⟩
    have hSeq := eq_of_subset_cycle hS h3 hSB hB.1.sconn hn e
    rw [← hSeq] at e
    exact (hC n hn).false e
  · rintro ⟨B, hB, hK, hC⟩
    have h3 : 3 ≤ B.ncard := three_le_of_not_clique hB.1.sconn hK
    exact ⟨B, h3, fun x hx => hB.1.2 x hx h3, hK, hC⟩

end aux

/-- Every edge lies in exactly one block. -/
theorem exists_unique_block_of_adj [Finite V] {u v : V} (h : G.Adj u v) :
    ∃! B : Set V, IsBlock G B ∧ u ∈ B ∧ v ∈ B := by
  obtain ⟨B, hB, hsub⟩ := exists_block_aux (isNonseparable_pair h)
  refine ⟨B, ⟨hB, hsub (Set.mem_insert _ _), hsub (Set.mem_insert_of_mem _ rfl)⟩, ?_⟩
  rintro B' ⟨hB', hu, hv⟩
  exact hB'.eq_of_mem_of_mem hB hu (hsub (Set.mem_insert _ _)) hv
    (hsub (Set.mem_insert_of_mem _ rfl)) (G.ne_of_adj h)

/-- Two distinct blocks share at most one vertex. -/
theorem inter_subsingleton [Finite V] {B B' : Set V} (hB : IsBlock G B) (hB' : IsBlock G B')
    (hne : B ≠ B') : (B ∩ B').Subsingleton := by
  rintro x ⟨hx, hx'⟩ y ⟨hy, hy'⟩
  by_contra hxy
  exact hne (hB.eq_of_mem_of_mem hB' hx hx' hy hy' hxy)

/-- Every nonseparable vertex set is contained in a block. -/
theorem exists_isBlock_superset [Finite V] {S : Set V} (hS : IsNonseparable G S) :
    ∃ B : Set V, IsBlock G B ∧ S ⊆ B := by
  exact exists_block_aux hS

/-- A vertex is a cut vertex if and only if it lies in two distinct blocks. -/
theorem isCutVertex_iff [Finite V] (v : V) :
    IsCutVertex G v ↔ ∃ B B' : Set V, IsBlock G B ∧ IsBlock G B' ∧ B ≠ B' ∧ v ∈ B ∧ v ∈ B' := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, hnr⟩
    by_contra hno
    push Not at hno
    have hone : ∀ B B' : Set V, IsBlock G B → IsBlock G B' → v ∈ B → v ∈ B' → B = B' :=
      fun B B' hB hB' hvB hvB' => by_contra fun h => hno B B' hB hB' h hvB hvB'
    have hN : ∀ n m, G.Adj v n → G.Adj v m → Relation.ReflTransGen (adjIn G {v}ᶜ) n m := by
      intro n m hn hm
      obtain ⟨Bn, hBn, hsn⟩ := exists_block_aux (isNonseparable_pair hn)
      obtain ⟨Bm, hBm, hsm⟩ := exists_block_aux (isNonseparable_pair hm)
      have hvn : v ∈ Bn := hsn (Set.mem_insert _ _)
      have hnB : n ∈ Bn := hsn (Set.mem_insert_of_mem _ rfl)
      have hmB : m ∈ Bn := by
        rw [hone Bn Bm hBn hBm hvn (hsm (Set.mem_insert _ _))]
        exact hsm (Set.mem_insert_of_mem _ rfl)
      by_cases hnm : n = m
      · subst hnm; exact .refl
      · have h3 := three_le_ncard_of_mem hvn hnB hmB (G.ne_of_adj hn) (G.ne_of_adj hm) hnm
        exact rtg_mono (fun x hx => hx.2) (((isNonseparable_iff.1 hBn.1).2 v hvn h3).rtg
          ⟨hnB, (G.ne_of_adj hn).symm⟩ ⟨hmB, (G.ne_of_adj hm).symm⟩)
    have key : ∀ x y (p : G.Walk x y), y ≠ v →
        (x ≠ v → Relation.ReflTransGen (adjIn G {v}ᶜ) x y) ∧
        (x = v → ∀ n, G.Adj v n → Relation.ReflTransGen (adjIn G {v}ᶜ) n y) := by
      intro x y p
      induction p with
      | nil => exact fun hy => ⟨fun _ => .refl, fun hx => absurd hx hy⟩
      | @cons x c y h p ih =>
        intro hy
        obtain ⟨ih1, ih2⟩ := ih hy
        refine ⟨fun hx => ?_, fun hx n hn => ?_⟩
        · by_cases hc : c = v
          · subst hc; exact ih2 rfl x h.symm
          · exact .head ⟨hx, hc, h⟩ (ih1 hc)
        · subst hx
          exact (hN n c hn h).trans (ih1 (G.ne_of_adj h).symm)
    obtain ⟨p⟩ := hab
    exact hnr ((induce_reachable_iff _ _).2 ((key a b p hb).1 ha))
  · rintro ⟨B, B', hB, hB', hne, hvB, hvB'⟩
    obtain ⟨a, haB, hav⟩ := hB.exists_ne hB' hne hvB'
    obtain ⟨b, hbB', hbv⟩ := hB'.exists_ne hB (Ne.symm hne) hvB
    refine ⟨⟨a, hav⟩, ⟨b, hbv⟩, ?_, fun h => ?_⟩
    · exact (rtg_reachable (hB.1.sconn.rtg haB hvB)).trans
        (rtg_reachable (hB'.1.sconn.rtg hvB' hbB'))
    · exact not_rtg_of_blocks hB hB' hne hvB hvB' haB hav hbB' hbv
        ((induce_reachable_iff _ _).1 h)

section blockCut

/-! ### The block–cut graph -/

lemma blockCutGraph_adj_inl_inr (B : {B : Set V // IsBlock G B})
    (c : {v : V // IsCutVertex G v}) :
    (blockCutGraph G).Adj (Sum.inl B) (Sum.inr c) ↔ c.1 ∈ B.1 := by
  simp [blockCutGraph, fromRel_adj]

lemma blockCutGraph_not_adj_inl_inl (B B' : {B : Set V // IsBlock G B}) :
    ¬ (blockCutGraph G).Adj (Sum.inl B) (Sum.inl B') := by
  simp [blockCutGraph, fromRel_adj]

lemma blockCutGraph_not_adj_inr_inr (c c' : {v : V // IsCutVertex G v}) :
    ¬ (blockCutGraph G).Adj (Sum.inr c) (Sum.inr c') := by
  simp [blockCutGraph, fromRel_adj]

lemma blockCutGraph_reachable_of_mem [Finite V] (B B' : {B : Set V // IsBlock G B}) {x : V}
    (hx : x ∈ B.1) (hx' : x ∈ B'.1) :
    (blockCutGraph G).Reachable (Sum.inl B) (Sum.inl B') := by
  by_cases h : B = B'
  · rw [h]
  · have hc : IsCutVertex G x :=
      (isCutVertex_iff G x).2 ⟨B.1, B'.1, B.2, B'.2, fun e => h (Subtype.ext e), hx, hx'⟩
    exact ((blockCutGraph_adj_inl_inr G B ⟨x, hc⟩).2 hx).reachable.trans
      ((blockCutGraph_adj_inl_inr G B' ⟨x, hc⟩).2 hx').symm.reachable

lemma blockCutGraph_reachable_of_walk [Finite V] {x y : V} (p : G.Walk x y) :
    ∀ B B' : {B : Set V // IsBlock G B}, x ∈ B.1 → y ∈ B'.1 →
      (blockCutGraph G).Reachable (Sum.inl B) (Sum.inl B') := by
  induction p with
  | nil => intro B B' hx hy; exact blockCutGraph_reachable_of_mem G B B' hx hy
  | @cons x c y h p ih =>
    intro B B' hx hy
    obtain ⟨D, hD, hsub⟩ := exists_block_aux (isNonseparable_pair h)
    exact (blockCutGraph_reachable_of_mem G B ⟨D, hD⟩ hx (hsub (Set.mem_insert _ _))).trans
      (ih ⟨D, hD⟩ B' (hsub (Set.mem_insert_of_mem _ rfl)) hy)

lemma blockCutGraph_exists_block [Finite V]
    (X : {B : Set V // IsBlock G B} ⊕ {v : V // IsCutVertex G v}) :
    ∃ B : {B : Set V // IsBlock G B}, ∃ z ∈ B.1, (blockCutGraph G).Reachable X (Sum.inl B) := by
  rcases X with B | c
  · obtain ⟨z, hz⟩ := B.2.1.sconn.1
    exact ⟨B, z, hz, Reachable.refl _⟩
  · obtain ⟨B, -, hB, -, -, hcB, -⟩ := (isCutVertex_iff G c.1).1 c.2
    exact ⟨⟨B, hB⟩, c.1, hcB, ((blockCutGraph_adj_inl_inr G ⟨B, hB⟩ c).2 hcB).symm.reachable⟩

/-- Every edge of the block–cut graph is a bridge. -/
lemma blockCutGraph_not_reachable [Finite V] (B : {B : Set V // IsBlock G B})
    (c : {v : V // IsCutVertex G v}) (hcB : c.1 ∈ B.1) :
    ¬ ((blockCutGraph G).deleteEdges {s(Sum.inl B, Sum.inr c)}).Reachable
      (Sum.inl B) (Sum.inr c) := by
  let R : V → Prop := fun y => ∃ b ∈ B.1, b ≠ c.1 ∧ Relation.ReflTransGen (adjIn G {c.1}ᶜ) b y
  let f : ({B : Set V // IsBlock G B} ⊕ {v : V // IsCutVertex G v}) → Prop := fun X =>
    match X with
    | Sum.inl D => ∃ y ∈ D.1, y ≠ c.1 ∧ R y
    | Sum.inr w => w.1 ≠ c.1 ∧ R w.1
  have hkey : ∀ (D : {B : Set V // IsBlock G B}) (w : {v : V // IsCutVertex G v}), w.1 ∈ D.1 →
      ¬ (D = B ∧ w = c) → (f (Sum.inl D) ↔ f (Sum.inr w)) := by
    intro D w hwD hne
    change (∃ y ∈ D.1, y ≠ c.1 ∧ R y) ↔ (w.1 ≠ c.1 ∧ R w.1)
    by_cases hwc : w.1 = c.1
    · have hDB : D.1 ≠ B.1 := fun h => hne ⟨Subtype.ext h, Subtype.ext hwc⟩
      simp only [hwc, ne_eq, not_true_eq_false, false_and, iff_false]
      rintro ⟨y, hyD, hyc, b, hbB, hbc, hby⟩
      exact not_rtg_of_blocks B.2 D.2 (Ne.symm hDB) hcB (hwc ▸ hwD) hbB hbc hyD hyc hby
    · constructor
      · rintro ⟨y, hyD, hyc, b, hbB, hbc, hby⟩
        refine ⟨hwc, b, hbB, hbc, hby.trans ?_⟩
        exact rtg_mono (fun x hx => hx.2)
          ((D.2.1.sconn_diff c.1 ⟨y, hyD, hyc⟩).rtg ⟨hyD, hyc⟩ ⟨hwD, hwc⟩)
      · rintro ⟨-, hR⟩
        exact ⟨w.1, hwD, hwc, hR⟩
  have hstep : ∀ X Y, ((blockCutGraph G).deleteEdges {s(Sum.inl B, Sum.inr c)}).Adj X Y →
      (f X ↔ f Y) := by
    intro X Y hXY
    rw [deleteEdges_adj] at hXY
    obtain ⟨hadj, hnot⟩ := hXY
    rcases X with D | w <;> rcases Y with D' | w'
    · exact absurd hadj (blockCutGraph_not_adj_inl_inl G D D')
    · exact hkey D w' ((blockCutGraph_adj_inl_inr G D w').1 hadj)
        (by rintro ⟨rfl, rfl⟩; exact hnot rfl)
    · exact (hkey D' w ((blockCutGraph_adj_inl_inr G D' w).1 hadj.symm)
        (by rintro ⟨rfl, rfl⟩; exact hnot Sym2.eq_swap)).symm
    · exact absurd hadj (blockCutGraph_not_adj_inr_inr G w w')
  have hreach : ∀ X Y, ((blockCutGraph G).deleteEdges {s(Sum.inl B, Sum.inr c)}).Reachable X Y →
      (f X ↔ f Y) := by
    rintro X Y ⟨p⟩
    induction p with
    | nil => exact Iff.rfl
    | cons h _ ih => exact (hstep _ _ h).trans ih
  intro h
  have hfB : f (Sum.inl B) := by
    obtain ⟨B1, B2, hB1, hB2, h12, hc1, hc2⟩ := (isCutVertex_iff G c.1).1 c.2
    obtain ⟨B', hB', hne, hcB'⟩ : ∃ B', IsBlock G B' ∧ B.1 ≠ B' ∧ c.1 ∈ B' := by
      by_cases h1 : B.1 = B1
      · exact ⟨B2, hB2, h1 ▸ h12, hc2⟩
      · exact ⟨B1, hB1, h1, hc1⟩
    obtain ⟨b, hbB, hbc⟩ := B.2.exists_ne hB' hne hcB'
    exact ⟨b, hbB, hbc, b, hbB, hbc, .refl⟩
  exact ((hreach _ _ h).1 hfB).1 rfl

end blockCut

/-- The block–cut graph of a finite connected graph is a tree. -/
theorem blockCutGraph_isTree [Finite V] (hconn : G.Connected) : (blockCutGraph G).IsTree := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x⟩ := hconn.nonempty
    obtain ⟨B0, hB0, -⟩ := exists_block_aux (G := G) (isNonseparable_singleton x)
    have : Nonempty ({B : Set V // IsBlock G B} ⊕ {v : V // IsCutVertex G v}) :=
      ⟨Sum.inl ⟨B0, hB0⟩⟩
    refine Connected.mk fun X Y => ?_
    obtain ⟨B, z, hz, hXB⟩ := blockCutGraph_exists_block G X
    obtain ⟨B', z', hz', hYB'⟩ := blockCutGraph_exists_block G Y
    exact hXB.trans ((blockCutGraph_reachable_of_walk G (hconn.preconnected z z').some B B' hz
      hz').trans hYB'.symm)
  · rw [isAcyclic_iff_forall_adj_isBridge]
    intro X Y hXY
    rw [isBridge_iff]
    rcases X with D | w <;> rcases Y with D' | w'
    · exact absurd hXY (blockCutGraph_not_adj_inl_inl G D D')
    · exact blockCutGraph_not_reachable G D w' ((blockCutGraph_adj_inl_inr G D w').1 hXY)
    · rw [Sym2.eq_swap]
      exact fun h => blockCutGraph_not_reachable G D' w
        ((blockCutGraph_adj_inl_inr G D' w).1 hXY.symm) h.symm
    · exact absurd hXY (blockCutGraph_not_adj_inr_inr G w w')

/-- Every block is complete or an odd cycle if and only if every vertex set with at least three
vertices that induces a 2-connected subgraph induces a complete graph or an odd cycle. -/
theorem gallai_iff [Finite V] :
    (∀ B : Set V, IsBlock G B →
        (∀ x ∈ B, ∀ y ∈ B, x ≠ y → G.Adj x y) ∨
          ∃ n, Odd n ∧ Nonempty (G.induce B ≃g cycleGraph n)) ↔
      ¬ ∃ S : Set V, 3 ≤ S.ncard ∧ (∀ x ∈ S, (G.induce (S \ {x})).Connected) ∧
        ¬ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) ∧
        ∀ n, Odd n → IsEmpty (G.induce S ≃g cycleGraph n) := by
  constructor
  · intro h hw
    obtain ⟨B, hB, hK, hC⟩ := (witness_iff G).1 hw
    rcases h B hB with hK' | ⟨n, hn, ⟨e⟩⟩
    · exact hK hK'
    · exact (hC n hn).false e
  · intro h B hB
    by_cases hK : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → G.Adj x y
    · exact Or.inl hK
    · right
      by_contra hC
      exact h ((witness_iff G).2 ⟨B, hB, hK, fun n hn => ⟨fun e => hC ⟨n, hn, ⟨e⟩⟩⟩⟩)

/-- **Erdős–Rubin–Taylor (1979), Borodin (1977), block form.** A finite connected graph is
degree-choosable if and only if some block of it is neither complete nor an odd cycle. -/
theorem degree_choosable_iff_blocks [Fintype V] [DecidableRel G.Adj] (hconn : G.Connected) :
    (∀ L : V → Finset ℕ, (∀ v, G.degree v ≤ (L v).card) →
        ∃ f : V → ℕ, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v) ↔
      ∃ B : Set V, IsBlock G B ∧ ¬ (∀ x ∈ B, ∀ y ∈ B, x ≠ y → G.Adj x y) ∧
        ∀ n, Odd n → IsEmpty (G.induce B ≃g cycleGraph n) := by
  exact (ErdosRubinTaylor.degree_choosable_iff G hconn).trans (witness_iff G)

end GraphBlocks
