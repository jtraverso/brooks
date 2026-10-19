/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Basic tools for degree-choosability

Connectivity of vertex sets, degrees into a vertex set, a greedy list-colouring lemma, the
slack lemma (Lemma A) and the extension lemma (Lemma B).
-/

@[expose] public section

open Finset SimpleGraph

namespace ErdosRubinTaylor

variable {V : Type*}

/-- Adjacency inside the vertex set `T`. -/
def adjIn (G : SimpleGraph V) (T : Set V) (u v : V) : Prop := u ∈ T ∧ v ∈ T ∧ G.Adj u v

/-- The vertex set `T` induces a connected subgraph (formulated via reflexive-transitive
closure of adjacency inside `T`). -/
def SConn (G : SimpleGraph V) (T : Set V) : Prop :=
  T.Nonempty ∧ ∀ u ∈ T, ∀ v ∈ T, Relation.ReflTransGen (adjIn G T) u v

/-- `L`-colourability of the vertices of `T` (properly on the edges inside `T`). -/
def ColIn {C : Type*} (G : SimpleGraph V) (T : Set V) (L : V → Finset C) : Prop :=
  ∃ f : V → C, (∀ v ∈ T, f v ∈ L v) ∧ ∀ u ∈ T, ∀ v ∈ T, G.Adj u v → f u ≠ f v

/-- A vertex set is a clique. -/
def IsCliqueOn (G : SimpleGraph V) (T : Set V) : Prop := ∀ x ∈ T, ∀ y ∈ T, x ≠ y → G.Adj x y

section rtg

variable {G : SimpleGraph V} {T T' : Set V}

lemma adjIn_symm {u v : V} (h : adjIn G T u v) : adjIn G T v u := ⟨h.2.1, h.1, h.2.2.symm⟩

lemma rtg_symm {u v : V} (h : Relation.ReflTransGen (adjIn G T) u v) :
    Relation.ReflTransGen (adjIn G T) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (adjIn_symm hbc) ih

lemma rtg_mono (hTT : T ⊆ T') {u v : V} (h : Relation.ReflTransGen (adjIn G T) u v) :
    Relation.ReflTransGen (adjIn G T') u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨hTT hbc.1, hTT hbc.2.1, hbc.2.2⟩

lemma rtg_mem {u v : V} (h : Relation.ReflTransGen (adjIn G T) u v) (hu : u ∈ T) : v ∈ T := by
  induction h with
  | refl => exact hu
  | tail _ hbc _ => exact hbc.2.1

/-- Closure lemma: if `D ⊆ W` is closed under adjacency inside `W`, paths in `W` starting in `D`
stay in `D`. -/
lemma rtg_closed {W D : Set V}
    (hcl : ∀ u ∈ D, ∀ v ∈ W, G.Adj u v → v ∈ D) {u v : V}
    (h : Relation.ReflTransGen (adjIn G W) u v) (hu : u ∈ D) :
    Relation.ReflTransGen (adjIn G D) u v ∧ v ∈ D := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hu⟩
  | tail _ hbc ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hc := hcl _ ih2 _ hbc.2.1 hbc.2.2
    exact ⟨ih1.tail ⟨ih2, hc, hbc.2.2⟩, hc⟩

lemma SConn.rtg (h : SConn G T) {u v : V} (hu : u ∈ T) (hv : v ∈ T) :
    Relation.ReflTransGen (adjIn G T) u v := h.2 u hu v hv

/-- A set is connected as soon as every vertex is joined to a fixed vertex. -/
lemma sconn_of_hub {a : V} (ha : a ∈ T)
    (h : ∀ v ∈ T, Relation.ReflTransGen (adjIn G T) a v) : SConn G T :=
  ⟨⟨a, ha⟩, fun u hu v hv => (rtg_symm (h u hu)).trans (h v hv)⟩

lemma connected_iff_sconn : (G.induce T).Connected ↔ SConn G T := by
  constructor
  · intro hc
    obtain ⟨⟨v, hv⟩⟩ := hc.nonempty
    refine ⟨⟨v, hv⟩, fun u hu w hw => ?_⟩
    have key : ∀ (a b : T) (p : (G.induce T).Walk a b),
        Relation.ReflTransGen (adjIn G T) a.1 b.1 := by
      intro a b p
      induction p with
      | nil => exact Relation.ReflTransGen.refl
      | cons h _ ih => exact Relation.ReflTransGen.head ⟨Subtype.prop _, Subtype.prop _, h⟩ ih
    exact key ⟨u, hu⟩ ⟨w, hw⟩ (hc.preconnected ⟨u, hu⟩ ⟨w, hw⟩).some
  · rintro ⟨⟨a, ha⟩, h⟩
    have : Nonempty T := ⟨⟨a, ha⟩⟩
    refine Connected.mk ?_
    rintro ⟨u, hu⟩ ⟨w, hw⟩
    have key : ∀ x y, Relation.ReflTransGen (adjIn G T) x y → ∀ (hx : x ∈ T) (hy : y ∈ T),
        (G.induce T).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
      intro x y hxy
      induction hxy with
      | refl => intro _ _; exact Reachable.refl _
      | tail _ hbc ih =>
        intro hx hy
        refine (ih hx hbc.1).trans (Adj.reachable ?_)
        exact hbc.2.2
    exact key u w (h u hu w hw) hu hw

lemma sconn_univ (hconn : G.Connected) : SConn G Set.univ := by
  obtain ⟨v⟩ := hconn.nonempty
  refine ⟨⟨v, trivial⟩, fun u _ w _ => ?_⟩
  have key : ∀ (a b : V) (p : G.Walk a b), Relation.ReflTransGen (adjIn G Set.univ) a b := by
    intro a b p
    induction p with
    | nil => exact Relation.ReflTransGen.refl
    | cons h _ ih => exact Relation.ReflTransGen.head ⟨trivial, trivial, h⟩ ih
  exact key u w (hconn.preconnected u w).some

end rtg

section fintype

variable [Fintype V]

open Classical in
/-- The number of neighbours of `v` lying in `T`. -/
noncomputable def dIn (G : SimpleGraph V) (T : Set V) (v : V) : ℕ :=
  (univ.filter (fun u => u ∈ T ∧ G.Adj v u)).card

lemma dIn_eq (G : SimpleGraph V) (T : Set V) (v : V) [DecidablePred (· ∈ T)]
    [DecidableRel G.Adj] : dIn G T v = (univ.filter (fun u => u ∈ T ∧ G.Adj v u)).card := by
  unfold dIn; congr 1; ext; simp

lemma dIn_univ (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    dIn G Set.univ v = G.degree v := by
  classical
  rw [dIn_eq, ← card_neighborFinset_eq_degree]; congr 1; ext; simp

lemma ncard_eq_filter (T : Set V) [DecidablePred (· ∈ T)] :
    T.ncard = (univ.filter (· ∈ T)).card := by
  rw [← Set.ncard_coe_finset]; congr; ext; simp

lemma dIn_le_ncard (G : SimpleGraph V) (T : Set V) {v : V} (hv : v ∈ T) :
    dIn G T v ≤ T.ncard - 1 := by
  classical
  rw [dIn_eq, ncard_eq_filter]
  have hsub : univ.filter (fun u => u ∈ T ∧ G.Adj v u) ⊆ (univ.filter (· ∈ T)).erase v := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and, mem_erase] at hu ⊢
    exact ⟨(G.ne_of_adj hu.2).symm, hu.1⟩
  have := card_le_card hsub
  rw [card_erase_of_mem (by simpa using hv)] at this
  exact this

open Classical in
lemma dIn_diff_single (G : SimpleGraph V) {T : Set V} {u : V} (hu : u ∈ T) (x : V) :
    dIn G T x = dIn G (T \ {u}) x + if G.Adj x u then 1 else 0 := by
  classical
  rw [dIn_eq, dIn_eq]
  by_cases hadj : G.Adj x u
  · have : univ.filter (fun w => w ∈ T ∧ G.Adj x w) =
        insert u (univ.filter (fun w => w ∈ T \ {u} ∧ G.Adj x w)) := by
      ext w
      simp only [mem_filter, mem_univ, true_and, mem_insert, Set.mem_sdiff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hwu : w = u
        · exact Or.inl hwu
        · exact Or.inr ⟨⟨h1, hwu⟩, h2⟩
      · rintro (rfl | ⟨⟨h1, _⟩, h2⟩)
        · exact ⟨hu, hadj⟩
        · exact ⟨h1, h2⟩
    rw [this, card_insert_of_notMem (by simp)]; simp [hadj]
  · simp only [hadj, ite_false, add_zero]
    congr 1
    ext w
    simp only [mem_filter, mem_univ, true_and, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun h => hadj (h ▸ h2)⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩

/-- Degree in the induced subgraph equals the number of neighbours inside the set. -/
lemma degree_induce (G : SimpleGraph V) (T : Set V) [Fintype T]
    [DecidableRel (G.induce T).Adj] (v : T) : (G.induce T).degree v = dIn G T v := by
  classical
  rw [dIn_eq, ← card_neighborFinset_eq_degree]
  refine card_bij (fun a _ => a.1) ?_ ?_ ?_
  · intro a ha
    simp only [mem_neighborFinset, induce_adj] at ha
    simp [ha, a.2]
  · intro a _ b _ h; exact Subtype.ext h
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩

/-! ### Greedy list colouring -/

open Classical in
/-- Greedy list colouring: colour the vertices of `U` in order of non-increasing rank `r`.
It suffices that each vertex has fewer neighbours in `U` of rank at least its own than
colours in its list. -/
lemma greedy_list {C : Type*} [Nonempty C] (G : SimpleGraph V)
    (L : V → Finset C) (r : V → ℕ) (U : Finset V)
    (hU : ∀ w ∈ U, (univ.filter (fun u => u ∈ U ∧ G.Adj w u ∧ r w ≤ r u)).card < (L w).card) :
    ∃ g : V → C, (∀ v ∈ U, g v ∈ L v) ∧ ∀ u ∈ U, ∀ v ∈ U, G.Adj u v → g u ≠ g v := by
  classical
  induction U using Finset.strongInduction with
  | H U ih =>
    rcases U.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => Classical.arbitrary C, by simp, by simp⟩
    obtain ⟨w, hwU, hwmin⟩ := exists_min_image U r hne
    obtain ⟨g, hg1, hg2⟩ := ih (U.erase w) (erase_ssubset hwU) (by
      intro x hx
      refine lt_of_le_of_lt (card_le_card ?_) (hU x (mem_of_mem_erase hx))
      intro u hu
      simp only [mem_filter, mem_univ, true_and, mem_erase] at hu ⊢
      exact ⟨hu.1.2, hu.2⟩)
    set N := (univ.filter (fun u => u ∈ U.erase w ∧ G.Adj w u)).image g
    have hN : N.card < (L w).card := by
      refine lt_of_le_of_lt card_image_le (lt_of_le_of_lt (card_le_card ?_) (hU w hwU))
      intro u hu
      simp only [mem_filter, mem_univ, true_and, mem_erase] at hu ⊢
      exact ⟨hu.1.2, hu.2, hwmin u hu.1.2⟩
    obtain ⟨c, hcL, hcN⟩ := exists_mem_notMem_of_card_lt_card hN
    refine ⟨Function.update g w c, ?_, ?_⟩
    · intro v hv
      by_cases hvw : v = w
      · subst hvw; simpa using hcL
      · rw [Function.update_of_ne hvw]; exact hg1 v (mem_erase.2 ⟨hvw, hv⟩)
    · have hgood : ∀ u ∈ U, u ≠ w → G.Adj w u → c ≠ g u := by
        intro u hu huw hadj h
        apply hcN
        rw [h]
        exact mem_image_of_mem g (by simp [hu, huw, hadj])
      intro u hu v hv huv
      by_cases huw : u = w
      · subst huw
        have hvw : v ≠ u := fun h => G.loopless.irrefl _ (h ▸ huv)
        rw [Function.update_self, Function.update_of_ne hvw]
        exact hgood v hv hvw huv
      · by_cases hvw : v = w
        · subst hvw
          rw [Function.update_self, Function.update_of_ne huw]
          exact (hgood u hu huw huv.symm).symm
        · rw [Function.update_of_ne huw, Function.update_of_ne hvw]
          exact hg2 u (mem_erase.2 ⟨huw, hu⟩) v (mem_erase.2 ⟨hvw, hv⟩) huv

end fintype

/-! ### Ranks (distances to a target set inside a vertex set) -/

/-- `near G W Tgt n v`: there is a walk of length `n` from `v` to `Tgt` whose vertices after `v`
lie in `W`. -/
def near (G : SimpleGraph V) (W Tgt : Set V) : ℕ → V → Prop
  | 0, v => v ∈ Tgt
  | n + 1, v => ∃ u ∈ W, G.Adj v u ∧ near G W Tgt n u

lemma exists_rank (G : SimpleGraph V) (W Tgt : Set V)
    (h : ∀ v ∈ W, ∃ n, near G W Tgt n v) :
    ∃ r : V → ℕ, ∀ v ∈ W, v ∉ Tgt → ∃ u ∈ W, G.Adj v u ∧ r u < r v := by
  classical
  refine ⟨fun v => if hv : ∃ n, near G W Tgt n v then Nat.find hv else 0, ?_⟩
  intro v hvW hvT
  have hex := h v hvW
  have hspec := Nat.find_spec hex
  simp only [hex, ↓reduceDIte]
  rcases hm : Nat.find hex with _ | j
  · rw [hm] at hspec; exact absurd hspec hvT
  · rw [hm] at hspec
    obtain ⟨u, huW, hvu, hu⟩ := hspec
    have hexu : ∃ n, near G W Tgt n u := ⟨j, hu⟩
    refine ⟨u, huW, hvu, ?_⟩
    simp only [hexu, ↓reduceDIte]
    have := Nat.find_min' hexu hu
    omega

section fintype2

variable [Fintype V]

/-- **Lemma A (slack).** If `T` is connected, every vertex of `T` has at least as many colours
as neighbours in `T`, and some vertex has more, then `T` is colourable from the lists. -/
lemma slack_colour {C : Type*} [Nonempty C] (G : SimpleGraph V) (T : Set V)
    (hT : SConn G T) {w0 : V} (hw0 : w0 ∈ T) (L : V → Finset C)
    (hL : ∀ v ∈ T, dIn G T v ≤ (L v).card) (hw : dIn G T w0 < (L w0).card) :
    ColIn G T L := by
  classical
  have hnear : ∀ v ∈ T, ∃ n, near G T {w0} n v := by
    intro v hv
    have key : ∀ a, Relation.ReflTransGen (adjIn G T) a w0 → ∃ n, near G T {w0} n a := by
      intro a ha
      induction ha using Relation.ReflTransGen.head_induction_on with
      | refl => exact ⟨0, rfl⟩
      | head hab _ ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, _, hab.2.1, hab.2.2, hn⟩
    exact key v (hT.rtg hv hw0)
  obtain ⟨r, hr⟩ := exists_rank G T {w0} hnear
  obtain ⟨g, hg1, hg2⟩ := greedy_list G L r (univ.filter (· ∈ T)) (by
    intro w hw'
    simp only [mem_filter, mem_univ, true_and] at hw'
    by_cases hww : w = w0
    · subst hww
      have h1 : (univ.filter (fun u => u ∈ univ.filter (· ∈ T) ∧ G.Adj w u ∧ r w ≤ r u)).card ≤
          (univ.filter (fun u => u ∈ T ∧ G.Adj w u)).card := by
        apply card_le_card
        intro u hu; simp only [mem_filter, mem_univ, true_and] at hu ⊢; exact ⟨hu.1, hu.2.1⟩
      rw [← dIn_eq] at h1
      omega
    · obtain ⟨u0, hu0T, hwu0, hru0⟩ := hr w hw' hww
      have hsub : univ.filter (fun u => u ∈ univ.filter (· ∈ T) ∧ G.Adj w u ∧ r w ≤ r u) ⊆
          (univ.filter (fun u => u ∈ T ∧ G.Adj w u)).erase u0 := by
        intro u hu
        simp only [mem_filter, mem_univ, true_and, mem_erase] at hu ⊢
        refine ⟨?_, hu.1, hu.2.1⟩
        rintro rfl; omega
      have h1 := card_le_card hsub
      have hmem : u0 ∈ univ.filter (fun u => u ∈ T ∧ G.Adj w u) := by simp [hu0T, hwu0]
      rw [card_erase_of_mem hmem, ← dIn_eq] at h1
      have hpos : 0 < dIn G T w := by rw [dIn_eq]; exact card_pos.2 ⟨u0, hmem⟩
      have := hL w hw'
      omega)
  exact ⟨g, fun v hv => hg1 v (by simpa using hv),
    fun u hu v hv h => hg2 u (by simpa using hu) v (by simpa using hv) h⟩

/-- Degree-choosability of a vertex set `T` (lists of size at least the degree into `T`). -/
def DCIn (C : Type*) (G : SimpleGraph V) (T : Set V) : Prop :=
  ∀ L : V → Finset C, (∀ v ∈ T, dIn G T v ≤ (L v).card) → ColIn G T L

/-- **Lemma B (extension).** If `G` is connected and the nonempty vertex set `T` is
degree-choosable, then `G` is degree-choosable. -/
lemma extend_from_set {C : Type*} [Nonempty C] (G : SimpleGraph V)
    (hconn : G.Connected) (T : Set V) (hTne : T.Nonempty) (hT : DCIn C G T)
    (L : V → Finset C) (hL : ∀ v, dIn G Set.univ v ≤ (L v).card) : ColIn G Set.univ L := by
  classical
  obtain ⟨t0, ht0⟩ := hTne
  have hnear : ∀ v ∈ (Set.univ : Set V), ∃ n, near G Set.univ T n v := by
    intro v _
    have key : ∀ (a b : V) (p : G.Walk a b), b ∈ T → near G Set.univ T p.length a := by
      intro a b p
      induction p with
      | nil => exact id
      | cons h _ ih => exact fun hb => ⟨_, trivial, h, ih hb⟩
    exact ⟨_, key v t0 (hconn.preconnected v t0).some ht0⟩
  obtain ⟨r, hr⟩ := exists_rank G Set.univ T hnear
  obtain ⟨g, hg1, hg2⟩ := greedy_list G L r (univ.filter (· ∉ T)) (by
    intro w hw'
    simp only [mem_filter, mem_univ, true_and] at hw'
    obtain ⟨u0, -, hwu0, hru0⟩ := hr w trivial hw'
    have hsub : univ.filter (fun u => u ∈ univ.filter (· ∉ T) ∧ G.Adj w u ∧ r w ≤ r u) ⊆
        (univ.filter (fun u => u ∈ (Set.univ : Set V) ∧ G.Adj w u)).erase u0 := by
      intro u hu
      simp only [mem_filter, mem_univ, true_and, mem_erase, Set.mem_univ] at hu ⊢
      refine ⟨?_, hu.2.1⟩
      rintro rfl; omega
    have h1 := card_le_card hsub
    have hmem : u0 ∈ univ.filter (fun u => u ∈ (Set.univ : Set V) ∧ G.Adj w u) := by simp [hwu0]
    rw [card_erase_of_mem hmem, ← dIn_eq] at h1
    have hpos : 0 < dIn G Set.univ w := by rw [dIn_eq]; exact card_pos.2 ⟨u0, hmem⟩
    have := hL w
    omega)
  set L' : V → Finset C := fun v =>
    L v \ (univ.filter (fun u => u ∉ T ∧ G.Adj v u)).image g with hL'
  obtain ⟨h, hh1, hh2⟩ := hT L' (by
    intro v hv
    have hsplit : dIn G Set.univ v =
        dIn G T v + (univ.filter (fun u => u ∉ T ∧ G.Adj v u)).card := by
      rw [dIn_eq, dIn_eq, ← card_union_of_disjoint]
      · congr 1; ext u; simp only [mem_filter, mem_univ, true_and, Set.mem_univ, mem_union]
        tauto
      · rw [Finset.disjoint_left]; intro u hu1 hu2
        simp only [mem_filter, mem_univ, true_and] at hu1 hu2; exact hu2.1 hu1.1
    have h1 := le_card_sdiff ((univ.filter (fun u => u ∉ T ∧ G.Adj v u)).image g) (L v)
    have h2 := card_image_le (s := univ.filter (fun u => u ∉ T ∧ G.Adj v u)) (f := g)
    have := hL v
    simp only [hL']
    omega)
  refine ⟨fun v => if v ∈ T then h v else g v, ?_, ?_⟩
  · intro v _
    by_cases hv : v ∈ T
    · simp only [hv, ite_true]; exact (mem_sdiff.1 (hh1 v hv)).1
    · simp only [hv, ite_false]; exact hg1 v (by simpa using hv)
  · intro u _ v _ huv
    by_cases hu : u ∈ T <;> by_cases hv : v ∈ T <;> simp only [hu, hv, ite_true, ite_false]
    · exact hh2 u hu v hv huv
    · intro he
      have := (mem_sdiff.1 (hh1 u hu)).2
      exact this (he ▸ mem_image_of_mem g (by simp [hv, huv]))
    · intro he
      have := (mem_sdiff.1 (hh1 v hv)).2
      exact this (he ▸ mem_image_of_mem g (by simp [hu, huv.symm]))
    · exact hg2 u (by simpa using hu) v (by simpa using hv) huv

end fintype2

end ErdosRubinTaylor
