/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ChoosabilityLib.ERTBasic
public import BrooksLib.Brooks

/-!
# Graphs that are not Gallai trees are degree-choosable

A vertex set `S` with `|S| ≥ 3` inducing a 2-connected subgraph which is neither complete nor an
odd cycle is degree-choosable (for any colour type): either some vertex has slack (Lemma A), or
some edge `uv` has a colour `c ∈ L u \ L v` (colour `u` with `c` and use Lemma A on `S − u`), or
all lists coincide and the induced subgraph is regular, so Brooks' theorem applies.  Lemma B then
extends the colouring to the whole connected graph.
-/

@[expose] public section

open Finset SimpleGraph

namespace ErdosRubinTaylor

variable {V : Type*}

lemma exists_third {S : Set V} (h3 : 3 ≤ S.ncard) (a b : V) : ∃ x ∈ S, x ≠ a ∧ x ≠ b := by
  by_contra h
  push Not at h
  have hsub : S ⊆ {a, b} := fun x hx => by
    by_cases hxa : x = a
    · simp [hxa]
    · simp [h x hx hxa]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_insert_le a ({b} : Set V)
  rw [Set.ncard_singleton] at h2
  omega

/-- A set of at least three vertices all of whose vertex-deleted subsets are connected is
connected. -/
lemma sconn_of_two_conn {G : SimpleGraph V} {S : Set V} (h3 : 3 ≤ S.ncard)
    (h2 : ∀ x ∈ S, SConn G (S \ {x})) : SConn G S := by
  obtain ⟨a, ha⟩ := Set.nonempty_of_ncard_ne_zero (s := S) (by omega)
  refine sconn_of_hub ha fun v hv => ?_
  obtain ⟨x, hx, hxa, hxv⟩ := exists_third h3 a v
  exact rtg_mono Set.sdiff_subset
    ((h2 x hx).rtg ⟨ha, fun h => hxa h.symm⟩ ⟨hv, fun h => hxv h.symm⟩)

variable [Fintype V]

/-- A 2-connected vertex set (of size at least three) inducing neither a complete graph nor an
odd cycle is degree-choosable. -/
theorem core_dc {C : Type*} [Nonempty C] (G : SimpleGraph V) (S : Set V)
    (h3 : 3 ≤ S.ncard) (h2 : ∀ x ∈ S, (G.induce (S \ {x})).Connected)
    (hK : ¬ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y)
    (hC : ∀ n, Odd n → IsEmpty (G.induce S ≃g cycleGraph n)) : DCIn C G S := by
  classical
  have h2' : ∀ x ∈ S, SConn G (S \ {x}) := fun x hx => connected_iff_sconn.1 (h2 x hx)
  have hS := sconn_of_two_conn h3 h2'
  intro L hL
  by_cases hw : ∃ w ∈ S, dIn G S w < (L w).card
  · obtain ⟨w, hwS, hw⟩ := hw
    exact slack_colour G S hS hwS L hL hw
  push Not at hw
  have heq : ∀ v ∈ S, (L v).card = dIn G S v := fun v hv => le_antisymm (hw v hv) (hL v hv)
  by_cases h2a : ∃ u ∈ S, ∃ v ∈ S, G.Adj u v ∧ ¬ L u ⊆ L v
  · obtain ⟨u, huS, v, hvS, huv, hsub⟩ := h2a
    obtain ⟨c, hcu, hcv⟩ := Finset.not_subset.1 hsub
    set L' : V → Finset C := fun x => if G.Adj u x then (L x).erase c else L x with hL'
    have hvS' : v ∈ S \ {u} := ⟨hvS, fun h => G.ne_of_adj huv (Set.mem_singleton_iff.1 h).symm⟩
    obtain ⟨f, hf1, hf2⟩ := slack_colour G (S \ {u}) (h2' u huS) hvS' L' (by
      intro x hx
      have hd := dIn_diff_single G huS x
      have hx' := heq x hx.1
      by_cases hux : G.Adj u x
      · have := pred_card_le_card_erase (s := L x) (a := c)
        simp only [hL', hux, ite_true]
        simp only [hux.symm, ite_true] at hd
        omega
      · have hxu : ¬ G.Adj x u := fun h => hux h.symm
        simp only [hL', hux, ite_false]
        simp only [hxu, ite_false] at hd
        omega) (by
      have hd := dIn_diff_single G huS v
      simp only [huv.symm, ite_true] at hd
      simp only [hL', huv, ite_true, Finset.erase_eq_of_notMem hcv]
      have := heq v hvS
      omega)
    refine ⟨Function.update f u c, ?_, ?_⟩
    · intro x hx
      by_cases hxu : x = u
      · subst hxu; simpa using hcu
      · rw [Function.update_of_ne hxu]
        have := hf1 x ⟨hx, hxu⟩
        simp only [hL'] at this
        split_ifs at this
        · exact Finset.mem_of_mem_erase this
        · exact this
    · have hgood : ∀ x ∈ S, x ≠ u → G.Adj u x → c ≠ f x := by
        intro x hx hxu hux h
        have := hf1 x ⟨hx, hxu⟩
        simp only [hL', hux, ite_true] at this
        exact (Finset.notMem_erase c (L x)) (h ▸ this)
      intro x hx y hy hxy
      by_cases hxu : x = u
      · subst hxu
        have hyx : y ≠ x := fun h => G.loopless.irrefl _ (h ▸ hxy)
        rw [Function.update_self, Function.update_of_ne hyx]
        exact hgood y hy hyx hxy
      · by_cases hyu : y = u
        · subst hyu
          rw [Function.update_self, Function.update_of_ne hxu]
          exact (hgood x hx hxu hxy.symm).symm
        · rw [Function.update_of_ne hxu, Function.update_of_ne hyu]
          exact hf2 x ⟨hx, hxu⟩ y ⟨hy, hyu⟩ hxy
  · push Not at h2a
    obtain ⟨s0, hs0⟩ := hS.1
    have hall : ∀ v ∈ S, L v = L s0 := by
      intro v hv
      have key : ∀ w, Relation.ReflTransGen (adjIn G S) s0 w → L w = L s0 := by
        intro w hw
        induction hw with
        | refl => rfl
        | tail _ hbc ih =>
          rw [← ih]
          exact (Finset.Subset.antisymm (h2a _ hbc.1 _ hbc.2.1 hbc.2.2)
            (h2a _ hbc.2.1 _ hbc.1 hbc.2.2.symm)).symm
      exact key v (hS.rtg hs0 hv)
    set k := (L s0).card
    have hdeg : ∀ v : S, (G.induce S).degree v = k := by
      intro v
      rw [degree_induce, ← heq v v.2, hall v v.2]
    have hconnS : (G.induce S).Connected := connected_iff_sconn.2 hS
    have hne : G.induce S ≠ ⊤ := by
      intro htop
      apply hK
      intro x hx y hy hxy
      have : (⊤ : SimpleGraph S).Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
        simp only [top_adj, ne_eq, Subtype.mk.injEq]; exact hxy
      rw [← htop] at this
      exact this
    have hcol := BrooksTheorem.brooks (G.induce S) hconnS hne hC
    have hmax : (G.induce S).maxDegree ≤ k :=
      maxDegree_le_of_forall_degree_le _ _ (fun v => (hdeg v).le)
    obtain ⟨col⟩ := hcol.mono hmax
    let e : Fin k ≃ L s0 := (L s0).equivFin.symm
    refine ⟨fun v => if h : v ∈ S then (e (col ⟨v, h⟩)).1 else Classical.arbitrary C, ?_, ?_⟩
    · intro v hv
      simp only [hv, ↓reduceDIte]
      rw [hall v hv]; exact (e _).2
    · intro x hx y hy hxy
      simp only [hx, hy, ↓reduceDIte]
      intro h
      have := col.valid (show (G.induce S).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
      exact this (e.injective (Subtype.ext h))

/-- **Direction (⇐) of Erdős–Rubin–Taylor**, for an arbitrary (nonempty) colour type. -/
theorem choosable_of_not_gallai {C : Type*} [Nonempty C] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (S : Set V) (h3 : 3 ≤ S.ncard)
    (h2 : ∀ x ∈ S, (G.induce (S \ {x})).Connected)
    (hK : ¬ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y)
    (hC : ∀ n, Odd n → IsEmpty (G.induce S ≃g cycleGraph n))
    (L : V → Finset C) (hL : ∀ v, G.degree v ≤ (L v).card) :
    ∃ f : V → C, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v := by
  have hne : S.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨f, hf1, hf2⟩ := extend_from_set G hconn S hne (core_dc G S h3 h2 hK hC) L
    (fun v => by rw [dIn_univ]; exact hL v)
  exact ⟨f, fun v => hf1 v trivial, fun u v h => hf2 u trivial v trivial h⟩

end ErdosRubinTaylor
