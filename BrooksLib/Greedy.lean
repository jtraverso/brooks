/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Greedy colouring tools for Brooks' theorem

Auxiliary material: neighbour finsets, proper colourings as functions, and a greedy
extension lemma for colourings driven by a rank function or by reachability of
"terminal" vertices.
-/

@[expose] public section

open SimpleGraph Finset

namespace BrooksTheorem
namespace Aux

variable {V : Type*}

/-- A function is a proper colouring of `H`. -/
def Proper {k : ℕ} (H : SimpleGraph V) (f : V → Fin k) : Prop :=
  ∀ u v, H.Adj u v → f u ≠ f v

variable [Fintype V]

open Classical in
/-- The finset of neighbours of `v` (classical decidability). -/
noncomputable def nb (H : SimpleGraph V) (v : V) : Finset V := univ.filter (H.Adj v)

@[simp] lemma mem_nb {H : SimpleGraph V} {v u : V} : u ∈ nb H v ↔ H.Adj v u := by
  simp [nb]


lemma exists_not_mem_of_card_lt {k : ℕ} (C : Finset (Fin k)) (h : C.card < k) :
    ∃ c : Fin k, c ∉ C := by
  by_contra hcon
  push Not at hcon
  have : (univ : Finset (Fin k)) ⊆ C := fun x _ => hcon x
  have := Finset.card_le_card this
  simp at this
  omega

/-- Greedy colouring along a rank: vertices of larger rank are coloured first. -/
lemma greedy_core [DecidableEq V] (H : SimpleGraph V) (k : ℕ) (r : V → ℕ) :
    ∀ (n : ℕ) (P : Finset V) (f : V → Fin k), Pᶜ.card = n →
    (∀ u ∈ P, ∀ v ∈ P, H.Adj u v → f u ≠ f v) →
    (∀ w ∉ P, (((nb H w).filter (· ∈ P)).image f).card +
       ((nb H w).filter (fun u => u ∉ P ∧ r w ≤ r u)).card < k) →
    ∃ g : V → Fin k, (∀ v ∈ P, g v = f v) ∧ Proper H g := by
  intro n
  induction n with
  | zero =>
    intro P f hn hf _
    have hP : ∀ v, v ∈ P := by
      intro v
      by_contra h
      have : v ∈ Pᶜ := by simpa using h
      rw [Finset.card_eq_zero] at hn
      simp_all
    exact ⟨f, fun _ _ => rfl, fun u v h => hf u (hP u) v (hP v) h⟩
  | succ n ih =>
    intro P f hn hf hc
    have hne : Pᶜ.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨w, hwP, hwmax⟩ := Finset.exists_max_image Pᶜ r hne
    have hwP' : w ∉ P := by simpa using hwP
    have hCk : (((nb H w).filter (· ∈ P)).image f).card < k :=
      lt_of_le_of_lt (Nat.le_add_right _ _) (hc w hwP')
    obtain ⟨col, hcol⟩ := exists_not_mem_of_card_lt _ hCk
    have hcard : (insert w P)ᶜ.card = n := by
      have : (insert w P)ᶜ = Pᶜ.erase w := by ext; simp
      rw [this, card_erase_of_mem hwP]; omega
    have hprop : ∀ u ∈ insert w P, ∀ v ∈ insert w P, H.Adj u v →
        Function.update f w col u ≠ Function.update f w col v := by
      intro u hu v hv huv
      rw [mem_insert] at hu hv
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact absurd huv (H.loopless.irrefl _)
      · have hvw : v ≠ u := fun h => hwP' (h ▸ hv)
        simp only [Function.update_self, Function.update_of_ne hvw]
        intro h
        apply hcol
        rw [h]
        exact mem_image_of_mem f (by simp [hv, huv])
      · have huw : u ≠ v := fun h => hwP' (h ▸ hu)
        simp only [Function.update_self, Function.update_of_ne huw]
        intro h
        apply hcol
        rw [← h]
        exact mem_image_of_mem f (by simp [hu, huv.symm])
      · have huw : u ≠ w := fun h => hwP' (h ▸ hu)
        have hvw : v ≠ w := fun h => hwP' (h ▸ hv)
        simp only [Function.update_of_ne huw, Function.update_of_ne hvw]
        exact hf u hu v hv huv
    have hcond : ∀ w' ∉ insert w P,
        (((nb H w').filter (· ∈ insert w P)).image (Function.update f w col)).card +
          ((nb H w').filter (fun u => u ∉ insert w P ∧ r w' ≤ r u)).card < k := by
      intro w' hw'
      rw [mem_insert, not_or] at hw'
      obtain ⟨hw'w, hw'P⟩ := hw'
      have hrw : r w' ≤ r w := hwmax w' (by simpa using hw'P)
      have hold := hc w' hw'P
      by_cases hadj : H.Adj w' w
      · have h1 : (((nb H w').filter (· ∈ insert w P)).image (Function.update f w col)) ⊆
            insert col (((nb H w').filter (· ∈ P)).image f) := by
          intro c hc'
          simp only [mem_image, mem_filter, mem_nb, mem_insert] at hc'
          obtain ⟨u, ⟨hu1, hu2⟩, rfl⟩ := hc'
          rcases hu2 with rfl | hu2
          · simp
          · have huw : u ≠ w := fun h => hwP' (h ▸ hu2)
            rw [Function.update_of_ne huw]
            exact mem_insert_of_mem (mem_image_of_mem f (by simp [hu1, hu2]))
        have h2 : (nb H w').filter (fun u => u ∉ P ∧ r w' ≤ r u) =
            insert w ((nb H w').filter (fun u => u ∉ insert w P ∧ r w' ≤ r u)) := by
          ext u
          simp only [mem_filter, mem_nb, mem_insert, not_or]
          constructor
          · rintro ⟨hu1, hu2, hu3⟩
            by_cases huw : u = w
            · left; exact huw
            · right; exact ⟨hu1, ⟨huw, hu2⟩, hu3⟩
          · rintro (rfl | ⟨hu1, ⟨_, hu2⟩, hu3⟩)
            · exact ⟨hadj, hwP', hrw⟩
            · exact ⟨hu1, hu2, hu3⟩
        have h3 : w ∉ (nb H w').filter (fun u => u ∉ insert w P ∧ r w' ≤ r u) := by
          simp
        rw [h2, card_insert_of_notMem h3] at hold
        have := (card_le_card h1).trans (card_insert_le _ _)
        omega
      · have h1 : (nb H w').filter (· ∈ insert w P) = (nb H w').filter (· ∈ P) := by
          ext u
          simp only [mem_filter, mem_nb, mem_insert]
          constructor
          · rintro ⟨hu1, rfl | hu2⟩
            · exact absurd hu1 hadj
            · exact ⟨hu1, hu2⟩
          · rintro ⟨hu1, hu2⟩; exact ⟨hu1, Or.inr hu2⟩
        have h1' : ((nb H w').filter (· ∈ P)).image (Function.update f w col) =
            ((nb H w').filter (· ∈ P)).image f := by
          apply image_congr
          intro u hu
          simp only [coe_filter, mem_nb, Set.mem_ofPred_eq] at hu
          have huw : u ≠ w := fun h => hwP' (h ▸ hu.2)
          simp [Function.update_of_ne huw]
        have h2 : (nb H w').filter (fun u => u ∉ insert w P ∧ r w' ≤ r u) =
            (nb H w').filter (fun u => u ∉ P ∧ r w' ≤ r u) := by
          ext u
          simp only [mem_filter, mem_nb, mem_insert, not_or]
          constructor
          · rintro ⟨hu1, ⟨_, hu2⟩, hu3⟩; exact ⟨hu1, hu2, hu3⟩
          · rintro ⟨hu1, hu2, hu3⟩
            exact ⟨hu1, ⟨fun h => hadj (h ▸ hu1), hu2⟩, hu3⟩
        rw [h1, h1', h2]
        exact hold
    obtain ⟨g, hg1, hg2⟩ := ih (insert w P) (Function.update f w col) hcard hprop hcond
    refine ⟨g, fun v hv => ?_, hg2⟩
    rw [hg1 v (mem_insert_of_mem hv)]
    simp [Function.update, show v ≠ w from fun h => hwP' (h ▸ hv)]
/-- `near H P T n w`: there is a walk of length `n` from `w` to a vertex satisfying `T`, all of
whose vertices after `w` avoid `P`. -/
def near (H : SimpleGraph V) (P : Finset V) (T : V → Prop) : ℕ → V → Prop
  | 0, w => T w
  | n + 1, w => ∃ u, H.Adj w u ∧ u ∉ P ∧ near H P T n u

/-- Greedy colouring towards terminals: if every uncoloured vertex reaches a terminal avoiding
the precoloured set, and terminals have fewer than `k` constraints, the colouring extends. -/
lemma greedy_reach [DecidableEq V] (H : SimpleGraph V) (k : ℕ) (hdeg : ∀ v, (nb H v).card ≤ k)
    (P : Finset V) (f : V → Fin k)
    (hf : ∀ u ∈ P, ∀ v ∈ P, H.Adj u v → f u ≠ f v) (T : V → Prop)
    (hT : ∀ w ∉ P, T w → (((nb H w).filter (· ∈ P)).image f).card +
       ((nb H w).filter (· ∉ P)).card < k)
    (hreach : ∀ w ∉ P, ∃ n, near H P T n w) :
    ∃ g : V → Fin k, (∀ v ∈ P, g v = f v) ∧ Proper H g := by
  classical
  let r : V → ℕ := fun w => if h : ∃ n, near H P T n w then Nat.find h else 0
  refine greedy_core H k r _ P f rfl hf ?_
  intro w hw
  obtain ⟨n0, hn0⟩ := hreach w hw
  have hex : ∃ n, near H P T n w := ⟨n0, hn0⟩
  have hrw : r w = Nat.find hex := dite_eq_left hex
  have hspec := Nat.find_spec hex
  have himg := card_image_le (s := (nb H w).filter (· ∈ P)) (f := f)
  have hsplit := card_filter_add_card_filter_not (s := nb H w) (fun u => u ∈ P)
  have hdw := hdeg w
  rcases hm : Nat.find hex with _ | j
  · rw [hm] at hspec
    have := hT w hw hspec
    have hsub : (nb H w).filter (fun u => u ∉ P ∧ r w ≤ r u) ⊆ (nb H w).filter (· ∉ P) := by
      intro u; simp only [mem_filter]; tauto
    have := card_le_card hsub
    omega
  · rw [hm] at hspec
    obtain ⟨u, hwu, huP, hu⟩ := hspec
    have hexu : ∃ n, near H P T n u := ⟨j, hu⟩
    have hru : r u ≤ j := by
      have : r u = Nat.find hexu := dite_eq_left hexu
      rw [this]; exact Nat.find_min' hexu hu
    have hsub : (nb H w).filter (fun u => u ∉ P ∧ r w ≤ r u) ⊆
        ((nb H w).filter (· ∉ P)).erase u := by
      intro v hv
      simp only [mem_filter, mem_erase] at hv ⊢
      refine ⟨?_, hv.1, hv.2.1⟩
      rintro rfl
      omega
    have hmem : u ∈ (nb H w).filter (· ∉ P) := by simp [hwu, huP]
    have := card_le_card hsub
    rw [card_erase_of_mem hmem] at this
    have hpos := card_pos.mpr ⟨u, hmem⟩
    omega

end Aux
end BrooksTheorem
