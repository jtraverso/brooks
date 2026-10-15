/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import BrooksLib.Greedy

/-!
# Core induction for Brooks' theorem

We prove, by strong induction on the number of (ordered) edges, that every graph on a fixed
finite vertex type with all degrees at most `k ≥ 3` and no `(k + 1)`-clique is `k`-colourable.
The inductive step either colours greedily (towards a vertex with two equally coloured
neighbours, or towards a vertex of small degree), or finds a separation by two non-adjacent
vertices `x, z` and glues colourings of the two sides.
-/

@[expose] public section

open SimpleGraph Finset

namespace BrooksTheorem
namespace Aux

variable {V : Type*}

/-- The spanning subgraph of `H` keeping only edges with both ends in `S`. -/
def restr (H : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := ⟨fun _ _ ⟨h, hu, hv⟩ => ⟨h.symm, hv, hu⟩⟩
  loopless := ⟨fun u h => H.loopless.irrefl u h.1⟩

@[simp] lemma restr_adj {H : SimpleGraph V} {S : Set V} {u v : V} :
    (restr H S).Adj u v ↔ H.Adj u v ∧ u ∈ S ∧ v ∈ S := Iff.rfl

lemma restr_le (H : SimpleGraph V) (S : Set V) : restr H S ≤ H := fun _ _ h => h.1

lemma addE_adj {H : SimpleGraph V} {x z u v : V} :
    (H ⊔ edge x z).Adj u v ↔ H.Adj u v ∨ ((u = x ∧ v = z ∨ u = z ∧ v = x) ∧ u ≠ v) := by
  rw [sup_adj, edge_adj]

lemma Proper.comp {k : ℕ} {H : SimpleGraph V} {f : V → Fin k} (hf : Proper H f)
    (σ : Equiv.Perm (Fin k)) : Proper H (σ ∘ f) :=
  fun u v h e => hf u v h (σ.injective e)

lemma Proper.mono {k : ℕ} {H H' : SimpleGraph V} {f : V → Fin k} (hf : Proper H f)
    (hle : H' ≤ H) : Proper H' f :=
  fun u v h => hf u v (hle h)

lemma exists_perm2 {k : ℕ} {a b a' b' : Fin k} (hab : a ≠ b) (hab' : a' ≠ b') :
    ∃ σ : Equiv.Perm (Fin k), σ a = a' ∧ σ b = b' := by
  refine ⟨(Equiv.swap a a').trans (Equiv.swap (Equiv.swap a a' b) b'), ?_, ?_⟩
  · have h1 : Equiv.swap a a' b ≠ a' := by
      intro h
      apply hab
      apply (Equiv.swap a a').injective
      rw [h, Equiv.swap_apply_left]
    simp only [Equiv.trans_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne h1.symm hab'
  · simp

/-- Gluing colourings of two sides of a separation. -/
lemma glue {k : ℕ} (H : SimpleGraph V) (S1 S2 : Set V)
    (hedge : ∀ u v, H.Adj u v → (u ∈ S1 ∧ v ∈ S1) ∨ (u ∈ S2 ∧ v ∈ S2))
    (c1 c2 : V → Fin k) (h1 : Proper (restr H S1) c1) (h2 : Proper (restr H S2) c2)
    (hagree : ∀ v ∈ S1, v ∈ S2 → c1 v = c2 v) : ∃ g : V → Fin k, Proper H g := by
  classical
  refine ⟨fun v => if v ∈ S1 then c1 v else c2 v, fun u v huv => ?_⟩
  rcases hedge u v huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · simp only [hu, hv, ite_true]
    exact h1 u v ⟨huv, hu, hv⟩
  · have eu : (if u ∈ S1 then c1 u else c2 u) = c2 u := by
      split_ifs with h
      · exact hagree u h hu
      · rfl
    have ev : (if v ∈ S1 then c1 v else c2 v) = c2 v := by
      split_ifs with h
      · exact hagree v h hv
      · rfl
    simp only [eu, ev]
    exact h2 u v ⟨huv, hu, hv⟩

variable [Fintype V]

open Classical in
/-- The set of ordered adjacent pairs. -/
noncomputable def pairs (H : SimpleGraph V) : Finset (V × V) :=
  univ.filter (fun p => H.Adj p.1 p.2)

/-- Number of ordered adjacent pairs (twice the number of edges). -/
noncomputable def mu (H : SimpleGraph V) : ℕ := (pairs H).card

lemma mem_pairs {H : SimpleGraph V} {p : V × V} : p ∈ pairs H ↔ H.Adj p.1 p.2 := by
  simp [pairs]

lemma mu_restr_lt (H : SimpleGraph V) (S : Set V) {u v : V} (h : H.Adj u v) (hu : u ∉ S) :
    mu (restr H S) < mu H := by
  apply card_lt_card
  refine ⟨fun p hp => mem_pairs.2 (mem_pairs.1 hp).1, fun hsub => ?_⟩
  have := mem_pairs.1 (hsub (mem_pairs.2 (show H.Adj (u, v).1 (u, v).2 from h)))
  exact hu this.2.1

lemma mu_addE_lt (H : SimpleGraph V) (S : Set V) {x z px pz : V} (hxz : x ≠ z) (hzS : z ∈ S)
    (hpx : H.Adj x px) (hpxS : px ∉ S) (hpz : H.Adj z pz) (hpzS : pz ∉ S) :
    mu (restr H S ⊔ edge x z) < mu H := by
  classical
  have h1 : pairs (restr H S ⊔ edge x z) ⊆ pairs (restr H S) ∪ {(x, z), (z, x)} := by
    intro p hp
    rw [mem_pairs, addE_adj] at hp
    rcases hp with hp | ⟨hp, _⟩
    · exact mem_union_left _ (mem_pairs.2 hp)
    · apply mem_union_right
      rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [Prod.ext_iff, h1, h2]
      · simp [Prod.ext_iff, h1, h2]
  have h2 : (pairs (restr H S) ∪ {(x, z), (z, x)}).card ≤ mu (restr H S) + 2 := by
    refine (card_union_le _ _).trans ?_
    unfold mu
    have := card_insert_le (x, z) {(z, x)}
    simp only [card_singleton] at this
    omega
  have hD : Disjoint (pairs (restr H S)) {(x, px), (px, x), (z, pz)} := by
    rw [Finset.disjoint_left]
    intro p hp hpD
    rw [mem_pairs] at hp
    simp only [mem_insert, mem_singleton] at hpD
    rcases hpD with rfl | rfl | rfl
    · exact hpxS hp.2.2
    · exact hpxS hp.2.1
    · exact hpzS hp.2.2
  have hcard3 : ({(x, px), (px, x), (z, pz)} : Finset (V × V)).card = 3 := by
    have hxpx : x ≠ px := H.ne_of_adj hpx
    have hpxz : px ≠ z := fun h => hpxS (h ▸ hzS)
    rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simp [Prod.ext_iff, hpxz]
    · simp [Prod.ext_iff, hxpx, hxz]
  have h3 : pairs (restr H S) ∪ {(x, px), (px, x), (z, pz)} ⊆ pairs H := by
    intro p hp
    rcases mem_union.1 hp with hp | hp
    · exact mem_pairs.2 (mem_pairs.1 hp).1
    · simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact mem_pairs.2 hpx
      · exact mem_pairs.2 hpx.symm
      · exact mem_pairs.2 hpz
  have h4 := card_le_card h3
  rw [card_union_of_disjoint hD, hcard3] at h4
  unfold mu at h2 ⊢
  have := card_le_card h1
  omega

lemma nb_restr_subset (H : SimpleGraph V) (S : Set V) (v : V) : nb (restr H S) v ⊆ nb H v :=
  fun _ hu => (mem_nb.1 hu).1 |> mem_nb.2

lemma deg_restr {H : SimpleGraph V} {k : ℕ} (hdeg : ∀ v, (nb H v).card ≤ k) (S : Set V) :
    ∀ v, (nb (restr H S) v).card ≤ k :=
  fun v => (card_le_card (nb_restr_subset H S v)).trans (hdeg v)

lemma nb_addE_sub [DecidableEq V] (H : SimpleGraph V) (S : Set V) {x z w w' pw : V}
    (hw : (w = x ∧ w' = z) ∨ (w = z ∧ w' = x)) (hpwS : pw ∉ S) :
    nb (restr H S ⊔ edge x z) w ⊆ insert w' ((nb H w).erase pw) := by
  intro u hu
  rw [mem_nb, addE_adj] at hu
  rw [mem_insert, mem_erase, mem_nb]
  rcases hu with ⟨hu1, _, hu3⟩ | ⟨hu, _⟩
  · exact Or.inr ⟨fun h => hpwS (h ▸ hu3), hu1⟩
  · left
    rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp_all

lemma deg_addE {H : SimpleGraph V} {k : ℕ} (hdeg : ∀ v, (nb H v).card ≤ k) (S : Set V)
    {x z px pz : V} (hpx : H.Adj x px) (hpxS : px ∉ S) (hpz : H.Adj z pz) (hpzS : pz ∉ S) :
    ∀ v, (nb (restr H S ⊔ edge x z) v).card ≤ k := by
  classical
  intro v
  have aux : ∀ w w' pw, ((w = x ∧ w' = z) ∨ (w = z ∧ w' = x)) → H.Adj w pw → pw ∉ S →
      (nb (restr H S ⊔ edge x z) w).card ≤ k := by
    intro w w' pw hw hpw hpwS
    have h1 := card_le_card (nb_addE_sub H S hw hpwS)
    have h2 := card_insert_le w' ((nb H w).erase pw)
    have h3 := card_erase_of_mem (mem_nb.2 hpw)
    have h4 := hdeg w
    have h5 := card_pos.2 ⟨pw, mem_nb.2 hpw⟩
    omega
  by_cases hvx : v = x
  · exact hvx ▸ aux x z px (Or.inl ⟨rfl, rfl⟩) hpx hpxS
  by_cases hvz : v = z
  · exact hvz ▸ aux z x pz (Or.inr ⟨rfl, rfl⟩) hpz hpzS
  refine (card_le_card fun u hu => ?_).trans (hdeg v)
  rw [mem_nb, addE_adj] at hu
  rcases hu with hu | ⟨hu, _⟩
  · exact mem_nb.2 hu.1
  · exfalso; rcases hu with ⟨h1, _⟩ | ⟨h1, _⟩ <;> contradiction

/-- The induction hypothesis: every graph with fewer ordered edges and the same constraints is
`k`-colourable. -/
def IHyp (k : ℕ) (H : SimpleGraph V) : Prop :=
  ∀ H' : SimpleGraph V, mu H' < mu H → (∀ v, (nb H' v).card ≤ k) → H'.CliqueFree (k + 1) →
    ∃ f : V → Fin k, Proper H' f

lemma colour_restr {k : ℕ} {H : SimpleGraph V} (ih : IHyp k H) (hdeg : ∀ v, (nb H v).card ≤ k)
    (hcf : H.CliqueFree (k + 1)) (S : Set V) {u v : V} (h : H.Adj u v) (hu : u ∉ S) :
    ∃ f : V → Fin k, Proper (restr H S) f :=
  ih _ (mu_restr_lt H S h hu) (deg_restr hdeg S) (hcf.anti (restr_le H S))


lemma nb_eq_insert [DecidableEq V] {H : SimpleGraph V} {k : ℕ} (hdeg : ∀ v, (nb H v).card ≤ k)
    {w p : V}
    {Q : Finset V} (hQ : Q ⊆ nb H w) (hp : H.Adj w p) (hpQ : p ∉ Q) (hcard : k ≤ Q.card + 1) :
    nb H w = insert p Q := by
  symm
  apply eq_of_subset_of_card_le
  · intro u hu
    rw [mem_insert] at hu
    rcases hu with rfl | hu
    · exact mem_nb.2 hp
    · exact hQ hu
  · rw [card_insert_of_notMem hpQ]; exact (hdeg w).trans hcard

omit [Fintype V] in
/-- Recolour two non-adjacent vertices `x, z` with a common colour `col`. -/
lemma proper_update2 [DecidableEq V] {k : ℕ} {H : SimpleGraph V} (S : Set V) {x z : V}
    (hn : ¬ H.Adj x z)
    (c0 : V → Fin k) (hc0 : Proper (restr H {v | v ∈ S ∧ v ≠ x ∧ v ≠ z}) c0) (col : Fin k)
    (hcol : ∀ w v, (w = x ∨ w = z) → v ∈ S → v ≠ x → v ≠ z → H.Adj w v → c0 v ≠ col) :
    Proper (restr H S) (fun v => if v = x ∨ v = z then col else c0 v) := by
  intro u v ⟨huv, hu, hv⟩
  by_cases hux : u = x ∨ u = z <;> by_cases hvx : v = x ∨ v = z
  · exfalso
    have hne := H.ne_of_adj huv
    rcases hux with rfl | rfl <;> rcases hvx with rfl | rfl
    · exact hne rfl
    · exact hn huv
    · exact hn huv.symm
    · exact hne rfl
  · simp only [hux, hvx, ite_true, ite_false]
    push Not at hvx
    exact (hcol u v hux hv hvx.1 hvx.2 huv).symm
  · simp only [hux, hvx, ite_true, ite_false]
    push Not at hux
    exact hcol v u hvx hu hux.1 hux.2 huv.symm
  · simp only [hux, hvx, ite_false]
    push Not at hux hvx
    exact hc0 u v ⟨huv, ⟨hu, hux⟩, ⟨hv, hvx⟩⟩

lemma clique_side {k : ℕ} (hk : 3 ≤ k) {H : SimpleGraph V} (ih : IHyp k H)
    (hdeg : ∀ v, (nb H v).card ≤ k) (hcf : H.CliqueFree (k + 1)) (S : Set V) {x z px pz : V}
    (hxz : x ≠ z) (hn : ¬ H.Adj x z) (hpx : H.Adj x px) (hpxS : px ∉ S)
    (hpz : H.Adj z pz) (hpzS : pz ∉ S)
    (hK : ¬ (restr H S ⊔ edge x z).CliqueFree (k + 1)) :
    (∃ c : V → Fin k, Proper (restr H S) c ∧ c x = c z) ∧
    (∀ v ∉ S, H.Adj x v → v = px) ∧ (∀ v ∉ S, H.Adj z v → v = pz) := by
  classical
  simp only [CliqueFree, not_forall, not_not] at hK
  obtain ⟨K, hK⟩ := hK
  rw [isNClique_iff] at hK
  obtain ⟨hKc, hKcard⟩ := hK
  have hadjK : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → (restr H S ⊔ edge x z).Adj u v :=
    fun u hu v hv huv => hKc hu hv huv
  have hxK : x ∈ K ∧ z ∈ K := by
    by_contra hcon
    apply hcf K
    rw [isNClique_iff]
    refine ⟨fun u hu v hv huv => ?_, hKcard⟩
    have := hadjK u hu v hv huv
    rw [addE_adj] at this
    rcases this with h | ⟨h, _⟩
    · exact h.1
    · exfalso; apply hcon
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hu, hv⟩
      · exact ⟨hv, hu⟩
  set Q := (K.erase x).erase z with hQdef
  have hzKx : z ∈ K.erase x := mem_erase.2 ⟨hxz.symm, hxK.2⟩
  have hQcard : Q.card = k - 1 := by
    rw [hQdef, card_erase_of_mem hzKx, card_erase_of_mem hxK.1, hKcard]; omega
  have hQmem : ∀ q ∈ Q, q ≠ z ∧ q ≠ x ∧ q ∈ K := by
    intro q hq
    simp only [hQdef, mem_erase] at hq
    exact ⟨hq.1, hq.2.1, hq.2.2⟩
  have hQadj : ∀ w ∈ ({x, z} : Finset V), ∀ q ∈ Q, H.Adj w q ∧ q ∈ S := by
    intro w hw q hq
    obtain ⟨hqz, hqx, hqK⟩ := hQmem q hq
    have hwK : w ∈ K := by
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hxK.1
      · exact hxK.2
    have hwq : w ≠ q := by
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hqx.symm
      · exact hqz.symm
    have := hadjK w hwK q hqK hwq
    rw [addE_adj] at this
    rcases this with h | ⟨h, _⟩
    · exact ⟨h.1, h.2.2⟩
    · exfalso
      rcases h with ⟨_, h⟩ | ⟨_, h⟩
      · exact hqz h
      · exact hqx h
  have hQS : ∀ q ∈ Q, q ∈ S := fun q hq => (hQadj x (by simp) q hq).2
  have hnbx : nb H x = insert px Q :=
    nb_eq_insert hdeg (fun q hq => mem_nb.2 (hQadj x (by simp) q hq).1) hpx
      (fun h => hpxS (hQS px h)) (by omega)
  have hnbz : nb H z = insert pz Q :=
    nb_eq_insert hdeg (fun q hq => mem_nb.2 (hQadj z (by simp) q hq).1) hpz
      (fun h => hpzS (hQS pz h)) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨c0, hc0⟩ := colour_restr ih hdeg hcf {v | v ∈ S ∧ v ≠ x ∧ v ≠ z} hpx
      (fun h => h.2.1 rfl)
    have hinj : Set.InjOn c0 (Q : Set V) := by
      intro q1 hq1 q2 hq2 he
      by_contra hne
      obtain ⟨h1z, h1x, h1K⟩ := hQmem q1 hq1
      obtain ⟨h2z, h2x, h2K⟩ := hQmem q2 hq2
      have := hadjK q1 h1K q2 h2K hne
      rw [addE_adj] at this
      rcases this with h | ⟨h, _⟩
      · exact hc0 q1 q2 ⟨h.1, ⟨h.2.1, h1x, h1z⟩, ⟨h.2.2, h2x, h2z⟩⟩ he
      · rcases h with ⟨h, _⟩ | ⟨h, _⟩
        · exact h1x h
        · exact h1z h
    have himg : (Q.image c0).card < k := by
      rw [card_image_of_injOn hinj, hQcard]; omega
    obtain ⟨col, hcol⟩ := exists_not_mem_of_card_lt _ himg
    refine ⟨_, proper_update2 S hn c0 hc0 col ?_, by simp⟩
    intro w v hw hvS hvx hvz hwv he
    apply hcol
    rw [← he]
    apply mem_image_of_mem
    have hv : v ∈ nb H w := mem_nb.2 hwv
    rcases hw with rfl | rfl
    · rw [hnbx, mem_insert] at hv
      rcases hv with rfl | hv
      · exact absurd hvS hpxS
      · exact hv
    · rw [hnbz, mem_insert] at hv
      rcases hv with rfl | hv
      · exact absurd hvS hpzS
      · exact hv
  · intro v hvS hxv
    have hv : v ∈ nb H x := mem_nb.2 hxv
    rw [hnbx, mem_insert] at hv
    rcases hv with rfl | hv
    · rfl
    · exact absurd (hQS v hv) hvS
  · intro v hvS hzv
    have hv : v ∈ nb H z := mem_nb.2 hzv
    rw [hnbz, mem_insert] at hv
    rcases hv with rfl | hv
    · rfl
    · exact absurd (hQS v hv) hvS

lemma few_side {k : ℕ} (hk : 3 ≤ k) {H : SimpleGraph V} (ih : IHyp k H)
    (hdeg : ∀ v, (nb H v).card ≤ k) (hcf : H.CliqueFree (k + 1)) (S : Set V) {x z qx qz w : V}
    (hn : ¬ H.Adj x z) (hw : H.Adj x w)
    (hx1 : ∀ v ∈ S, v ≠ z → H.Adj x v → v = qx) (hz1 : ∀ v ∈ S, v ≠ x → H.Adj z v → v = qz) :
    ∃ c : V → Fin k, Proper (restr H S) c ∧ c x = c z := by
  classical
  obtain ⟨c0, hc0⟩ := colour_restr ih hdeg hcf {v | v ∈ S ∧ v ≠ x ∧ v ≠ z} hw
    (fun h => h.2.1 rfl)
  have h2 : ({c0 qx, c0 qz} : Finset (Fin k)).card < k :=
    lt_of_le_of_lt (card_le_two) (by omega)
  obtain ⟨col, hcol⟩ := exists_not_mem_of_card_lt _ h2
  refine ⟨_, proper_update2 S hn c0 hc0 col ?_, by simp⟩
  intro w' v hw' hvS hvx hvz hwv he
  apply hcol
  rcases hw' with rfl | rfl
  · rw [hx1 v hvS hvz hwv] at he; simp [he]
  · rw [hz1 v hvS hvx hwv] at he; simp [he]

/-- Separation at a single vertex `z`: the set `B` is attached to the rest only through `z`. -/
lemma cut_case {k : ℕ} {H : SimpleGraph V} (ih : IHyp k H)
    (hdeg : ∀ v, (nb H v).card ≤ k) (hcf : H.CliqueFree (k + 1)) (B : Set V) {x z y0 b bn : V}
    (hxz : x ≠ z) (hxB : x ∉ B) (hxy : H.Adj x y0)
    (hBedge : ∀ u ∈ B, ∀ v, H.Adj u v → v ∈ B ∨ v = z) (hb : b ∈ B) (hbn : H.Adj b bn) :
    ∃ g : V → Fin k, Proper H g := by
  obtain ⟨c1, h1⟩ := colour_restr ih hdeg hcf Bᶜ hbn (by simpa using hb)
  obtain ⟨c2, h2⟩ := colour_restr ih hdeg hcf {v | v ∈ B ∨ v = z} hxy
    (by simp [hxB, hxz])
  refine glue H Bᶜ {v | v ∈ B ∨ v = z} ?_ c1 (Equiv.swap (c2 z) (c1 z) ∘ c2) h1
    (h2.comp _) ?_
  · intro u v h
    by_cases hu : u ∈ B
    · exact Or.inr ⟨Or.inl hu, hBedge u hu v h⟩
    · by_cases hv : v ∈ B
      · exact Or.inr ⟨hBedge v hv u h.symm, Or.inl hv⟩
      · exact Or.inl ⟨hu, hv⟩
  · intro v hv1 hv2
    rcases hv2 with hv2 | rfl
    · exact absurd hv2 hv1
    · simp

lemma step {k : ℕ} (hk : 3 ≤ k) {H : SimpleGraph V} (ih : IHyp k H)
    (hdeg : ∀ v, (nb H v).card ≤ k) (hcf : H.CliqueFree (k + 1)) :
    ∃ f : V → Fin k, Proper H f := by
  classical
  by_cases hreg : ∃ y0, k ≤ (nb H y0).card
  swap
  · push Not at hreg
    obtain ⟨g, -, hg⟩ := greedy_reach H k hdeg ∅ (fun _ => ⟨0, by omega⟩) (by simp)
      (fun _ => True) (fun w _ _ => by simpa using hreg w) (fun w _ => ⟨0, trivial⟩)
    exact ⟨g, hg⟩
  obtain ⟨y0, hy0⟩ := hreg
  have hy0k : (nb H y0).card = k := le_antisymm (hdeg y0) hy0
  obtain ⟨x, hx, z, hz, hxz, hn⟩ : ∃ x ∈ nb H y0, ∃ z ∈ nb H y0, x ≠ z ∧ ¬ H.Adj x z := by
    by_contra hcon
    push Not at hcon
    apply hcf (insert y0 (nb H y0))
    rw [isNClique_iff]
    refine ⟨?_, ?_⟩
    · rw [coe_insert, isClique_insert]
      exact ⟨fun u hu v hv huv => hcon u hu v hv huv, fun u hu _ => mem_nb.1 hu⟩
    · rw [card_insert_of_notMem (by simp), hy0k]
  rw [mem_nb] at hx hz
  set P : Finset V := {x, z} with hPdef
  let f : V → Fin k := fun _ => ⟨0, by omega⟩
  let T : V → Prop := fun w => w = y0 ∨ (nb H w).card < k
  have hy0x : y0 ≠ x := H.ne_of_adj hx
  have hy0z : y0 ≠ z := H.ne_of_adj hz
  have hf : ∀ u ∈ P, ∀ v ∈ P, H.Adj u v → f u ≠ f v := by
    intro u hu v hv huv
    exfalso
    have hne := H.ne_of_adj huv
    simp only [hPdef, mem_insert, mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact hne rfl
    · exact hn huv
    · exact hn huv.symm
    · exact hne rfl
  have hT : ∀ w ∉ P, T w → (((nb H w).filter (· ∈ P)).image f).card +
       ((nb H w).filter (· ∉ P)).card < k := by
    intro w _ hw
    have himg := card_image_le (s := (nb H w).filter (· ∈ P)) (f := f)
    have himg1 : (((nb H w).filter (· ∈ P)).image f).card ≤ 1 := by
      apply card_le_one.2
      intro a ha b hb
      simp only [mem_image] at ha hb
      obtain ⟨_, _, rfl⟩ := ha
      obtain ⟨_, _, rfl⟩ := hb
      rfl
    have hsplit := card_filter_add_card_filter_not (s := nb H w) (fun u => u ∈ P)
    rcases hw with rfl | hw
    · have h2 : ({x, z} : Finset V) ⊆ (nb H w).filter (· ∈ P) := by
        intro u hu
        simp only [mem_insert, mem_singleton] at hu
        rcases hu with rfl | rfl
        · simp [hPdef, hx]
        · simp [hPdef, hz]
      have := card_le_card h2
      rw [card_pair hxz] at this
      omega
    · omega
  by_cases hall : ∀ w ∉ P, ∃ n, near H P T n w
  · obtain ⟨g, -, hg⟩ := greedy_reach H k hdeg P f hf T hT hall
    exact ⟨g, hg⟩
  push Not at hall
  obtain ⟨b, hbP, hbn⟩ := hall
  set B : Set V := {v | v ∉ P ∧ ∀ n, ¬ near H P T n v} with hBdef
  have hBcl : ∀ u ∈ B, ∀ v, H.Adj u v → v ∈ B ∨ v = x ∨ v = z := by
    intro u hu v huv
    by_cases hvP : v ∈ P
    · right; simpa [hPdef] using hvP
    · left
      exact ⟨hvP, fun n hn => hu.2 (n + 1) ⟨v, huv, hvP, hn⟩⟩
  have hy0B : y0 ∉ B := fun h => h.2 0 (Or.inl rfl)
  have hxB : x ∉ B := fun h => h.1 (by simp [hPdef])
  have hzB : z ∉ B := fun h => h.1 (by simp [hPdef])
  have hbB : b ∈ B := ⟨hbP, hbn⟩
  have hbdeg : k ≤ (nb H b).card := by
    by_contra hcon
    exact hbn 0 (Or.inr (by omega))
  obtain ⟨bn, hbn'⟩ : (nb H b).Nonempty := card_pos.1 (by omega)
  rw [mem_nb] at hbn'
  by_cases hxB' : ∃ bx ∈ B, H.Adj x bx
  swap
  · push Not at hxB'
    refine cut_case ih hdeg hcf B hxz hxB hx.symm ?_ hbB hbn'
    intro u hu v huv
    rcases hBcl u hu v huv with h | rfl | h
    · exact Or.inl h
    · exact absurd huv.symm (hxB' u hu)
    · exact Or.inr h
  by_cases hzB' : ∃ bz ∈ B, H.Adj z bz
  swap
  · push Not at hzB'
    refine cut_case ih hdeg hcf B hxz.symm hzB hz.symm ?_ hbB hbn'
    intro u hu v huv
    rcases hBcl u hu v huv with h | h | rfl
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd huv.symm (hzB' u hu)
  obtain ⟨bx, hbxB, hbx⟩ := hxB'
  obtain ⟨bz, hbzB, hbz⟩ := hzB'
  set S1 : Set V := Bᶜ with hS1
  set S2 : Set V := {v | v ∈ B ∨ v = x ∨ v = z} with hS2
  have hedge : ∀ u v, H.Adj u v → (u ∈ S1 ∧ v ∈ S1) ∨ (u ∈ S2 ∧ v ∈ S2) := by
    intro u v h
    by_cases hu : u ∈ B
    · exact Or.inr ⟨Or.inl hu, hBcl u hu v h⟩
    · by_cases hv : v ∈ B
      · exact Or.inr ⟨hBcl v hv u h.symm, Or.inl hv⟩
      · exact Or.inl ⟨hu, hv⟩
  have hinter : ∀ v ∈ S1, v ∈ S2 → v = x ∨ v = z := by
    intro v hv1 hv2
    rcases hv2 with hv2 | hv2
    · exact absurd hv2 hv1
    · exact hv2
  have hzS1 : z ∈ S1 := hzB
  have hzS2 : z ∈ S2 := Or.inr (Or.inr rfl)
  have hbxS1 : bx ∉ S1 := fun h => h hbxB
  have hbzS1 : bz ∉ S1 := fun h => h hbzB
  have hy0S2 : y0 ∉ S2 := by
    rintro (h | h | h)
    · exact hy0B h
    · exact hy0x h
    · exact hy0z h
  -- gluing two colourings in which `x` and `z` share a colour
  have same_glue : ∀ c1 c2 : V → Fin k, Proper (restr H S1) c1 → c1 x = c1 z →
      Proper (restr H S2) c2 → c2 x = c2 z → ∃ g : V → Fin k, Proper H g := by
    intro c1 c2 h1 e1 h2 e2
    refine glue H S1 S2 hedge c1 (Equiv.swap (c2 x) (c1 x) ∘ c2) h1 (h2.comp _) ?_
    intro v hv1 hv2
    rcases hinter v hv1 hv2 with rfl | rfl
    · simp
    · simp [← e1, ← e2]
  by_cases hc1 : (restr H S1 ⊔ edge x z).CliqueFree (k + 1)
  · by_cases hc2 : (restr H S2 ⊔ edge x z).CliqueFree (k + 1)
    · obtain ⟨c1, h1⟩ := ih _ (mu_addE_lt H S1 hxz hzS1 hbx hbxS1 hbz hbzS1)
        (deg_addE hdeg S1 hbx hbxS1 hbz hbzS1) hc1
      obtain ⟨c2, h2⟩ := ih _ (mu_addE_lt H S2 hxz hzS2 hx.symm hy0S2 hz.symm hy0S2)
        (deg_addE hdeg S2 hx.symm hy0S2 hz.symm hy0S2) hc2
      have hexz : (restr H S1 ⊔ edge x z).Adj x z := addE_adj.2 (Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hxz⟩)
      have hexz2 : (restr H S2 ⊔ edge x z).Adj x z :=
        addE_adj.2 (Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hxz⟩)
      obtain ⟨σ, hσ1, hσ2⟩ := exists_perm2 (h2 x z hexz2) (h1 x z hexz)
      refine glue H S1 S2 hedge c1 (σ ∘ c2) (h1.mono le_sup_left)
        ((h2.mono le_sup_left).comp σ) ?_
      intro v hv1 hv2
      rcases hinter v hv1 hv2 with rfl | rfl
      · simp [hσ1]
      · simp [hσ2]
    · obtain ⟨⟨c2, h2, e2⟩, ux, uz⟩ := clique_side hk ih hdeg hcf S2 hxz hn hx.symm hy0S2
        hz.symm hy0S2 hc2
      obtain ⟨c1, h1, e1⟩ := few_side hk ih hdeg hcf S1 (qx := y0) (qz := y0) hn hbx
        (fun v hv1 hvz hxv => ux v (fun hv2 => by
          rcases hinter v hv1 hv2 with rfl | rfl
          · exact H.loopless.irrefl _ hxv
          · exact hvz rfl) hxv)
        (fun v hv1 hvx hzv => uz v (fun hv2 => by
          rcases hinter v hv1 hv2 with rfl | rfl
          · exact hvx rfl
          · exact H.loopless.irrefl _ hzv) hzv)
      exact same_glue c1 c2 h1 e1 h2 e2
  · obtain ⟨⟨c1, h1, e1⟩, ux, uz⟩ := clique_side hk ih hdeg hcf S1 hxz hn hbx hbxS1
      hbz hbzS1 hc1
    obtain ⟨c2, h2, e2⟩ := few_side hk ih hdeg hcf S2 (qx := bx) (qz := bz) hn hx.symm
      (fun v hv2 hvz hxv => ux v (fun hv1 => by
        rcases hinter v hv1 hv2 with rfl | rfl
        · exact H.loopless.irrefl _ hxv
        · exact hvz rfl) hxv)
      (fun v hv2 hvx hzv => uz v (fun hv1 => by
        rcases hinter v hv1 hv2 with rfl | rfl
        · exact hvx rfl
        · exact H.loopless.irrefl _ hzv) hzv)
    exact same_glue c1 c2 h1 e1 h2 e2

/-- The core statement: every graph on `V` with all degrees at most `k ≥ 3` and no
`(k + 1)`-clique has a proper `k`-colouring. -/
theorem exists_proper (k : ℕ) (hk : 3 ≤ k) (H : SimpleGraph V)
    (hdeg : ∀ v, (nb H v).card ≤ k) (hcf : H.CliqueFree (k + 1)) :
    ∃ f : V → Fin k, Proper H f := by
  suffices h : ∀ n, ∀ H : SimpleGraph V, mu H = n → (∀ v, (nb H v).card ≤ k) →
      H.CliqueFree (k + 1) → ∃ f : V → Fin k, Proper H f from h _ H rfl hdeg hcf
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro H hn hdeg hcf
    exact step hk (fun H' hlt hdeg' hcf' => ihn _ (hn ▸ hlt) H' rfl hdeg' hcf') hdeg hcf

end Aux
end BrooksTheorem
