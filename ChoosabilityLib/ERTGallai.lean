/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ChoosabilityLib.ERTBasic

/-!
# Gallai trees

A vertex set `T` is a *Gallai set* if every 2-connected subset `S ⊆ T` with `|S| ≥ 3` induces a
complete graph or an odd cycle.  We prove, by induction on `|T|` and splitting at a cut vertex:

* `bad_lists`: a connected Gallai set has a list assignment with `|L v| ≥ deg_T v` admitting no
  proper colouring;
* `regular_gallai_block`: a connected Gallai set in which all degrees are at most `k` and all
  vertices except possibly one have degree `k` induces a complete graph or an odd cycle.
-/

@[expose] public section

open Finset SimpleGraph

namespace ErdosRubinTaylor

variable {V : Type*} {G : SimpleGraph V}

/-- Every 2-connected subset of `T` with at least three vertices induces a complete graph or an
odd cycle (`T` induces a Gallai forest). -/
def Gallai (G : SimpleGraph V) (T : Set V) : Prop :=
  ∀ S ⊆ T, 3 ≤ S.ncard → (∀ x ∈ S, (G.induce (S \ {x})).Connected) →
    IsCliqueOn G S ∨ ∃ n, Odd n ∧ Nonempty (G.induce S ≃g cycleGraph n)

lemma gallai_mono {T T' : Set V} (h : Gallai G T) (hsub : T' ⊆ T) : Gallai G T' :=
  fun S hS => h S (hS.trans hsub)

lemma three_le_of_not_clique [Finite V] {T : Set V} (hT : SConn G T) (hK : ¬ IsCliqueOn G T) :
    3 ≤ T.ncard := by
  simp only [IsCliqueOn, not_forall] at hK
  obtain ⟨x, hx, y, hy, hxy, hnadj⟩ := hK
  rcases (hT.rtg hx hy).cases_head with h | ⟨c, hc, -⟩
  · exact absurd h hxy
  · have hcx : c ≠ x := (G.ne_of_adj hc.2.2).symm
    have hcy : c ≠ y := fun h => hnadj (h ▸ hc.2.2)
    have hsub : ({x, y, c} : Set V) ⊆ T := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hc.2.1
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair hcy.symm] at this
    · exact this
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hxy, hcx.symm⟩

lemma two_le_ncard_insert [Finite V] {D : Set V} {x b : V} (hb : b ∈ D) (hxb : x ≠ b) :
    2 ≤ (insert x D).ncard := by
  have hsub : ({x, b} : Set V) ⊆ insert x D := Set.insert_subset_insert (by simpa using hb)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_pair hxb] at this

/-- From a vertex `v ≠ x` of a connected set `T`, some neighbour of `x` can be reached inside
`T − x`. -/
lemma reach_cut {T : Set V} (hT : SConn G T) {x : V} (hx : x ∈ T) {v : V} (hv : v ∈ T \ {x}) :
    ∃ c ∈ T \ {x}, G.Adj c x ∧ Relation.ReflTransGen (adjIn G (T \ {x})) v c := by
  by_contra hno
  push Not at hno
  have key : ∀ w, Relation.ReflTransGen (adjIn G T) v w →
      w ∈ T \ {x} ∧ Relation.ReflTransGen (adjIn G (T \ {x})) v w := by
    intro w hw
    induction hw with
    | refl => exact ⟨hv, .refl⟩
    | @tail b c _ hbc ih =>
      obtain ⟨ih1, ih2⟩ := ih
      by_cases hcx : c = x
      · subst hcx; exact absurd ih2 (hno b ih1 hbc.2.2)
      · have hc : c ∈ T \ {x} := ⟨hbc.2.1, hcx⟩
        exact ⟨hc, ih2.tail ⟨ih1, hc, hbc.2.2⟩⟩
  exact (key x (hT.rtg hv.1 hx)).1.2 rfl

lemma sconn_insert {W D : Set V} {x : V} (hDW : D ⊆ W)
    (hcl : ∀ u ∈ D, ∀ v ∈ W, G.Adj u v → v ∈ D)
    (hreach : ∀ v ∈ W, ∃ c ∈ W, G.Adj c x ∧ Relation.ReflTransGen (adjIn G W) v c) :
    SConn G (insert x D) := by
  refine sconn_of_hub (Set.mem_insert x D) fun v hv => ?_
  rcases hv with rfl | hv
  · exact .refl
  · obtain ⟨c, -, hcx, hvc⟩ := hreach v (hDW hv)
    obtain ⟨h1, h2⟩ := rtg_closed hcl hvc hv
    refine rtg_symm ((rtg_mono (Set.subset_insert x D) h1).tail ?_)
    exact ⟨Set.mem_insert_of_mem _ h2, Set.mem_insert _ _, hcx⟩

lemma adj_of_sconn_insert {D : Set V} {x : V} (h : SConn G (insert x D)) (hne : D.Nonempty)
    (hxD : x ∉ D) : ∃ d ∈ D, G.Adj x d := by
  obtain ⟨d, hd⟩ := hne
  rcases (h.rtg (Set.mem_insert x D) (Set.mem_insert_of_mem x hd)).cases_head with
    h' | ⟨c, hc, -⟩
  · exact absurd (h' ▸ hd) hxD
  · rcases hc.2.1 with rfl | hcD
    · exact absurd hc.2.2 (G.loopless.irrefl _)
    · exact ⟨c, hcD, hc.2.2⟩

/-- Splitting a connected set at a cut vertex `x`. -/
lemma cut_decomp {T : Set V} (hT : SConn G T) {x : V} (hx : x ∈ T)
    (hcut : ¬ SConn G (T \ {x})) (hne : (T \ {x}).Nonempty) :
    ∃ A B : Set V, A ∪ B = T \ {x} ∧ Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) ∧ SConn G (insert x A) ∧ SConn G (insert x B) := by
  obtain ⟨a, ha⟩ := hne
  set W := T \ {x} with hW
  set A : Set V := {v | Relation.ReflTransGen (adjIn G W) a v} with hA
  have hAW : A ⊆ W := fun v hv => rtg_mem hv ha
  have hclA : ∀ u ∈ A, ∀ v ∈ W, G.Adj u v → v ∈ A :=
    fun u hu v hv huv => Relation.ReflTransGen.tail hu ⟨hAW hu, hv, huv⟩
  have hclB : ∀ u ∈ W \ A, ∀ v ∈ W, G.Adj u v → v ∈ W \ A := by
    intro u hu v hv huv
    refine ⟨hv, fun hvA => hu.2 ?_⟩
    exact hclA v hvA u hu.1 huv.symm
  have hreach := fun v (hv : v ∈ W) => reach_cut hT hx hv
  refine ⟨A, W \ A, Set.union_sdiff_cancel hAW, Set.disjoint_sdiff_right, ⟨a, .refl⟩, ?_, ?_,
    sconn_insert hAW hclA hreach, sconn_insert Set.sdiff_subset hclB hreach⟩
  · by_contra hB
    apply hcut
    refine sconn_of_hub ha fun v hv => ?_
    by_contra hva
    exact hB ⟨v, hv, hva⟩
  · intro u hu v hv huv
    exact hv.2 (hclA u hu v hv.1 huv)

section fintype

variable [Fintype V]

lemma dIn_split {T A B : Set V} {x : V} (hAB : A ∪ B = T \ {x}) (hdisj : Disjoint A B)
    (hx : x ∈ T) (hnoadj : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    (∀ v ∈ A, dIn G T v = dIn G (insert x A) v) ∧
    (∀ v ∈ B, dIn G T v = dIn G (insert x B) v) ∧
    dIn G T x = dIn G (insert x A) x + dIn G (insert x B) x := by
  classical
  have hmem : ∀ u, u ∈ T ↔ u = x ∨ u ∈ A ∨ u ∈ B := by
    intro u
    constructor
    · intro hu
      by_cases hux : u = x
      · exact Or.inl hux
      · have : u ∈ A ∪ B := hAB ▸ ⟨hu, hux⟩
        exact Or.inr this
    · rintro (rfl | hu)
      · exact hx
      · have : u ∈ T \ {x} := hAB ▸ hu
        exact this.1
  refine ⟨fun v hv => ?_, fun v hv => ?_, ?_⟩
  · rw [dIn_eq, dIn_eq]
    congr 1; ext u
    simp only [mem_filter, mem_univ, true_and, Set.mem_insert_iff, hmem]
    constructor
    · rintro ⟨h | h | h, hadj⟩
      · exact ⟨Or.inl h, hadj⟩
      · exact ⟨Or.inr h, hadj⟩
      · exact absurd hadj (hnoadj v hv u h)
    · rintro ⟨h | h, hadj⟩
      · exact ⟨Or.inl h, hadj⟩
      · exact ⟨Or.inr (Or.inl h), hadj⟩
  · rw [dIn_eq, dIn_eq]
    congr 1; ext u
    simp only [mem_filter, mem_univ, true_and, Set.mem_insert_iff, hmem]
    constructor
    · rintro ⟨h | h | h, hadj⟩
      · exact ⟨Or.inl h, hadj⟩
      · exact absurd hadj.symm (hnoadj u h v hv)
      · exact ⟨Or.inr h, hadj⟩
    · rintro ⟨h | h, hadj⟩
      · exact ⟨Or.inl h, hadj⟩
      · exact ⟨Or.inr (Or.inr h), hadj⟩
  · rw [dIn_eq, dIn_eq, dIn_eq, ← card_union_of_disjoint]
    · congr 1; ext u
      simp only [mem_filter, mem_univ, true_and, Set.mem_insert_iff, hmem, mem_union]
      tauto
    · rw [Finset.disjoint_left]
      intro u h1 h2
      simp only [mem_filter, mem_univ, true_and, Set.mem_insert_iff] at h1 h2
      have hux : u ≠ x := (G.ne_of_adj h1.2).symm
      rcases h1.1 with h | h
      · exact hux h
      rcases h2.1 with h' | h'
      · exact hux h'
      exact Set.disjoint_left.1 hdisj h h'

lemma dIn_clique {T : Set V} (hK : IsCliqueOn G T) {u : V} (hu : u ∈ T) :
    dIn G T u = T.ncard - 1 := by
  classical
  rw [dIn_eq, ncard_eq_filter]
  have : univ.filter (fun w => w ∈ T ∧ G.Adj u w) = (univ.filter (· ∈ T)).erase u := by
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(G.ne_of_adj h2).symm, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, hK u hu w h2 (Ne.symm h1)⟩
  rw [this, card_erase_of_mem (by simpa using hu)]

omit [Fintype V] in
lemma ncard_eq_of_iso [Finite V] {T : Set V} {n : ℕ} (e : G.induce T ≃g cycleGraph n) :
    T.ncard = n := by
  classical
  have := Fintype.ofFinite V
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, Fintype.card_congr e.toEquiv,
    Fintype.card_fin]

lemma dIn_cycle {T : Set V} {n : ℕ} (e : G.induce T ≃g cycleGraph n) (hn : Odd n)
    (h2 : 2 ≤ T.ncard) {u : V} (hu : u ∈ T) : dIn G T u = 2 := by
  classical
  have hcard := ncard_eq_of_iso e
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := by obtain ⟨j, hj⟩ := hn; exact ⟨n - 3, by omega⟩
  rw [← degree_induce G T ⟨u, hu⟩, ← e.degree_eq ⟨u, hu⟩]
  convert (cycleGraph_degree_three_le (n := m) (v := e ⟨u, hu⟩))

lemma block_regular {T : Set V}
    (h : IsCliqueOn G T ∨ ∃ n, Odd n ∧ Nonempty (G.induce T ≃g cycleGraph n))
    (h2 : 2 ≤ T.ncard) {u v : V} (hu : u ∈ T) (hv : v ∈ T) : dIn G T u = dIn G T v := by
  rcases h with hK | ⟨n, hn, ⟨e⟩⟩
  · rw [dIn_clique hK hu, dIn_clique hK hv]
  · rw [dIn_cycle e hn h2 hu, dIn_cycle e hn h2 hv]

omit [Fintype V] in
lemma not_two_col_cycle [Finite V] {T : Set V} {n : ℕ} (e : G.induce T ≃g cycleGraph n) (hn : Odd n)
    (h2 : 2 ≤ T.ncard) (f : V → ℕ) (hf1 : ∀ v ∈ T, f v ∈ ({0, 1} : Finset ℕ))
    (hf2 : ∀ u ∈ T, ∀ v ∈ T, G.Adj u v → f u ≠ f v) : False := by
  have hcard := ncard_eq_of_iso e
  have hcol : (cycleGraph n).Colorable 2 := by
    refine ⟨Coloring.mk (fun i => ⟨f (e.symm i).1, ?_⟩) ?_⟩
    · have := hf1 _ (e.symm i).2
      simp only [mem_insert, mem_singleton] at this
      omega
    · intro i j hij heq
      have hadj : (G.induce T).Adj (e.symm i) (e.symm j) := e.symm.map_adj_iff.2 hij
      exact hf2 _ (e.symm i).2 _ (e.symm j).2 hadj (congrArg Fin.val heq)
  have h3 := chromaticNumber_cycleGraph_of_odd n (by omega) hn
  have := hcol.chromaticNumber_le
  rw [h3] at this
  exact absurd this (by decide)

/-- A connected Gallai set has a degree list assignment with no proper colouring. -/
theorem bad_lists (G : SimpleGraph V) : ∀ n, ∀ T : Set V, T.ncard = n → SConn G T →
    Gallai G T →
    ∃ L : V → Finset ℕ, (∀ v ∈ T, dIn G T v ≤ (L v).card) ∧ ¬ ColIn G T L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hTn hT hG
  classical
  by_cases hK : IsCliqueOn G T
  · refine ⟨fun _ => range (T.ncard - 1), fun v hv => by simpa using dIn_le_ncard G T hv, ?_⟩
    rintro ⟨f, hf1, hf2⟩
    obtain ⟨t, ht⟩ := hT.1
    have := card_le_card_of_injOn f (s := univ.filter (· ∈ T)) (t := range (T.ncard - 1))
      (fun v hv => Finset.mem_coe.2 (hf1 v (by simpa using hv))) (by
        intro u hu v hv huv
        by_contra hne
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu hv
        exact hf2 u hu v hv (hK u hu v hv hne) huv)
    rw [← ncard_eq_filter, card_range] at this
    have : 0 < T.ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨t, ht⟩
    omega
  by_cases h2c : ∀ x ∈ T, SConn G (T \ {x})
  · have h3 := three_le_of_not_clique hT hK
    rcases hG T le_rfl h3 (fun x hx => connected_iff_sconn.2 (h2c x hx)) with h | ⟨m, hm, ⟨e⟩⟩
    · exact absurd h hK
    · refine ⟨fun _ => {0, 1}, fun v hv => ?_, ?_⟩
      · rw [dIn_cycle e hm (by omega) hv]; simp
      · rintro ⟨f, hf1, hf2⟩
        exact not_two_col_cycle e hm (by omega) f hf1 hf2
  push Not at h2c
  obtain ⟨x, hx, hcut⟩ := h2c
  have hne : (T \ {x}).Nonempty := by
    by_contra hemp
    apply hK
    intro a ha b hb hab
    exfalso
    apply hemp
    by_cases hax : a = x
    · exact ⟨b, hb, fun h => hab (hax.trans (Set.mem_singleton_iff.1 h).symm)⟩
    · exact ⟨a, ha, hax⟩
  obtain ⟨A, B, hAB, hdisj, hAne, hBne, hnoadj, hA, hB⟩ := cut_decomp hT hx hcut hne
  obtain ⟨hdA, hdB, hdx⟩ := dIn_split hAB hdisj hx hnoadj
  have hAT : A ⊆ T \ {x} := hAB ▸ Set.subset_union_left
  have hBT : B ⊆ T \ {x} := hAB ▸ Set.subset_union_right
  have hT1 : insert x A ⊆ T := Set.insert_subset hx (hAT.trans Set.sdiff_subset)
  have hT2 : insert x B ⊆ T := Set.insert_subset hx (hBT.trans Set.sdiff_subset)
  have hlt1 : (insert x A).ncard < n := by
    rw [← hTn]
    apply Set.ncard_lt_ncard _ (Set.toFinite _)
    rw [Set.ssubset_iff_of_subset hT1]
    obtain ⟨b, hb⟩ := hBne
    refine ⟨b, (hBT hb).1, ?_⟩
    rintro (h | h)
    · exact (hBT hb).2 h
    · exact Set.disjoint_left.1 hdisj h hb
  have hlt2 : (insert x B).ncard < n := by
    rw [← hTn]
    apply Set.ncard_lt_ncard _ (Set.toFinite _)
    rw [Set.ssubset_iff_of_subset hT2]
    obtain ⟨a, ha⟩ := hAne
    refine ⟨a, (hAT ha).1, ?_⟩
    rintro (h | h)
    · exact (hAT ha).2 h
    · exact Set.disjoint_left.1 hdisj ha h
  obtain ⟨L1, hL1, hbad1⟩ := ih _ hlt1 _ rfl hA (gallai_mono hG hT1)
  obtain ⟨L2, hL2, hbad2⟩ := ih _ hlt2 _ rfl hB (gallai_mono hG hT2)
  have hinj1 : Function.Injective (fun c : ℕ => 2 * c) := fun a b h => by simp at h; omega
  have hinj2 : Function.Injective (fun c : ℕ => 2 * c + 1) := fun a b h => by simp at h; omega
  refine ⟨fun v => if v = x then (L1 x).image (2 * ·) ∪ (L2 x).image (2 * · + 1)
    else if v ∈ A then (L1 v).image (2 * ·) else (L2 v).image (2 * · + 1), ?_, ?_⟩
  · intro v hv
    by_cases hvx : v = x
    · subst hvx
      simp only [ite_true]
      rw [card_union_of_disjoint, card_image_of_injective _ hinj1,
        card_image_of_injective _ hinj2, hdx]
      · have := hL1 v (Set.mem_insert _ _); have := hL2 v (Set.mem_insert _ _); omega
      · rw [Finset.disjoint_left]
        intro c h1 h2
        obtain ⟨a, -, rfl⟩ := mem_image.1 h1
        obtain ⟨b, -, hb⟩ := mem_image.1 h2
        omega
    · simp only [hvx, ite_false]
      by_cases hvA : v ∈ A
      · simp only [hvA, ite_true]
        rw [card_image_of_injective _ hinj1, hdA v hvA]
        exact hL1 v (Set.mem_insert_of_mem _ hvA)
      · have hvB : v ∈ B := by
          have : v ∈ A ∪ B := hAB ▸ ⟨hv, hvx⟩
          exact this.resolve_left hvA
        simp only [hvA, ite_false]
        rw [card_image_of_injective _ hinj2, hdB v hvB]
        exact hL2 v (Set.mem_insert_of_mem _ hvB)
  · rintro ⟨f, hf1, hf2⟩
    have hf1x := hf1 x hx
    simp only [ite_true] at hf1x
    rcases mem_union.1 hf1x with h | h
    · apply hbad1
      have hev : ∀ u ∈ insert x A, ∃ c ∈ L1 u, f u = 2 * c := by
        intro u hu
        rcases hu with rfl | hu
        · obtain ⟨c, hc, he⟩ := mem_image.1 h; exact ⟨c, hc, he.symm⟩
        · have hux : u ≠ x := fun h' => (hAT hu).2 h'
          have := hf1 u (hAT hu).1
          simp only [hux, hu, ite_false, ite_true] at this
          obtain ⟨c, hc, he⟩ := mem_image.1 this
          exact ⟨c, hc, he.symm⟩
      refine ⟨fun v => f v / 2, fun v hv => ?_, fun u hu v hv huv => ?_⟩
      · obtain ⟨c, hc, he⟩ := hev v hv
        have : f v / 2 = c := by omega
        simpa [this] using hc
      · obtain ⟨c, hc, he⟩ := hev u hu
        obtain ⟨d, hd, hd'⟩ := hev v hv
        have := hf2 u (hT1 hu) v (hT1 hv) huv
        simp only
        omega
    · apply hbad2
      have hod : ∀ u ∈ insert x B, ∃ c ∈ L2 u, f u = 2 * c + 1 := by
        intro u hu
        rcases hu with rfl | hu
        · obtain ⟨c, hc, he⟩ := mem_image.1 h; exact ⟨c, hc, he.symm⟩
        · have hux : u ≠ x := fun h' => (hBT hu).2 h'
          have huA : u ∉ A := fun h' => Set.disjoint_left.1 hdisj h' hu
          have := hf1 u (hBT hu).1
          simp only [hux, huA, ite_false] at this
          obtain ⟨c, hc, he⟩ := mem_image.1 this
          exact ⟨c, hc, he.symm⟩
      refine ⟨fun v => f v / 2, fun v hv => ?_, fun u hu v hv huv => ?_⟩
      · obtain ⟨c, hc, he⟩ := hod v hv
        have : f v / 2 = c := by omega
        simpa [this] using hc
      · obtain ⟨c, hc, he⟩ := hod u hu
        obtain ⟨d, hd, hd'⟩ := hod v hv
        have := hf2 u (hT2 hu) v (hT2 hv) huv
        simp only
        omega

/-- A connected Gallai set in which all degrees are at most `k`, and all vertices other than
`y` have degree exactly `k`, induces a complete graph or an odd cycle. -/
theorem regular_gallai_block (G : SimpleGraph V) (k : ℕ) : ∀ n, ∀ T : Set V, ∀ y : V,
    T.ncard = n → SConn G T → Gallai G T → (∀ v ∈ T, dIn G T v ≤ k) →
    (∀ v ∈ T, v ≠ y → dIn G T v = k) →
    IsCliqueOn G T ∨ ∃ m, Odd m ∧ Nonempty (G.induce T ≃g cycleGraph m) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T y hTn hT hG hle hreg
  by_cases hK : IsCliqueOn G T
  · exact Or.inl hK
  by_cases h2c : ∀ x ∈ T, SConn G (T \ {x})
  · exact hG T le_rfl (three_le_of_not_clique hT hK)
      (fun x hx => connected_iff_sconn.2 (h2c x hx))
  exfalso
  push Not at h2c
  obtain ⟨x, hx, hcut⟩ := h2c
  have hne : (T \ {x}).Nonempty := by
    by_contra hemp
    apply hK
    intro a ha b hb hab
    exfalso
    apply hemp
    by_cases hax : a = x
    · exact ⟨b, hb, fun h => hab (hax.trans (Set.mem_singleton_iff.1 h).symm)⟩
    · exact ⟨a, ha, hax⟩
  obtain ⟨A, B, hAB, hdisj, hAne, hBne, hnoadj, hA, hB⟩ := cut_decomp hT hx hcut hne
  obtain ⟨hdA, hdB, hdx⟩ := dIn_split hAB hdisj hx hnoadj
  have hAT : A ⊆ T \ {x} := hAB ▸ Set.subset_union_left
  have hBT : B ⊆ T \ {x} := hAB ▸ Set.subset_union_right
  have hT1 : insert x A ⊆ T := Set.insert_subset hx (hAT.trans Set.sdiff_subset)
  have hT2 : insert x B ⊆ T := Set.insert_subset hx (hBT.trans Set.sdiff_subset)
  have hxA : x ∉ A := fun h => (hAT h).2 rfl
  have hxB : x ∉ B := fun h => (hBT h).2 rfl
  obtain ⟨a0, ha0, hxa0⟩ := adj_of_sconn_insert hA hAne hxA
  obtain ⟨b0, hb0, hxb0⟩ := adj_of_sconn_insert hB hBne hxB
  have hpos1 : 0 < dIn G (insert x A) x := by
    classical
    rw [dIn_eq]; exact card_pos.2 ⟨a0, by simp [ha0, hxa0]⟩
  have hpos2 : 0 < dIn G (insert x B) x := by
    classical
    rw [dIn_eq]; exact card_pos.2 ⟨b0, by simp [hb0, hxb0]⟩
  have hxk := hle x hx
  by_cases hyA : y ∈ A
  · have hlt2 : (insert x B).ncard < n := by
      rw [← hTn]
      apply Set.ncard_lt_ncard _ (Set.toFinite _)
      rw [Set.ssubset_iff_of_subset hT2]
      refine ⟨a0, (hAT ha0).1, ?_⟩
      rintro (h | h)
      · exact (hAT ha0).2 h
      · exact Set.disjoint_left.1 hdisj ha0 h
    have hblk := ih _ hlt2 (insert x B) x rfl hB (gallai_mono hG hT2) (by
      intro v hv
      rcases hv with rfl | hv
      · omega
      · rw [← hdB v hv]; exact hle v (hBT hv).1) (by
      intro v hv hvx
      rcases hv with rfl | hv
      · exact absurd rfl hvx
      · rw [← hdB v hv]
        exact hreg v (hBT hv).1 (fun h => Set.disjoint_left.1 hdisj (by rw [h]; exact hyA) hv))
    have := block_regular hblk (two_le_ncard_insert hb0 (G.ne_of_adj hxb0))
      (Set.mem_insert x B) (Set.mem_insert_of_mem x hb0)
    rw [← hdB b0 hb0, hreg b0 (hBT hb0).1
      (fun h => Set.disjoint_left.1 hdisj (by rw [h]; exact hyA) hb0)] at this
    omega
  · have hlt1 : (insert x A).ncard < n := by
      rw [← hTn]
      apply Set.ncard_lt_ncard _ (Set.toFinite _)
      rw [Set.ssubset_iff_of_subset hT1]
      refine ⟨b0, (hBT hb0).1, ?_⟩
      rintro (h | h)
      · exact (hBT hb0).2 h
      · exact Set.disjoint_left.1 hdisj h hb0
    have hblk := ih _ hlt1 (insert x A) x rfl hA (gallai_mono hG hT1) (by
      intro v hv
      rcases hv with rfl | hv
      · omega
      · rw [← hdA v hv]; exact hle v (hAT hv).1) (by
      intro v hv hvx
      rcases hv with rfl | hv
      · exact absurd rfl hvx
      · rw [← hdA v hv]
        exact hreg v (hAT hv).1 (fun h => hyA (by rw [← h]; exact hv)))
    have := block_regular hblk (two_le_ncard_insert ha0 (G.ne_of_adj hxa0))
      (Set.mem_insert x A) (Set.mem_insert_of_mem x ha0)
    rw [← hdA a0 ha0, hreg a0 (hAT ha0).1 (fun h => hyA (by rw [← h]; exact ha0))] at this
    omega

end fintype

end ErdosRubinTaylor
