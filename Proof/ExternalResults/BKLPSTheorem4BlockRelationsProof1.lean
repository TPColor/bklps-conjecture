import Proof.ExternalResults.UniqueCutBlocks
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finite.Card
import Mathlib.Tactic.Ring.RingNF

namespace BKLPS.External

open SimpleGraph
open scoped BigOperators

noncomputable section

universe u

/-- The vertex set `V(C_i) ∪ {u}` used inside the proof of BKLPS Theorem 4. -/
def blockExtensionVertexSet
    {V : Type u} [Fintype V] [DecidableEq V]
    (u : V) (C : Set {x : V // x ≠ u}) : Set V :=
  {u} ∪ {x : V | ∃ hx : x ≠ u, (⟨x, hx⟩ : {x : V // x ≠ u}) ∈ C}

noncomputable local instance instFintypeBlockExtensionVertexSet
    {V : Type u} [Fintype V] [DecidableEq V]
    (u : V) (C : Set {x : V // x ≠ u}) :
    Fintype (blockExtensionVertexSet u C) := Fintype.ofFinite _

/-- The graph `G_i = G[V(C_i) ∪ {u}]` from the proof of BKLPS Theorem 4. -/
def blockExtensionGraph
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (C : Set {x : V // x ≠ u}) :
    SimpleGraph (blockExtensionVertexSet u C) :=
  G.induce (blockExtensionVertexSet u C)

/-- The order `m_i` of a block extension. -/
def blockExtensionOrder
    {V : Type u} [Fintype V] [DecidableEq V]
    (u : V) (C : Set {x : V // x ≠ u}) : ℕ := by
  letI : Fintype (blockExtensionVertexSet u C) := Fintype.ofFinite _
  exact Fintype.card (blockExtensionVertexSet u C)

/-- The gap `η(G_i)` of a block extension. -/
def blockExtensionGap
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (u : V) (C : Set {x : V // x ≠ u}) : ℤ := by
  letI : Fintype (blockExtensionVertexSet u C) := Fintype.ofFinite _
  exact szegedWienerGap (blockExtensionGraph G u C)

/-- A block extension consists of one new vertex and the vertices of its
block. -/
def blockExtensionVertexSetEquivOption
    {V : Type u} [Fintype V] [DecidableEq V]
    (u : V) (C : Set {x : V // x ≠ u}) :
    blockExtensionVertexSet u C ≃ Option C where
  toFun x :=
    if hx : x.1 = u then none
    else some ⟨⟨x.1, hx⟩, by
      rcases x.2 with hu | hC
      · exact False.elim (hx (by simpa using hu))
      · exact hC.choose_spec⟩
  invFun x := match x with
    | none => ⟨u, by simp [blockExtensionVertexSet]⟩
    | some c => ⟨c.1.1, Or.inr ⟨c.1.2, c.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    by_cases hx : x.1 = u <;> simp [hx]
  right_inv x := by
    cases x with
    | none => simp
    | some c => simp [c.1.2]

theorem blockExtensionOrder_eq_card_add_one
    {V : Type u} [Fintype V] [DecidableEq V]
    (u : V) (C : Set {x : V // x ≠ u}) :
    blockExtensionOrder u C = Nat.card C + 1 := by
  letI : Fintype (blockExtensionVertexSet u C) := Fintype.ofFinite _
  unfold blockExtensionOrder
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (blockExtensionVertexSetEquivOption u C), Finite.card_option]

/-- Vertices of a block other than the common cut vertex. -/
noncomputable def blockNoncutFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    {u : V} (v : V) (C : Set {x : V // x ≠ u}) : Finset {x : V // x ≠ u} := by
  classical
  exact Finset.univ.filter fun x => x ∈ C ∧ x.1 ≠ v

/-- The second sum in the proof of BKLPS Theorem 4: pair contributions whose
two vertices lie in distinct blocks (with the common cut vertex omitted by
`blockPairContribution`). -/
def blockCrossContribution
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (k : ℕ)
    (blocks : Fin k → Set {x : V // x ≠ u}) : ℤ := by
  classical
  exact ∑ i : Fin k, ∑ j ∈ (Finset.univ.filter fun j : Fin k => i < j),
    ∑ a ∈ blockNoncutFinset v (blocks i),
      ∑ b ∈ blockNoncutFinset v (blocks j),
        pairGap G a.1 b.1

private theorem intTermLeSum {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℤ) (x : α) (hx : x ∈ s)
    (hf : ∀ y ∈ s, 0 ≤ f y) :
    f x ≤ ∑ y ∈ s, f y := by
  rw [← Finset.sum_erase_add _ _ hx]
  have hr : 0 ≤ ∑ y ∈ s.erase x, f y :=
    Finset.sum_nonneg fun y hy => hf y (Finset.mem_of_mem_erase hy)
  omega

/-- The two good edges incident with `u` give two units for one selected
pair of non-cut vertices from distinct blocks. -/
private theorem blockPairSum_ge_two
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (htwo : IsTwoConnected G)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C D : Set {x : V // x ≠ u})
    (hC : IsBlock (deleteVertex G u) C)
    (hD : IsBlock (deleteVertex G u) D) (hCD : C ≠ D) :
    (∑ a ∈ blockNoncutFinset v C,
      ∑ b ∈ blockNoncutFinset v D, pairGap G a.1 b.1) ≥ 2 := by
  classical
  let H := deleteVertex G u
  let vc : {x : V // x ≠ u} := ⟨v, huv.symm⟩
  obtain ⟨a, haC, hav, hua⟩ :=
    exists_u_neighbor_in_block G htwo u v huv hunique C hC
  obtain ⟨b, hbD, hbv, hub⟩ :=
    exists_u_neighbor_in_block G htwo u v huv hunique D hD
  have hab : a ≠ b := by
    intro h
    apply hCD
    exact isBlock_eq_of_two_common H C D hC hD vc a
      (uniqueCut_mem_isBlock H vc hunique C hC)
      (uniqueCut_mem_isBlock H vc hunique D hD)
      haC (h ▸ hbD) (by
        intro hvc
        exact hav (congrArg Subtype.val hvc).symm)
  have hnab : ¬H.Adj a b :=
    not_adj_of_mem_distinct_blocks H vc hunique C D hC hD hCD
      haC hbD (by intro h; exact hav (congrArg Subtype.val h))
      (by intro h; exact hbv (congrArg Subtype.val h))
  have hgain := pairGain_two_of_neighbor_nonedge G htwo.2.1
    u v huv hN a b hab hua hub hnab
  have hnonnegDelete : 0 ≤ pairGap H a b :=
    pairGap_nonneg H (htwo.2.2 u) a b
  change 0 ≤ pairGap (deleteVertex G u) a b at hnonnegDelete
  have hp : pairGap G a.1 b.1 ≥ 2 := by omega
  let A : Finset {x : V // x ≠ u} :=
    blockNoncutFinset v C
  let B : Finset {x : V // x ≠ u} :=
    blockNoncutFinset v D
  have haA : a ∈ A := by simp [A, blockNoncutFinset, haC, hav]
  have hbB : b ∈ B := by simp [B, blockNoncutFinset, hbD, hbv]
  have hinner : pairGap G a.1 b.1 ≤
      ∑ z ∈ B, pairGap G a.1 z.1 :=
    intTermLeSum B (fun z => pairGap G a.1 z.1) b hbB
      (fun z _ => pairGap_nonneg G htwo.2.1 a.1 z.1)
  have houter : (∑ z ∈ B, pairGap G a.1 z.1) ≤
      ∑ x ∈ A, ∑ z ∈ B, pairGap G x.1 z.1 :=
    intTermLeSum A (fun x => ∑ z ∈ B, pairGap G x.1 z.1) a haA
      (fun x _ => Finset.sum_nonneg fun z _ =>
        pairGap_nonneg G htwo.2.1 x.1 z.1)
  change (∑ x ∈ A, ∑ z ∈ B, pairGap G x.1 z.1) ≥ 2
  omega

private theorem finIncreasingPairCount (k : ℕ) :
    (∑ i : Fin k, (Finset.univ.filter fun j : Fin k => i < j).card) =
      Nat.choose k 2 := by
  simp only [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_range_reflect (fun i => i) k]
  rw [Finset.sum_range_id, Nat.choose_two_right]

theorem blockCrossContribution_ge_two_mul_choose
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (htwo : IsTwoConnected G)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (k : ℕ) (blocks : Fin k → Set {x : V // x ≠ u})
    (hinj : Function.Injective blocks)
    (hblocks : ∀ i : Fin k, IsBlock (deleteVertex G u) (blocks i)) :
    blockCrossContribution G u v k blocks ≥ 2 * Nat.choose k 2 := by
  have hsum :
      (∑ i : Fin k,
        ∑ _j ∈ (Finset.univ.filter fun j : Fin k => i < j), (2 : ℤ)) ≤
      blockCrossContribution G u v k blocks := by
    unfold blockCrossContribution
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j hj =>
        blockPairSum_ge_two G u v huv htwo hN hunique
          (blocks i) (blocks j) (hblocks i) (hblocks j)
          (fun h => (ne_of_lt (by simpa using hj)) (hinj h))
  have hconst :
      (∑ i : Fin k,
        ∑ _j ∈ (Finset.univ.filter fun j : Fin k => i < j), (2 : ℤ)) =
      2 * (Nat.choose k 2 : ℤ) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.sum_mul]
    rw [← Nat.cast_sum, finIncreasingPairCount]
    ring
  rw [hconst] at hsum
  exact hsum

/-- Double-counting block membership gives BKLPS relation (2).  The unique
cut vertex occurs in all `k` blocks, every other vertex of `G-u` occurs in
exactly one, and the added vertex `u` occurs once in every extension. -/
theorem sum_blockExtensionOrder_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (k : ℕ) (blocks : Fin k → Set {x : V // x ≠ u})
    (hinj : Function.Injective blocks)
    (h_blocks : ∀ C : Set {x : V // x ≠ u},
      IsBlock (deleteVertex G u) C ↔ ∃ i : Fin k, C = blocks i) :
    (∑ i : Fin k, (blockExtensionOrder u (blocks i) : ℤ)) =
      (Fintype.card V : ℤ) + 2 * ((k : ℤ) - 1) := by
  classical
  let H := deleteVertex G u
  let cut : {x : V // x ≠ u} := ⟨v, huv.symm⟩
  have hblock (i : Fin k) : IsBlock H (blocks i) := by
    exact (h_blocks (blocks i)).mpr ⟨i, rfl⟩
  have hcutMem (i : Fin k) : cut ∈ blocks i :=
    uniqueCut_mem_isBlock H cut hunique (blocks i) (hblock i)
  have huniqueMem (x : {x : V // x ≠ u}) (hx : x ≠ cut) :
      ∃! i : Fin k, x ∈ blocks i := by
    let xx : {z : {x : V // x ≠ u} // z ≠ cut} := ⟨x, hx⟩
    let D : (deleteVertex H cut).ConnectedComponent :=
      (deleteVertex H cut).connectedComponentMk xx
    let C₀ := cutComponentExtension H cut D
    have hC₀ : IsBlock H C₀ := cutComponentExtension_isBlock H cut hunique D
    obtain ⟨i, hi⟩ := (h_blocks C₀).mp hC₀
    have hxi : x ∈ blocks i := by
      rw [← hi]
      exact Or.inr ⟨hx, by
        rw [ConnectedComponent.mem_supp_iff]⟩
    refine ⟨i, hxi, ?_⟩
    intro j hxj
    have heq : blocks i = blocks j :=
      isBlock_eq_of_two_common H (blocks i) (blocks j) (hblock i) (hblock j)
        cut x (hcutMem i) (hcutMem j) hxi hxj hx.symm
    exact (hinj heq).symm
  have hHtwo : 2 ≤ Fintype.card {x : V // x ≠ u} := hunique.1.1
  have hkpos : 1 ≤ k := by
    obtain ⟨C₁, C₂, hC₁, _hC₂, _hne, _hc₁, _hc₂⟩ :=
      exists_two_blocks_of_cutVertex H cut hunique.1
    obtain ⟨i, _hi⟩ := (h_blocks C₁).mp hC₁
    exact Fin.pos_iff_nonempty.mpr ⟨i⟩
  have hinnerCut :
      (∑ i : Fin k, if cut ∈ blocks i then (1 : ℕ) else 0) = k := by
    simp [hcutMem]
  have hinnerOther (x : {x : V // x ≠ u}) (hx : x ≠ cut) :
      (∑ i : Fin k, if x ∈ blocks i then (1 : ℕ) else 0) = 1 := by
    obtain ⟨i, hi, huniq⟩ := huniqueMem x hx
    have hfilter :
        (Finset.univ.filter fun j : Fin k => x ∈ blocks j) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · exact huniq j
      · intro hji
        subst j
        exact hi
    calc
      (∑ j : Fin k, if x ∈ blocks j then (1 : ℕ) else 0) =
          (Finset.univ.filter fun j : Fin k => x ∈ blocks j).card := by simp
      _ = 1 := by rw [hfilter]; simp
  have hsizes : (∑ i : Fin k, Fintype.card (blocks i)) =
      Fintype.card {x : V // x ≠ u} + k - 1 := by
    calc
      (∑ i : Fin k, Fintype.card (blocks i)) =
          ∑ i : Fin k, ∑ x : {x : V // x ≠ u},
            if x ∈ blocks i then (1 : ℕ) else 0 := by
              apply Finset.sum_congr rfl
              intro i _
              simp
      _ = ∑ x : {x : V // x ≠ u}, ∑ i : Fin k,
            if x ∈ blocks i then (1 : ℕ) else 0 := by
              exact Finset.sum_comm
      _ = k + (Fintype.card {x : V // x ≠ u} - 1) := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ cut)]
            rw [hinnerCut]
            have hrest :
                (∑ x ∈ (Finset.univ.erase cut),
                  ∑ i : Fin k, if x ∈ blocks i then (1 : ℕ) else 0) =
                (Finset.univ.erase cut).card := by
              calc
                _ = ∑ _x ∈ (Finset.univ.erase cut), (1 : ℕ) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  exact hinnerOther x (Finset.ne_of_mem_erase hx)
                _ = (Finset.univ.erase cut).card := by simp
            rw [hrest]
            have hcardErase : (Finset.univ.erase cut).card =
                Fintype.card {x : V // x ≠ u} - 1 := by simp
            rw [hcardErase]
            exact Nat.add_comm _ _
      _ = Fintype.card {x : V // x ≠ u} + k - 1 := by omega
  have hordersNat :
      (∑ i : Fin k, blockExtensionOrder u (blocks i)) =
        Fintype.card {x : V // x ≠ u} + 2 * k - 1 := by
    calc
      _ = ∑ i : Fin k, (Fintype.card (blocks i) + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [blockExtensionOrder_eq_card_add_one, Nat.card_eq_fintype_card]
      _ = (∑ i : Fin k, Fintype.card (blocks i)) + k := by
        rw [Finset.sum_add_distrib]
        simp
      _ = (Fintype.card {x : V // x ≠ u} + k - 1) + k := by rw [hsizes]
      _ = Fintype.card {x : V // x ≠ u} + 2 * k - 1 := by omega
  have hHcard : Fintype.card {x : V // x ≠ u} = Fintype.card V - 1 := by
    simpa using Fintype.card_subtype_compl (fun x : V => x = u)
  have hfinalNat :
      Fintype.card {x : V // x ≠ u} + 2 * k - 1 =
        Fintype.card V + 2 * k - 2 := by
    rw [hHcard]
    omega
  rw [← Nat.cast_sum, hordersNat, hfinalNat,
    Nat.cast_sub (by omega : 2 ≤ Fintype.card V + 2 * k)]
  push_cast
  ring

/-- Retraction of the whole graph onto one block extension: vertices outside
the selected component are sent to the common cut vertex. -/
noncomputable def blockExtensionRetraction
    {V : Type u} [Fintype V] [DecidableEq V]
    (u v : V) (huv : u ≠ v) (C : Set {x : V // x ≠ u})
    (hvC : (⟨v, huv.symm⟩ : {x : V // x ≠ u}) ∈ C) :
    V → blockExtensionVertexSet u C := by
  classical
  intro x
  exact if hx : x ∈ blockExtensionVertexSet u C then ⟨x, hx⟩
    else ⟨v, Or.inr ⟨huv.symm, hvC⟩⟩

theorem blockExtensionRetraction_fixed
    {V : Type u} [Fintype V] [DecidableEq V]
    (u v : V) (C : Set {x : V // x ≠ u})
    (huv : u ≠ v) (hvC : (⟨v, huv.symm⟩ : {x : V // x ≠ u}) ∈ C)
    (x : blockExtensionVertexSet u C) :
    blockExtensionRetraction u v huv C hvC x.1 = x := by
  simp [blockExtensionRetraction, x.2]

/-- The retraction maps an edge either to an edge or collapses it.  The only
possible edge leaving a non-cut part of `C` goes to `u`; edges from `u` may
be rerouted to `v` by neighborhood domination. -/
theorem blockExtensionRetraction_adj_or_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u})
    (hC : IsBlock (deleteVertex G u) C) :
    ∀ {a b : V}, G.Adj a b →
      blockExtensionRetraction u v huv C
          (uniqueCut_mem_isBlock (deleteVertex G u) ⟨v, huv.symm⟩
            hunique C hC) a =
        blockExtensionRetraction u v huv C
          (uniqueCut_mem_isBlock (deleteVertex G u) ⟨v, huv.symm⟩
            hunique C hC) b ∨
      (blockExtensionGraph G u C).Adj
        (blockExtensionRetraction u v huv C
          (uniqueCut_mem_isBlock (deleteVertex G u) ⟨v, huv.symm⟩
            hunique C hC) a)
        (blockExtensionRetraction u v huv C
          (uniqueCut_mem_isBlock (deleteVertex G u) ⟨v, huv.symm⟩
            hunique C hC) b) := by
  classical
  let H := deleteVertex G u
  let cut : {x : V // x ≠ u} := ⟨v, huv.symm⟩
  let hvC : cut ∈ C := uniqueCut_mem_isBlock H cut hunique C hC
  let f := blockExtensionRetraction u v huv C hvC
  have huvAdj : G.Adj u v := by
    have hu : u ∈ closedNeighborhood G u := by
      simp [closedNeighborhood, openNeighborhood]
    have hout := hN hu
    have hvu : G.Adj v u := by
      simpa [closedNeighborhood, openNeighborhood, huv, huv.symm] using hout
    exact hvu.symm
  have mixed {a b : V} (hab : G.Adj a b)
      (ha : a ∈ blockExtensionVertexSet u C)
      (hb : b ∉ blockExtensionVertexSet u C) :
      f a = f b ∨ (blockExtensionGraph G u C).Adj (f a) (f b) := by
    by_cases hau : a = u
    · subst a
      right
      simpa [f, blockExtensionRetraction, ha, hb] using huvAdj
    · have haC : (⟨a, hau⟩ : {x : V // x ≠ u}) ∈ C := by
        rcases ha with ha | ha
        · exact False.elim (hau (by simpa using ha))
        · exact ha.choose_spec
      have hbu : b ≠ u := by
        intro hbu
        subst b
        exact hb (Or.inl rfl)
      by_cases hav : a = v
      · left
        subst a
        apply Subtype.ext
        simp [f, blockExtensionRetraction, ha, hb]
      · have habH : H.Adj (⟨a, hau⟩ : {x : V // x ≠ u}) ⟨b, hbu⟩ := hab
        have hbC : (⟨b, hbu⟩ : {x : V // x ≠ u}) ∈ C :=
          adj_mem_isBlock_of_uniqueCut H cut hunique C hC
            haC (by
              intro h
              exact hav (congrArg Subtype.val h)) habH
        exact False.elim (hb (Or.inr ⟨hbu, hbC⟩))
  intro a b hab
  by_cases ha : a ∈ blockExtensionVertexSet u C
  · by_cases hb : b ∈ blockExtensionVertexSet u C
    · right
      simpa [f, blockExtensionRetraction, ha, hb] using hab
    · exact mixed hab ha hb
  · by_cases hb : b ∈ blockExtensionVertexSet u C
    · rcases mixed hab.symm hb ha with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · left
      apply Subtype.ext
      simp [f, blockExtensionRetraction, ha, hb]

/-- All distances between vertices of a block extension are unchanged when
the extension is viewed inside the whole graph. -/
theorem blockExtension_dist_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u})
    (hC : IsBlock (deleteVertex G u) C)
    (a b : blockExtensionVertexSet u C) :
    (blockExtensionGraph G u C).dist a b = G.dist a.1 b.1 := by
  let cut : {x : V // x ≠ u} := ⟨v, huv.symm⟩
  let hvC : cut ∈ C := uniqueCut_mem_isBlock (deleteVertex G u) cut hunique C hC
  let f := blockExtensionRetraction u v huv C hvC
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist a.1 b.1
  let q := Walk.mapAdjOrEq f
    (blockExtensionRetraction_adj_or_eq G u v huv hN hunique C hC) p
  let q' : (blockExtensionGraph G u C).Walk a b :=
    q.copy (blockExtensionRetraction_fixed u v C huv hvC a)
      (blockExtensionRetraction_fixed u v C huv hvC b)
  have hleExt : (blockExtensionGraph G u C).dist a b ≤ G.dist a.1 b.1 := by
    rw [← hp]
    calc
      _ ≤ q'.length := SimpleGraph.dist_le q'
      _ = q.length := by simp [q']
      _ ≤ p.length := by
        dsimp [q]
        exact Walk.length_mapAdjOrEq_le f
          (blockExtensionRetraction_adj_or_eq G u v huv hN hunique C hC) p
  have hreach : (blockExtensionGraph G u C).Reachable a b := ⟨q'⟩
  obtain ⟨r, hr⟩ := hreach.exists_walk_length_eq_dist
  let inclusion : blockExtensionGraph G u C →g G :=
    { toFun := Subtype.val
      map_rel' := fun h => h }
  have hleG : G.dist a.1 b.1 ≤ (blockExtensionGraph G u C).dist a b := by
    rw [← hr, ← r.length_map inclusion]
    exact SimpleGraph.dist_le (r.map inclusion)
  omega

/-- Every block extension is connected.  The retraction used in
`blockExtension_dist_eq` maps a walk in `G` to a walk in the extension. -/
theorem blockExtension_connected
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u})
    (hC : IsBlock (deleteVertex G u) C) :
    (blockExtensionGraph G u C).Connected := by
  refine { preconnected := ?_, nonempty := ⟨⟨u, Or.inl rfl⟩⟩ }
  intro a b
  let cut : {x : V // x ≠ u} := ⟨v, huv.symm⟩
  let hvC : cut ∈ C :=
    uniqueCut_mem_isBlock (deleteVertex G u) cut hunique C hC
  let f := blockExtensionRetraction u v huv C hvC
  obtain ⟨p⟩ := hconn a.1 b.1
  let q := Walk.mapAdjOrEq f
    (blockExtensionRetraction_adj_or_eq G u v huv hN hunique C hC) p
  exact ⟨q.copy (blockExtensionRetraction_fixed u v C huv hvC a)
    (blockExtensionRetraction_fixed u v C huv hvC b)⟩

/-- A good edge inside a block extension remains good in the whole graph. -/
theorem blockExtension_goodEdge_maps
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u})
    (hC : IsBlock (deleteVertex G u) C)
    (a b : blockExtensionVertexSet u C)
    (e : Sym2 (blockExtensionVertexSet u C))
    (he : IsGoodEdgeFor (blockExtensionGraph G u C) a b e) :
    IsGoodEdgeFor G a.1 b.1 (Sym2.map Subtype.val e) := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [Sym2.map_pair_eq]
      simp only [IsGoodEdgeFor, Sym2.lift_mk] at he ⊢
      rcases he with ⟨hxy, hgood⟩
      refine ⟨hxy, ?_⟩
      have hax := blockExtension_dist_eq G hconn u v huv hN hunique C hC a x
      have hay := blockExtension_dist_eq G hconn u v huv hN hunique C hC a y
      have hby := blockExtension_dist_eq G hconn u v huv hN hunique C hC b y
      have hbx := blockExtension_dist_eq G hconn u v huv hN hunique C hC b x
      rcases hgood with hgood | hgood
      · left; omega
      · right; omega

/-- Hence a pair contribution computed in one extension is at most its
contribution in `G`. -/
theorem blockExtension_pairGap_le
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u})
    (hC : IsBlock (deleteVertex G u) C)
    (a b : blockExtensionVertexSet u C) :
    pairGap (blockExtensionGraph G u C) a b ≤ pairGap G a.1 b.1 := by
  classical
  let f : Sym2 (blockExtensionVertexSet u C) → Sym2 V :=
    Sym2.map Subtype.val
  have hf : Function.Injective f := by
    dsimp [f]
    exact Sym2.map.injective Subtype.val_injective
  have hmaps :
      (goodEdgeFinset (blockExtensionGraph G u C) a b).image f ⊆
        goodEdgeFinset G a.1 b.1 := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
    simp only [goodEdgeFinset, Finset.mem_filter,
      SimpleGraph.mem_edgeFinset] at he' ⊢
    exact ⟨by
      induction e' using Sym2.inductionOn with
      | _ x y => exact he'.1,
      blockExtension_goodEdge_maps G hconn u v huv hN hunique C hC a b e' he'.2⟩
  have hcount : goodEdgeCount (blockExtensionGraph G u C) a b ≤
      goodEdgeCount G a.1 b.1 := by
    unfold goodEdgeCount
    rw [← Finset.card_image_iff.mpr hf.injOn]
    exact Finset.card_le_card hmaps
  have hdist := blockExtension_dist_eq G hconn u v huv hN hunique C hC a b
  unfold pairGap
  omega

/-- A pair is a core pair when both of its entries are among the two
vertices `u,v` shared by every block extension. -/
def IsBlockCorePair {V : Type u} (u v : V) (p : Sym2 V) : Prop :=
  ∀ x ∈ p, x = u ∨ x = v

/-- The non-core unordered pairs supported on one block extension. -/
noncomputable def blockInternalPairFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (u v : V) (C : Set {x : V // x ≠ u}) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter fun p =>
    (∀ x ∈ p, x ∈ blockExtensionVertexSet u C) ∧
      ¬IsBlockCorePair u v p

/-- The unordered cross pairs represented by one ordered pair of distinct
blocks. -/
noncomputable def blockCrossPairFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    {u : V} (v : V)
    (C D : Set {x : V // x ≠ u}) : Finset (Sym2 V) := by
  classical
  exact ((blockNoncutFinset v C).product (blockNoncutFinset v D)).image
    fun ab => s(ab.1.1, ab.2.1)

private theorem blockExtension_core_pairGap_zero
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u})
    (hC : IsBlock (deleteVertex G u) C)
    (p : Sym2 (blockExtensionVertexSet u C))
    (hp : IsBlockCorePair u v (Sym2.map Subtype.val p)) :
    pairGapOnPair (blockExtensionGraph G u C) p = 0 := by
  induction p using Sym2.inductionOn with
  | _ a b =>
      have ha : a.1 = u ∨ a.1 = v := hp a.1 (by simp)
      have hb : b.1 = u ∨ b.1 = v := hp b.1 (by simp)
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · have hab : a = b := Subtype.ext (ha.trans hb.symm)
        subst b
        exact pairGap_self _ a
      · have hglobal : pairGap G a.1 b.1 = 0 := by
          simpa [ha, hb] using pairGap_dominated_eq_zero G hconn u v huv hN
        have hle := blockExtension_pairGap_le G hconn u v huv hN hunique
          C hC a b
        have hnonneg := pairGap_nonneg (blockExtensionGraph G u C)
          (blockExtension_connected G hconn u v huv hN hunique C hC) a b
        change pairGap (blockExtensionGraph G u C) a b = 0
        omega
      · have hglobal : pairGap G a.1 b.1 = 0 := by
          change pairGapOnPair G s(a.1, b.1) = 0
          rw [Sym2.eq_swap]
          change pairGap G b.1 a.1 = 0
          simpa [ha, hb] using pairGap_dominated_eq_zero G hconn u v huv hN
        have hle := blockExtension_pairGap_le G hconn u v huv hN hunique
          C hC a b
        have hnonneg := pairGap_nonneg (blockExtensionGraph G u C)
          (blockExtension_connected G hconn u v huv hN hunique C hC) a b
        change pairGap (blockExtensionGraph G u C) a b = 0
        omega
      · have hab : a = b := Subtype.ext (ha.trans hb.symm)
        subst b
        exact pairGap_self _ a

/-- The gap of one block extension is bounded by the global contributions
on the corresponding non-core internal pairs. -/
private theorem blockExtensionGap_le_internalSum
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u})
    (hC : IsBlock (deleteVertex G u) C) :
    blockExtensionGap G u C ≤
      ∑ p ∈ blockInternalPairFinset u v C, pairGapOnPair G p := by
  classical
  let f : Sym2 (blockExtensionVertexSet u C) → Sym2 V :=
    Sym2.map Subtype.val
  let S : Finset (Sym2 (blockExtensionVertexSet u C)) :=
    Finset.univ.filter fun p => ¬IsBlockCorePair u v (f p)
  have hf : Function.Injective f :=
    Sym2.map.injective Subtype.val_injective
  have hzero (p : Sym2 (blockExtensionVertexSet u C)) (hp : p ∉ S) :
      pairGapOnPair (blockExtensionGraph G u C) p = 0 := by
    apply blockExtension_core_pairGap_zero G hconn u v huv hN hunique C hC p
    simpa [S] using hp
  have hrestrict : blockExtensionGap G u C =
      ∑ p ∈ S, pairGapOnPair (blockExtensionGraph G u C) p := by
    unfold blockExtensionGap
    rw [szegedWienerGap_eq_sum_pairGapOnPair]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p _ hp
    exact hzero p hp
  have himage : S.image f = blockInternalPairFinset u v C := by
    ext p
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, S, blockInternalPairFinset]
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨?_, hq⟩
      intro x hx
      rw [Sym2.mem_map] at hx
      obtain ⟨y, _hy, rfl⟩ := hx
      exact y.2
    · rintro ⟨hsupp, hncore⟩
      induction p using Sym2.inductionOn with
      | _ a b =>
          have ha : a ∈ blockExtensionVertexSet u C := hsupp a (by simp)
          have hb : b ∈ blockExtensionVertexSet u C := hsupp b (by simp)
          refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, ?_⟩
          simpa using hncore
          rfl
  rw [hrestrict, ← himage, Finset.sum_image]
  · apply Finset.sum_le_sum
    intro p hp
    induction p using Sym2.inductionOn with
    | _ a b =>
        exact blockExtension_pairGap_le G hconn u v huv hN hunique C hC a b
  · exact fun _ _ _ _ h => hf h

private theorem mem_block_of_mem_blockExtension
    {V : Type u} [Fintype V] [DecidableEq V]
    {u x : V} {C : Set {z : V // z ≠ u}}
    (hxu : x ≠ u) (hx : x ∈ blockExtensionVertexSet u C) :
    (⟨x, hxu⟩ : {z : V // z ≠ u}) ∈ C := by
  rcases hx with hx | hx
  · exact False.elim (hxu (by simpa using hx))
  · exact hx.choose_spec

private theorem block_index_eq_of_common_noncut
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (k : ℕ) (blocks : Fin k → Set {x : V // x ≠ u})
    (hinj : Function.Injective blocks)
    (hblock : ∀ i : Fin k, IsBlock (deleteVertex G u) (blocks i))
    {i j : Fin k} {x : {z : V // z ≠ u}}
    (hxi : x ∈ blocks i) (hxj : x ∈ blocks j)
    (hxv : x.1 ≠ v) : i = j := by
  apply hinj
  exact isBlock_eq_of_two_common (deleteVertex G u) (blocks i) (blocks j)
    (hblock i) (hblock j) ⟨v, huv.symm⟩ x
    (uniqueCut_mem_isBlock (deleteVertex G u) ⟨v, huv.symm⟩
      hunique (blocks i) (hblock i))
    (uniqueCut_mem_isBlock (deleteVertex G u) ⟨v, huv.symm⟩
      hunique (blocks j) (hblock j)) hxi hxj
    (by intro h; exact hxv (congrArg Subtype.val h).symm)

private theorem blockInternalPairFinset_pairwiseDisjoint
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (k : ℕ) (blocks : Fin k → Set {x : V // x ≠ u})
    (hinj : Function.Injective blocks)
    (hblock : ∀ i : Fin k, IsBlock (deleteVertex G u) (blocks i)) :
    (Set.univ : Set (Fin k)).PairwiseDisjoint
      (fun i => blockInternalPairFinset u v (blocks i)) := by
  intro i _ j _ hij
  change Disjoint (blockInternalPairFinset u v (blocks i))
    (blockInternalPairFinset u v (blocks j))
  rw [Finset.disjoint_left]
  intro p hpi hpj
  simp only [blockInternalPairFinset, Finset.mem_filter, Finset.mem_univ,
    true_and] at hpi hpj
  rcases hpi with ⟨hsuppi, hncore⟩
  rcases hpj with ⟨hsuppj, _⟩
  simp only [IsBlockCorePair, not_forall, not_or] at hncore
  obtain ⟨x, hxp, hxu, hxv⟩ := hncore
  exact hij (block_index_eq_of_common_noncut G u v huv hunique k blocks hinj
    hblock
    (mem_block_of_mem_blockExtension hxu (hsuppi x hxp))
    (mem_block_of_mem_blockExtension hxu (hsuppj x hxp)) hxv)

private theorem blockCrossPairMap_injective
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C D : Set {x : V // x ≠ u})
    (hC : IsBlock (deleteVertex G u) C)
    (hD : IsBlock (deleteVertex G u) D) (hCD : C ≠ D) :
    Set.InjOn
      (fun ab : {x : V // x ≠ u} × {x : V // x ≠ u} =>
        s(ab.1.1, ab.2.1))
      ((blockNoncutFinset v C).product (blockNoncutFinset v D)) := by
  intro ab hab cd hcd heq
  have habC : ab.1 ∈ C ∧ ab.1.1 ≠ v := by
    simpa [blockNoncutFinset] using (Finset.mem_product.mp hab).1
  have habD : ab.2 ∈ D ∧ ab.2.1 ≠ v := by
    simpa [blockNoncutFinset] using (Finset.mem_product.mp hab).2
  have hcdC : cd.1 ∈ C ∧ cd.1.1 ≠ v := by
    simpa [blockNoncutFinset] using (Finset.mem_product.mp hcd).1
  have hcdD : cd.2 ∈ D ∧ cd.2.1 ≠ v := by
    simpa [blockNoncutFinset] using (Finset.mem_product.mp hcd).2
  rcases Sym2.eq_iff.mp heq with h | h
  · rcases h with ⟨h₁, h₂⟩
    apply Prod.ext
    · exact Subtype.ext h₁
    · exact Subtype.ext h₂
  · rcases h with ⟨h₁, h₂⟩
    exfalso
    apply hCD
    exact isBlock_eq_of_two_common (deleteVertex G u) C D hC hD
      ⟨v, huv.symm⟩ ab.1
      (uniqueCut_mem_isBlock (deleteVertex G u) ⟨v, huv.symm⟩ hunique C hC)
      (uniqueCut_mem_isBlock (deleteVertex G u) ⟨v, huv.symm⟩ hunique D hD)
      habC.1
      (by
        have he : ab.1 = cd.2 := Subtype.ext h₁
        rw [he]
        exact hcdD.1)
      (by
        intro h
        exact habC.2 (congrArg Subtype.val h).symm)

private theorem blockCrossPair_sum_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C D : Set {x : V // x ≠ u})
    (hC : IsBlock (deleteVertex G u) C)
    (hD : IsBlock (deleteVertex G u) D) (hCD : C ≠ D) :
    (∑ a ∈ blockNoncutFinset v C,
      ∑ b ∈ blockNoncutFinset v D, pairGap G a.1 b.1) =
      ∑ p ∈ blockCrossPairFinset v C D, pairGapOnPair G p := by
  classical
  let A := blockNoncutFinset v C
  let B := blockNoncutFinset v D
  let f := fun ab : {x : V // x ≠ u} × {x : V // x ≠ u} =>
    s(ab.1.1, ab.2.1)
  have hf : Set.InjOn f (A.product B) := by
    simpa [A, B, f] using
      blockCrossPairMap_injective G u v huv hunique C D hC hD hCD
  calc
    (∑ a ∈ blockNoncutFinset v C,
        ∑ b ∈ blockNoncutFinset v D, pairGap G a.1 b.1) =
        ∑ ab ∈ A.product B, pairGapOnPair G (f ab) := by
          exact (Finset.sum_product' A B
            (fun a b => pairGap G a.1 b.1)).symm
    _ = ∑ p ∈ blockCrossPairFinset v C D, pairGapOnPair G p := by
      unfold blockCrossPairFinset
      rw [Finset.sum_image hf]

private theorem blockCrossPairFinset_pairwiseDisjoint
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (k : ℕ) (blocks : Fin k → Set {x : V // x ≠ u})
    (hinj : Function.Injective blocks)
    (hblock : ∀ i : Fin k, IsBlock (deleteVertex G u) (blocks i)) :
    (Set.univ : Set {ij : Fin k × Fin k // ij.1 < ij.2}).PairwiseDisjoint
      (fun ij => blockCrossPairFinset v (blocks ij.1.1) (blocks ij.1.2)) := by
  intro ij _ lm _ hijlm
  change Disjoint
    (blockCrossPairFinset v (blocks ij.1.1) (blocks ij.1.2))
    (blockCrossPairFinset v (blocks lm.1.1) (blocks lm.1.2))
  rw [Finset.disjoint_left]
  intro p hpij hplm
  simp only [blockCrossPairFinset, Finset.mem_image] at hpij hplm
  obtain ⟨ab, hab, habp⟩ := hpij
  obtain ⟨cd, hcd, hcdp⟩ := hplm
  have habA : ab.1 ∈ blocks ij.1.1 ∧ ab.1.1 ≠ v := by
    simpa [blockNoncutFinset] using (Finset.mem_product.mp hab).1
  have habB : ab.2 ∈ blocks ij.1.2 ∧ ab.2.1 ≠ v := by
    simpa [blockNoncutFinset] using (Finset.mem_product.mp hab).2
  have hcdA : cd.1 ∈ blocks lm.1.1 ∧ cd.1.1 ≠ v := by
    simpa [blockNoncutFinset] using (Finset.mem_product.mp hcd).1
  have hcdB : cd.2 ∈ blocks lm.1.2 ∧ cd.2.1 ≠ v := by
    simpa [blockNoncutFinset] using (Finset.mem_product.mp hcd).2
  have heq : s(ab.1.1, ab.2.1) = s(cd.1.1, cd.2.1) := habp.trans hcdp.symm
  rcases Sym2.eq_iff.mp heq with h | h
  · rcases h with ⟨h₁, h₂⟩
    have hi : ij.1.1 = lm.1.1 :=
      block_index_eq_of_common_noncut G u v huv hunique k blocks hinj hblock
        habA.1 (by
          have he : ab.1 = cd.1 := Subtype.ext h₁
          rw [he]
          exact hcdA.1) habA.2
    have hj : ij.1.2 = lm.1.2 :=
      block_index_eq_of_common_noncut G u v huv hunique k blocks hinj hblock
        habB.1 (by
          have he : ab.2 = cd.2 := Subtype.ext h₂
          rw [he]
          exact hcdB.1) habB.2
    exact hijlm (Subtype.ext (Prod.ext hi hj))
  · rcases h with ⟨h₁, h₂⟩
    have hi : ij.1.1 = lm.1.2 :=
      block_index_eq_of_common_noncut G u v huv hunique k blocks hinj hblock
        habA.1 (by
          have he : ab.1 = cd.2 := Subtype.ext h₁
          rw [he]
          exact hcdB.1) habA.2
    have hj : ij.1.2 = lm.1.1 :=
      block_index_eq_of_common_noncut G u v huv hunique k blocks hinj hblock
        habB.1 (by
          have he : ab.2 = cd.1 := Subtype.ext h₂
          rw [he]
          exact hcdA.1) habB.2
    have hij := ij.2
    have hlm := lm.2
    omega

private theorem blockInternal_disjoint_blockCross
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (k : ℕ) (blocks : Fin k → Set {x : V // x ≠ u})
    (hinj : Function.Injective blocks)
    (hblock : ∀ i : Fin k, IsBlock (deleteVertex G u) (blocks i))
    (l : Fin k) (ij : {ij : Fin k × Fin k // ij.1 < ij.2}) :
    Disjoint (blockInternalPairFinset u v (blocks l))
      (blockCrossPairFinset v (blocks ij.1.1) (blocks ij.1.2)) := by
  rw [Finset.disjoint_left]
  intro p hpint hpcross
  simp only [blockInternalPairFinset, Finset.mem_filter, Finset.mem_univ,
    true_and] at hpint
  rcases hpint with ⟨hsupp, _⟩
  simp only [blockCrossPairFinset, Finset.mem_image] at hpcross
  obtain ⟨ab, hab, rfl⟩ := hpcross
  have habprod := Finset.mem_product.mp hab
  have haBlock : ab.1 ∈ blocks ij.1.1 ∧ ab.1.1 ≠ v := by
    simpa [blockNoncutFinset] using habprod.1
  have hbBlock : ab.2 ∈ blocks ij.1.2 ∧ ab.2.1 ≠ v := by
    simpa [blockNoncutFinset] using habprod.2
  have haExt : ab.1.1 ∈ blockExtensionVertexSet u (blocks l) :=
    hsupp ab.1.1 (by simp)
  have hbExt : ab.2.1 ∈ blockExtensionVertexSet u (blocks l) :=
    hsupp ab.2.1 (by simp)
  have hli : l = ij.1.1 :=
    block_index_eq_of_common_noncut G u v huv hunique k blocks hinj hblock
      (mem_block_of_mem_blockExtension ab.1.2 haExt)
      haBlock.1 haBlock.2
  have hlj : l = ij.1.2 :=
    block_index_eq_of_common_noncut G u v huv hunique k blocks hinj hblock
      (mem_block_of_mem_blockExtension ab.2.2 hbExt)
      hbBlock.1 hbBlock.2
  have := ij.2
  omega

/-- The two displayed block-decomposition relations extracted from the proof
of BKLPS Theorem 4. -/
theorem bklpsTheorem4BlockRelationsCore
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (u v : V) (h_distinct : u ≠ v)
    (h_two_connected : IsTwoConnected G)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_unique_cut : IsUniqueCutVertex (deleteVertex G u) ⟨v, h_distinct.symm⟩)
    (k : ℕ) (h_k : k ≥ 2)
    (blocks : Fin k → Set {x : V // x ≠ u})
    (h_blocks_injective : Function.Injective blocks)
    (h_blocks : ∀ C : Set {x : V // x ≠ u},
      IsBlock (deleteVertex G u) C ↔ ∃ i : Fin k, C = blocks i) :
    szegedWienerGap G ≥
        (∑ i : Fin k, blockExtensionGap G u (blocks i)) +
          blockCrossContribution G u v k blocks ∧
      blockCrossContribution G u v k blocks ≥ 2 * Nat.choose k 2 ∧
      (∑ i : Fin k, (blockExtensionOrder u (blocks i) : ℤ)) =
        (Fintype.card V : ℤ) + 2 * ((k : ℤ) - 1) := by
  have hblock (i : Fin k) : IsBlock (deleteVertex G u) (blocks i) :=
    (h_blocks (blocks i)).mpr ⟨i, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · classical
    let internal := fun i : Fin k =>
      blockInternalPairFinset u v (blocks i)
    let cross := fun i j : Fin k =>
      blockCrossPairFinset v (blocks i) (blocks j)
    let crossFor := fun i : Fin k =>
      (Finset.univ.filter fun j : Fin k => i < j).biUnion (cross i)
    let internalAll := (Finset.univ : Finset (Fin k)).biUnion internal
    let crossAll := (Finset.univ : Finset (Fin k)).biUnion crossFor
    have hInternalPW :
        ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint internal := by
      simpa [internal] using
        blockInternalPairFinset_pairwiseDisjoint G u v h_distinct h_unique_cut
          k blocks h_blocks_injective hblock
    have hCrossGlobal :=
      blockCrossPairFinset_pairwiseDisjoint G u v h_distinct h_unique_cut
        k blocks h_blocks_injective hblock
    have hCrossInnerPW (i : Fin k) :
        ((Finset.univ.filter fun j : Fin k => i < j : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
          (cross i) := by
      intro j hj l hl hjl
      change Disjoint (cross i j) (cross i l)
      let ij : {q : Fin k × Fin k // q.1 < q.2} :=
        ⟨(i, j), by simpa using hj⟩
      let il : {q : Fin k × Fin k // q.1 < q.2} :=
        ⟨(i, l), by simpa using hl⟩
      have hne : ij ≠ il := by
        intro h
        apply hjl
        exact congrArg (fun q => q.1.2) h
      have hd := hCrossGlobal (Set.mem_univ ij) (Set.mem_univ il) hne
      simpa [cross, ij, il] using hd
    have hCrossOuterPW :
        ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint crossFor := by
      intro i _ l _ hil
      change Disjoint (crossFor i) (crossFor l)
      rw [Finset.disjoint_left]
      intro p hpi hpl
      rcases Finset.mem_biUnion.mp hpi with ⟨j, hj, hpij⟩
      rcases Finset.mem_biUnion.mp hpl with ⟨m, hm, hplm⟩
      let ij : {q : Fin k × Fin k // q.1 < q.2} :=
        ⟨(i, j), by simpa using hj⟩
      let lm : {q : Fin k × Fin k // q.1 < q.2} :=
        ⟨(l, m), by simpa using hm⟩
      have hne : ij ≠ lm := by
        intro h
        apply hil
        exact congrArg (fun q => q.1.1) h
      have hd := hCrossGlobal (Set.mem_univ ij) (Set.mem_univ lm) hne
      exact (Finset.disjoint_left.mp (by simpa [cross, ij, lm] using hd)) hpij hplm
    have hInternalEq :
        (∑ p ∈ internalAll, pairGapOnPair G p) =
          ∑ i : Fin k, ∑ p ∈ internal i, pairGapOnPair G p := by
      simpa [internalAll] using
        (Finset.sum_biUnion hInternalPW (f := pairGapOnPair G))
    have hCrossForEq (i : Fin k) :
        (∑ p ∈ crossFor i, pairGapOnPair G p) =
          ∑ j ∈ (Finset.univ.filter fun j : Fin k => i < j),
            ∑ p ∈ cross i j, pairGapOnPair G p := by
      simpa [crossFor] using
        (Finset.sum_biUnion (hCrossInnerPW i) (f := pairGapOnPair G))
    have hCrossAllEq :
        (∑ p ∈ crossAll, pairGapOnPair G p) =
          ∑ i : Fin k, ∑ p ∈ crossFor i, pairGapOnPair G p := by
      simpa [crossAll] using
        (Finset.sum_biUnion hCrossOuterPW (f := pairGapOnPair G))
    have hCrossEq : blockCrossContribution G u v k blocks =
        ∑ p ∈ crossAll, pairGapOnPair G p := by
      rw [hCrossAllEq]
      unfold blockCrossContribution
      apply Finset.sum_congr rfl
      intro i _
      rw [hCrossForEq i]
      apply Finset.sum_congr rfl
      intro j hj
      exact blockCrossPair_sum_eq G u v h_distinct h_unique_cut
        (blocks i) (blocks j) (hblock i) (hblock j)
        (fun h => (ne_of_lt (by simpa using hj)) (h_blocks_injective h))
    have hInternalCross : Disjoint internalAll crossAll := by
      rw [Finset.disjoint_left]
      intro p hpint hpcross
      rcases Finset.mem_biUnion.mp hpint with ⟨i, _hi, hpi⟩
      rcases Finset.mem_biUnion.mp hpcross with ⟨j, _hj, hpj⟩
      rcases Finset.mem_biUnion.mp hpj with ⟨l, hl, hpjl⟩
      let jl : {q : Fin k × Fin k // q.1 < q.2} :=
        ⟨(j, l), by simpa using hl⟩
      exact (Finset.disjoint_left.mp
        (blockInternal_disjoint_blockCross G u v h_distinct h_unique_cut
          k blocks h_blocks_injective hblock i jl)) hpi (by simpa [cross, jl] using hpjl)
    have hLocal :
        (∑ i : Fin k, blockExtensionGap G u (blocks i)) ≤
          ∑ p ∈ internalAll, pairGapOnPair G p := by
      rw [hInternalEq]
      exact Finset.sum_le_sum fun i _ =>
        blockExtensionGap_le_internalSum G h_two_connected.2.1 u v
          h_distinct h_neighborhood h_unique_cut (blocks i) (hblock i)
    have hPieces :
        (∑ p ∈ internalAll, pairGapOnPair G p) +
            (∑ p ∈ crossAll, pairGapOnPair G p) =
          ∑ p ∈ internalAll ∪ crossAll, pairGapOnPair G p := by
      exact (Finset.sum_union hInternalCross).symm
    have hRest :
        (∑ p ∈ internalAll ∪ crossAll, pairGapOnPair G p) ≤
          ∑ p : Sym2 V, pairGapOnPair G p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro p _ _
      induction p using Sym2.inductionOn with
      | _ a b => exact pairGap_nonneg G h_two_connected.2.1 a b
    rw [szegedWienerGap_eq_sum_pairGapOnPair, hCrossEq]
    omega
  · exact blockCrossContribution_ge_two_mul_choose G u v h_distinct
      h_two_connected h_neighborhood h_unique_cut k blocks
      h_blocks_injective hblock
  · exact sum_blockExtensionOrder_eq G u v h_distinct h_unique_cut
      k blocks h_blocks_injective h_blocks

/-- The internal and cross-block contributions lie below the total gap. -/
theorem bklpsTheorem4BlockRelationsProof1
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (h_distinct : u ≠ v)
    (h_two_connected : IsTwoConnected G)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_unique_cut : IsUniqueCutVertex (deleteVertex G u) ⟨v, h_distinct.symm⟩)
    (k : ℕ) (h_k : k ≥ 2) (blocks : Fin k → Set {x : V // x ≠ u})
    (h_blocks_injective : Function.Injective blocks)
    (h_blocks : ∀ C : Set {x : V // x ≠ u},
      IsBlock (deleteVertex G u) C ↔ ∃ i : Fin k, C = blocks i) :
    szegedWienerGap G ≥
      (∑ i : Fin k, blockExtensionGap G u (blocks i)) +
        blockCrossContribution G u v k blocks := by
  exact (bklpsTheorem4BlockRelationsCore G u v h_distinct h_two_connected
    h_neighborhood h_unique_cut k h_k blocks h_blocks_injective h_blocks).1

end

end BKLPS.External
