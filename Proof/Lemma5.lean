import Proof.ExternalResults.UniqueCutBlocks
import Proof.Definitions
import Proof.ExternalResults.BKLPSLemma7GoodsLowerBounds

/-! Witness construction for Lemma 5 (`w₁,w₂,x₁,x₂`). -/

namespace BKLPS

open SimpleGraph

noncomputable section

universe u

/-- The extra edge `uw` used in the manuscript is outside a geodesic in
`G-u` and hence raises the pair contribution by one. -/
private theorem pairGap_ge_one_of_cross_attachment
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (a w b : {x : V // x ≠ u})
    (haw : G.Adj a.1 w.1) (huw : G.Adj u w.1) (hub : G.Adj u b.1)
    (hnua : ¬G.Adj u a.1) (hwb : w.1 ≠ b.1)
    (hnwb : ¬G.Adj w.1 b.1) :
    pairGap G a.1 b.1 ≥ 1 := by
  classical
  let H := deleteVertex G u
  have hHconn := External.deleteVertex_connected_of_closedNeighborhood_subset
    G hconn u v huv hN
  obtain ⟨pH, hpH⟩ := hHconn.exists_walk_length_eq_dist a b
  let inclusion : H →g G :=
    { toFun := Subtype.val
      map_rel' := fun h => h }
  let p := pH.map inclusion
  have hdist := External.deleteVertex_dist_eq_of_closedNeighborhood_subset
    G hconn u v huv hN a b
  have hp : p.length = G.dist a.1 b.1 := by
    rw [Walk.length_map, hpH]
    exact hdist
  let e : Sym2 V := s(u, w.1)
  have hgood : IsGoodEdgeFor G a.1 b.1 e := by
    change G.Adj u w.1 ∧
      ((G.dist a.1 u < G.dist a.1 w.1 ∧
          G.dist b.1 w.1 < G.dist b.1 u) ∨
       (G.dist a.1 w.1 < G.dist a.1 u ∧
          G.dist b.1 u < G.dist b.1 w.1))
    refine ⟨huw, Or.inr ?_⟩
    have haune : a.1 ≠ u := a.2
    have hbwn : b.1 ≠ w.1 := Ne.symm hwb
    rw [dist_eq_one_iff_adj.mpr haw,
      dist_eq_one_iff_adj.mpr hub.symm]
    exact ⟨hconn.one_lt_dist_of_ne_of_not_adj haune (fun h => hnua h.symm),
      hconn.one_lt_dist_of_ne_of_not_adj hbwn (fun h => hnwb h.symm)⟩
  have hextra : e ∉ p.edges := by
    intro he
    have huSupport : u ∈ p.support := p.fst_mem_support_of_mem_edges he
    change u ∈ (pH.map inclusion).support at huSupport
    rw [Walk.support_map] at huSupport
    obtain ⟨z, hz, hzu⟩ := List.mem_map.mp huSupport
    exact z.2 (by simpa [inclusion] using hzu)
  exact External.pairGap_ge_one_of_extra_goodEdge G hconn a.1 b.1 p hp e hgood hextra

/-- The three distinct cross-block pairs with contributions `2,1,1` whose
existence is the main combinatorial claim in Lemma 5. -/
theorem lemma5Proof1
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_two_connected : IsTwoConnected G)
    (u v : V) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete_not_two_connected : ¬IsTwoConnected (deleteVertex G u))
    (h_unique_cut : IsUniqueCutVertex (deleteVertex G u) ⟨v, h_distinct.symm⟩)
    (C₁ C₂ : Set {x : V // x ≠ u})
    (h_C₁ : IsBlock (deleteVertex G u) C₁ ∧
      letI : Fintype C₁ := Fintype.ofFinite C₁
      IsTwoConnected ((deleteVertex G u).induce C₁))
    (h_C₂ : IsBlock (deleteVertex G u) C₂ ∧
      letI : Fintype C₂ := Fintype.ofFinite C₂
      IsTwoConnected ((deleteVertex G u).induce C₂))
    (h_blocks_distinct : C₁ ≠ C₂) :
    ∃ w₁ x₁ w₂ x₂ : {x : V // x ≠ u},
      w₁ ∈ C₁ ∧ w₁.1 ≠ v ∧ G.Adj u w₁.1 ∧
      w₂ ∈ C₂ ∧ w₂.1 ≠ v ∧ G.Adj u w₂.1 ∧
      x₁ ∈ C₁ ∧ x₁.1 ≠ v ∧ x₁ ≠ w₁ ∧ G.Adj x₁.1 w₁.1 ∧
      x₂ ∈ C₂ ∧ x₂.1 ≠ v ∧ x₂ ≠ w₂ ∧ G.Adj x₂.1 w₂.1 ∧
      pairGap G w₁.1 w₂.1 ≥ 2 ∧
      pairGap G x₁.1 w₂.1 ≥ 1 ∧ pairGap G w₁.1 x₂.1 ≥ 1 := by
  classical
  let H := deleteVertex G u
  let vc : {x : V // x ≠ u} := ⟨v, h_distinct.symm⟩
  have hC₁block : IsBlock H C₁ := by simpa [H] using h_C₁.1
  have hC₂block : IsBlock H C₂ := by simpa [H] using h_C₂.1
  have hC₁two :
      letI : Fintype C₁ := Fintype.ofFinite C₁
      IsTwoConnected (H.induce C₁) := by simpa [H] using h_C₁.2
  have hC₂two :
      letI : Fintype C₂ := Fintype.ofFinite C₂
      IsTwoConnected (H.induce C₂) := by simpa [H] using h_C₂.2
  obtain ⟨w₁, hw₁C, hw₁v, huw₁⟩ :=
    External.exists_u_neighbor_in_twoConnectedBlock G h_two_connected u v
      h_distinct h_unique_cut C₁ hC₁block hC₁two
  obtain ⟨w₂, hw₂C, hw₂v, huw₂⟩ :=
    External.exists_u_neighbor_in_twoConnectedBlock G h_two_connected u v
      h_distinct h_unique_cut C₂ hC₂block hC₂two
  have hw₁w₂ : w₁ ≠ w₂ := by
    intro h
    apply h_blocks_distinct
    exact External.isBlock_eq_of_two_common H C₁ C₂ hC₁block hC₂block vc w₁
      (External.uniqueCut_mem_isBlock H vc h_unique_cut C₁ hC₁block)
      (External.uniqueCut_mem_isBlock H vc h_unique_cut C₂ hC₂block)
      hw₁C (h ▸ hw₂C) (by
        intro hvw
        exact hw₁v (Eq.symm (congrArg Subtype.val hvw)))
  have hn₁₂ : ¬H.Adj w₁ w₂ :=
      External.not_adj_of_mem_distinct_blocks H vc h_unique_cut C₁ C₂
      hC₁block hC₂block h_blocks_distinct hw₁C hw₂C
      (by intro h; exact hw₁v (congrArg Subtype.val h))
      (by intro h; exact hw₂v (congrArg Subtype.val h))
  have hpair₁₂ : pairGap G w₁.1 w₂.1 ≥ 2 := by
    have hgain := External.pairGain_two_of_neighbor_nonedge G
      h_two_connected.2.1 u v h_distinct h_neighborhood
      w₁ w₂ hw₁w₂ huw₁ huw₂ hn₁₂
    have hnonneg : 0 ≤ pairGap (deleteVertex G u) w₁ w₂ :=
      External.pairGap_nonneg (deleteVertex G u) (h_two_connected.2.2 u) w₁ w₂
    omega
  have choose_x (C : Set {x : V // x ≠ u})
      (hCblock : IsBlock H C)
      (hCtwo :
        letI : Fintype C := Fintype.ofFinite C
        IsTwoConnected (H.induce C))
      (w : {x : V // x ≠ u}) (hwC : w ∈ C) (hwv : w.1 ≠ v) :
      ∃ x : {x : V // x ≠ u},
        x ∈ C ∧ x.1 ≠ v ∧ x ≠ w ∧ G.Adj x.1 w.1 := by
    letI : Fintype C := Fintype.ofFinite C
    change IsTwoConnected (H.induce C) at hCtwo
    let wC : C := ⟨w, hwC⟩
    obtain ⟨r, s, hrs, hwr, hws⟩ :=
      External.exists_two_neighbors_of_twoConnected (H.induce C) hCtwo wC
    by_cases hrv : r.1.1 = v
    · refine ⟨s.1, s.2, ?_, ?_, hws.symm⟩
      · intro hsv
        apply hrs
        apply Subtype.ext
        apply Subtype.ext
        exact hrv.trans hsv.symm
      · intro hsw
        exact hws.ne (by apply Subtype.ext; exact hsw.symm)
    · refine ⟨r.1, r.2, hrv, ?_, hwr.symm⟩
      intro hrw
      exact hwr.ne (by apply Subtype.ext; exact hrw.symm)
  obtain ⟨x₁, hx₁C, hx₁v, hx₁w, hx₁wAdj⟩ :=
    choose_x C₁ hC₁block hC₁two w₁ hw₁C hw₁v
  obtain ⟨x₂, hx₂C, hx₂v, hx₂w, hx₂wAdj⟩ :=
    choose_x C₂ hC₂block hC₂two w₂ hw₂C hw₂v
  have cross_one (A B : Set {x : V // x ≠ u})
      (hAblock : IsBlock H A) (hBblock : IsBlock H B) (hAB : A ≠ B)
      (x w₁ w₂ : {x : V // x ≠ u})
      (hxC : x ∈ A) (hw₁C : w₁ ∈ A) (hw₂C : w₂ ∈ B)
      (hxv : x.1 ≠ v) (hw₁v : w₁.1 ≠ v) (hw₂v : w₂.1 ≠ v)
      (hxw₁ : G.Adj x.1 w₁.1) (huw₁ : G.Adj u w₁.1)
      (huw₂ : G.Adj u w₂.1) : pairGap G x.1 w₂.1 ≥ 1 := by
    have hxw₂ : x ≠ w₂ := by
      intro h
      apply hAB
      exact External.isBlock_eq_of_two_common H A B hAblock hBblock vc x
        (External.uniqueCut_mem_isBlock H vc h_unique_cut A hAblock)
        (External.uniqueCut_mem_isBlock H vc h_unique_cut B hBblock)
        hxC (h ▸ hw₂C) (by
          intro hvc
          exact hxv (Eq.symm (congrArg Subtype.val hvc)))
    have hnxw₂ : ¬H.Adj x w₂ :=
      External.not_adj_of_mem_distinct_blocks H vc h_unique_cut A B
        hAblock hBblock hAB hxC hw₂C
        (by intro h; exact hxv (congrArg Subtype.val h))
        (by intro h; exact hw₂v (congrArg Subtype.val h))
    by_cases hux : G.Adj u x.1
    · have hgain := External.pairGain_two_of_neighbor_nonedge G
        h_two_connected.2.1 u v h_distinct h_neighborhood
        x w₂ hxw₂ hux huw₂ hnxw₂
      have hnonneg : 0 ≤ pairGap (deleteVertex G u) x w₂ :=
        External.pairGap_nonneg (deleteVertex G u) (h_two_connected.2.2 u) x w₂
      omega
    · have hnww : ¬G.Adj w₁.1 w₂.1 :=
        External.not_adj_of_mem_distinct_blocks H vc h_unique_cut A B
          hAblock hBblock hAB hw₁C hw₂C
          (by intro h; exact hw₁v (congrArg Subtype.val h))
          (by intro h; exact hw₂v (congrArg Subtype.val h))
      have hww : w₁.1 ≠ w₂.1 := by
        intro h
        apply hAB
        exact External.isBlock_eq_of_two_common H A B hAblock hBblock vc w₁
          (External.uniqueCut_mem_isBlock H vc h_unique_cut A hAblock)
          (External.uniqueCut_mem_isBlock H vc h_unique_cut B hBblock)
          hw₁C (by
            have : w₁ = w₂ := Subtype.ext h
            exact this ▸ hw₂C)
          (by intro hvc; exact hw₁v (Eq.symm (congrArg Subtype.val hvc)))
      exact pairGap_ge_one_of_cross_attachment G h_two_connected.2.1
        u v h_distinct h_neighborhood x w₁ w₂ hxw₁ huw₁ huw₂ hux hww hnww
  have hcross₁ := cross_one C₁ C₂ hC₁block hC₂block h_blocks_distinct
    x₁ w₁ w₂ hx₁C hw₁C hw₂C hx₁v hw₁v hw₂v
    hx₁wAdj huw₁ huw₂
  have hcross₂ : pairGap G w₁.1 x₂.1 ≥ 1 := by
    have h := cross_one C₂ C₁ hC₂block hC₁block h_blocks_distinct.symm x₂ w₂ w₁
      hx₂C hw₂C hw₁C hx₂v hw₂v hw₁v hx₂wAdj huw₂ huw₁
    simpa [show pairGap G x₂.1 w₁.1 = pairGap G w₁.1 x₂.1 by
      change pairGapOnPair G s(x₂.1, w₁.1) =
        pairGapOnPair G s(w₁.1, x₂.1)
      rw [Sym2.eq_swap]] using h
  exact ⟨w₁, x₁, w₂, x₂, hw₁C, hw₁v, huw₁,
    hw₂C, hw₂v, huw₂, hx₁C, hx₁v, hx₁w, hx₁wAdj,
    hx₂C, hx₂v, hx₂w, hx₂wAdj, hpair₁₂, hcross₁, hcross₂⟩

end

end BKLPS


/-!
Main route of Lemma 5.

2-connectivity supplies a neighbor `w_i` of `u` in each block `C_i` away
from the common cut vertex `v`.  Inside each 2-connected block choose a
second vertex `x_i`, adjacent to `w_i` and different from `v`.  Since
`N[u]⊆N[v]` and the `w_i` lie in different blocks,
`pairGap G w₁ w₂ ≥ 2`.

For `i≠j`, if `x_i` is adjacent to `u`, the same domination argument gives
`pairGap G x_i w_j ≥ 2`.  Otherwise `w_i u` is an extra good edge beyond a
shortest `x_i`--`w_j` path avoiding `u`, so the contribution is at least
one.  The three distinct pairs `{w₁,w₂}`, `{x₁,w₂}`, and `{w₁,x₂}`
therefore contribute at least `2+1+1=4`; nonnegativity lets us embed those
three terms into the full double sum.
-/

namespace BKLPS

open SimpleGraph
open scoped BigOperators

noncomputable section

universe u

/-- A 2-connected block, used in the statement of Lemma 5. -/
def IsTwoConnectedBlock
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Set V) : Prop :=
  IsBlock G C ∧
    letI : Fintype C := Fintype.ofFinite C
    IsTwoConnected (G.induce C)

/-- The double sum in Lemma 5 over vertices in two blocks other than `v`. -/
def blockPairContribution
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (u v : V) (C₁ C₂ : Set {x : V // x ≠ u}) : ℤ := by
  classical
  exact ∑ a ∈ (Finset.univ.filter fun a : {x : V // x ≠ u} => a ∈ C₁ ∧ a.1 ≠ v),
    ∑ b ∈ (Finset.univ.filter fun b : {x : V // x ≠ u} => b ∈ C₂ ∧ b.1 ≠ v),
      pairGap G a.1 b.1

private theorem intSumNonneg {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℤ) (hf : ∀ x ∈ s, 0 ≤ f x) :
    0 ≤ ∑ x ∈ s, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
      simp only [Finset.sum_insert hxs]
      have hx := hf x (by simp)
      have hs := ih (fun y hy => hf y (by simp [hy]))
      omega

private theorem intTermLeSum {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℤ) (x : α) (hx : x ∈ s)
    (hf : ∀ y ∈ s, 0 ≤ f y) :
    f x ≤ ∑ y ∈ s, f y := by
  rw [← Finset.sum_erase_add _ _ hx]
  have hr : 0 ≤ ∑ y ∈ s.erase x, f y :=
    intSumNonneg (s.erase x) f
      (fun y hy => hf y (Finset.mem_of_mem_erase hy))
  omega

private theorem intTwoTermsLeSum {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℤ) (x y : α)
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    (hf : ∀ z ∈ s, 0 ≤ f z) :
    f x + f y ≤ ∑ z ∈ s, f z := by
  rw [← Finset.sum_erase_add _ _ hx]
  have hy' : y ∈ s.erase x := by simp [hy, hxy.symm]
  have hle : f y ≤ ∑ z ∈ s.erase x, f z :=
    intTermLeSum (s.erase x) f y hy'
      (fun z hz => hf z (Finset.mem_of_mem_erase hz))
  omega

/-- **Lemma 5.** Distinct 2-connected blocks on opposite sides of the unique
cut vertex contribute at least four. -/
theorem lemma5
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_two_connected : IsTwoConnected G)
    (u v : V) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete_not_two_connected : ¬IsTwoConnected (deleteVertex G u))
    (h_unique_cut : IsUniqueCutVertex (deleteVertex G u) ⟨v, h_distinct.symm⟩)
    (C₁ C₂ : Set {x : V // x ≠ u})
    (h_C₁ : IsTwoConnectedBlock (deleteVertex G u) C₁)
    (h_C₂ : IsTwoConnectedBlock (deleteVertex G u) C₂)
    (h_blocks_distinct : C₁ ≠ C₂) :
    blockPairContribution G u v C₁ C₂ ≥ 4 := by
  /-
  Choose neighbors `wᵢ` of `u` in each block and then a neighbor `xᵢ≠v` of
  `wᵢ` inside that block.  The dominated-neighborhood hypothesis gives
  `η_G(w₁,w₂)≥2`.  For distinct `i,j`, either `xᵢ` is adjacent to `u`, giving
  `η_G(xᵢ,wⱼ)≥2`, or `wᵢu` is one additional good edge beyond a shortest path,
  giving `η_G(xᵢ,wⱼ)≥1`.  The three distinct pairs therefore contribute at
  least `2+1+1` to the double sum.
  -/
  classical
  obtain ⟨w₁, x₁, w₂, x₂, hw₁C, hw₁v, huw₁,
    hw₂C, hw₂v, huw₂, hx₁C, hx₁v, hx₁w₁, hx₁w₁adj,
    hx₂C, hx₂v, hx₂w₂, hx₂w₂adj, hww, hxw, hwx⟩ :=
    lemma5Proof1 G h_two_connected u v h_distinct h_neighborhood
      h_delete_not_two_connected h_unique_cut C₁ C₂ h_C₁ h_C₂ h_blocks_distinct
  let A : Finset {x : V // x ≠ u} :=
    Finset.univ.filter fun a => a ∈ C₁ ∧ a.1 ≠ v
  let B : Finset {x : V // x ≠ u} :=
    Finset.univ.filter fun b => b ∈ C₂ ∧ b.1 ≠ v
  have hw₁A : w₁ ∈ A := by simp [A, hw₁C, hw₁v]
  have hx₁A : x₁ ∈ A := by simp [A, hx₁C, hx₁v]
  have hw₂B : w₂ ∈ B := by simp [B, hw₂C, hw₂v]
  have hx₂B : x₂ ∈ B := by simp [B, hx₂C, hx₂v]
  have hnonneg (a b : {x : V // x ≠ u}) : 0 ≤ pairGap G a.1 b.1 :=
    External.pairGap_nonneg G h_two_connected.2.1 a.1 b.1
  have hinner_w₁ :
      pairGap G w₁.1 w₂.1 + pairGap G w₁.1 x₂.1 ≤
        ∑ b ∈ B, pairGap G w₁.1 b.1 :=
    intTwoTermsLeSum B (fun b => pairGap G w₁.1 b.1) w₂ x₂
      hw₂B hx₂B hx₂w₂.symm (fun b _ => hnonneg w₁ b)
  have hinner_x₁ :
      pairGap G x₁.1 w₂.1 ≤ ∑ b ∈ B, pairGap G x₁.1 b.1 :=
    intTermLeSum B (fun b => pairGap G x₁.1 b.1) w₂ hw₂B
      (fun b _ => hnonneg x₁ b)
  have houter :
      (∑ b ∈ B, pairGap G w₁.1 b.1) +
          (∑ b ∈ B, pairGap G x₁.1 b.1) ≤
        ∑ a ∈ A, ∑ b ∈ B, pairGap G a.1 b.1 := by
    apply intTwoTermsLeSum A
      (fun a => ∑ b ∈ B, pairGap G a.1 b.1) w₁ x₁
      hw₁A hx₁A hx₁w₁.symm
    intro a ha
    exact intSumNonneg B (fun b => pairGap G a.1 b.1)
      (fun b hb => hnonneg a b)
  unfold blockPairContribution
  change (∑ a ∈ A, ∑ b ∈ B, pairGap G a.1 b.1) ≥ 4
  calc
    (4 : ℤ) ≤ pairGap G w₁.1 w₂.1 + pairGap G x₁.1 w₂.1 +
        pairGap G w₁.1 x₂.1 := by omega
    _ ≤ (∑ b ∈ B, pairGap G w₁.1 b.1) +
        (∑ b ∈ B, pairGap G x₁.1 b.1) := by omega
    _ ≤ _ := houter

end

end BKLPS
