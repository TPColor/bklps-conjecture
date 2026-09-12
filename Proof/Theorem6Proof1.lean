import Proof.Lemma4
import Proof.Lemma5
import Proof.ExternalResults.BKLPSLemma9
import Proof.ExternalResults.BKLPSTheorem4BlockRelations
import Proof.ExternalResults.BlockEnumeration
import Proof.ExternalResults.BlockStructure
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring.RingNF

/-! The block-decomposition branch and final strong-induction assembly. -/

namespace BKLPS

open SimpleGraph

noncomputable section

universe u

/-- The numerical finish of the block branch, separated from the graph
structure.  The block extensions contribute `2mᵢ-4`; Lemma 5 upgrades every
cross-block pair to four units. -/
theorem theorem6BlockArithmetic
    (n k : ℕ) (h_k : k ≥ 2)
    (gap cross : ℤ) (orders gaps : Fin k → ℤ)
    (h_gap : gap ≥ (∑ i : Fin k, gaps i) + cross)
    (h_cross : cross ≥ 4 * (Nat.choose k 2 : ℤ))
    (h_orders : (∑ i : Fin k, orders i) =
      (n : ℤ) + 2 * ((k : ℤ) - 1))
    (h_gaps : ∀ i : Fin k, gaps i ≥ 2 * orders i - 4) :
    gap ≥ 2 * (n : ℤ) := by
  have h_sum : (∑ i : Fin k, (2 * orders i - 4)) ≤ ∑ i : Fin k, gaps i :=
    Finset.sum_le_sum fun i _ => h_gaps i
  have h_choose : (1 : ℤ) ≤ (Nat.choose k 2 : ℤ) := by
    exact_mod_cast Nat.choose_pos h_k
  have h_card : Fintype.card (Fin k) = k := Fintype.card_fin k
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    h_card, nsmul_eq_mul] at h_sum
  rw [← Finset.mul_sum] at h_sum
  rw [h_orders] at h_sum
  omega

/-- The BKLPS block-extension notation and the manuscript's Lemma 4 notation
denote the same vertex set. -/
theorem blockExtensionVertexSet_eq_lemma4VertexSet
    {V : Type u} [Fintype V] [DecidableEq V]
    (u : V) (C : Set {x : V // x ≠ u}) :
    External.blockExtensionVertexSet u C = lemma4VertexSet u C := by
  rfl

/-- Consequently the two names for the induced block-extension graph agree
definitionally. -/
theorem blockExtensionGraph_eq_lemma4Graph
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (C : Set {x : V // x ≠ u}) :
    External.blockExtensionGraph G u C = lemma4Graph G u C := by
  rfl

/-- The corresponding order parameters agree as well. -/
theorem blockExtensionOrder_eq_card_lemma4VertexSet
    {V : Type u} [Fintype V] [DecidableEq V]
    (u : V) (C : Set {x : V // x ≠ u}) :
    External.blockExtensionOrder u C = Fintype.card (lemma4VertexSet u C) := by
  rfl

/-- The BKLPS block gap is exactly the gap bounded by Lemma 4. -/
theorem blockExtensionGap_eq_lemma4Gap
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (C : Set {x : V // x ≠ u}) :
    External.blockExtensionGap G u C = szegedWienerGap (lemma4Graph G u C) := by
  rfl

/-- The cross-block term in the BKLPS decomposition is precisely the sum of
the block-pair contributions used in Lemma 5. -/
theorem blockCrossContribution_eq_sum_blockPairContribution
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (k : ℕ)
    (blocks : Fin k → Set {x : V // x ≠ u}) :
    External.blockCrossContribution G u v k blocks =
      ∑ i : Fin k, ∑ j ∈ (Finset.univ.filter fun j : Fin k => i < j),
        blockPairContribution G u v (blocks i) (blocks j) := by
  rfl

/-- There are exactly `choose k 2` ordered representatives `i < j` of
unordered pairs of indices in `Fin k`. -/
theorem finIncreasingPairCount (k : ℕ) :
    (∑ i : Fin k, (Finset.univ.filter fun j : Fin k => i < j).card) =
      Nat.choose k 2 := by
  simp only [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_range_reflect (fun i => i) k]
  rw [Finset.sum_range_id, Nat.choose_two_right]

/-- If each distinct pair of blocks contributes at least four, then all
cross-block pairs together contribute at least `4 * choose k 2`. -/
theorem blockCrossContribution_ge_four_mul_choose
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (k : ℕ)
    (blocks : Fin k → Set {x : V // x ≠ u})
    (h_each : ∀ i j : Fin k, i < j →
      blockPairContribution G u v (blocks i) (blocks j) ≥ 4) :
    External.blockCrossContribution G u v k blocks ≥
      4 * (Nat.choose k 2 : ℤ) := by
  rw [blockCrossContribution_eq_sum_blockPairContribution]
  have hsum :
      (∑ i : Fin k,
          ∑ j ∈ (Finset.univ.filter fun j : Fin k => i < j), (4 : ℤ)) ≤
        ∑ i : Fin k,
          ∑ j ∈ (Finset.univ.filter fun j : Fin k => i < j),
            blockPairContribution G u v (blocks i) (blocks j) := by
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j hj => h_each i j (by simpa using hj)
  have hfour :
      (∑ i : Fin k,
          ∑ j ∈ (Finset.univ.filter fun j : Fin k => i < j), (4 : ℤ)) =
        4 * (Nat.choose k 2 : ℤ) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.sum_mul]
    rw [← Nat.cast_sum, finIncreasingPairCount]
    ring
  rw [hfour] at hsum
  exact hsum

/-- One pair of distinct blocks already supplies the four cross-block units
needed in the final arithmetic; all other block-pair sums are nonnegative. -/
theorem blockCrossContribution_ge_four
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (k : ℕ) (h_k : k ≥ 2)
    (blocks : Fin k → Set {x : V // x ≠ u})
    (h_each : ∀ i j : Fin k, i < j →
      blockPairContribution G u v (blocks i) (blocks j) ≥ 4) :
    External.blockCrossContribution G u v k blocks ≥ 4 := by
  classical
  let i₀ : Fin k := ⟨0, by omega⟩
  let i₁ : Fin k := ⟨1, by omega⟩
  let F : Fin k → Fin k → ℤ := fun i j =>
    blockPairContribution G u v (blocks i) (blocks j)
  have h_cross_def : External.blockCrossContribution G u v k blocks =
      ∑ i : Fin k, ∑ j ∈ (Finset.univ.filter fun j : Fin k => i < j), F i j := by
    rfl
  have hterm (i j : Fin k) (hij : i < j) : 0 ≤ F i j := by
    have h := h_each i j hij
    simpa [F] using (show (0 : ℤ) ≤
      blockPairContribution G u v (blocks i) (blocks j) by omega)
  have hinner_nonneg (i : Fin k) :
      0 ≤ ∑ j ∈ (Finset.univ.filter fun j : Fin k => i < j), F i j := by
    exact Finset.sum_nonneg fun j hj => hterm i j (by simpa using hj)
  have hi₀ : i₀ ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ _
  have houter :
      (∑ j ∈ (Finset.univ.filter fun j : Fin k => i₀ < j), F i₀ j) ≤
        ∑ i : Fin k, ∑ j ∈ (Finset.univ.filter fun j : Fin k => i < j), F i j := by
    rw [← Finset.sum_erase_add _ _ hi₀]
    have hrest : 0 ≤ ∑ i ∈ (Finset.univ.erase i₀),
        ∑ j ∈ (Finset.univ.filter fun j : Fin k => i < j), F i j := by
      exact Finset.sum_nonneg fun i _ => hinner_nonneg i
    omega
  have hi₀i₁ : i₀ < i₁ := by simp [i₀, i₁]
  have hi₁ : i₁ ∈ (Finset.univ.filter fun j : Fin k => i₀ < j) := by
    simp [hi₀i₁]
  have hinner : F i₀ i₁ ≤
      ∑ j ∈ (Finset.univ.filter fun j : Fin k => i₀ < j), F i₀ j := by
    rw [← Finset.sum_erase_add _ _ hi₁]
    have hrest : 0 ≤ ∑ j ∈
        (Finset.univ.filter fun j : Fin k => i₀ < j).erase i₁, F i₀ j := by
      exact Finset.sum_nonneg fun j hj =>
        hterm i₀ j (by
          have := Finset.mem_of_mem_erase hj
          simpa using this)
    omega
  have hfour : F i₀ i₁ ≥ 4 := h_each i₀ i₁ hi₀i₁
  rw [h_cross_def]
  omega

/-- The graph-theoretic hypotheses of Lemma 5 discharge the per-pair premise
of `blockCrossContribution_ge_four`. -/
theorem blockCrossContribution_ge_four_of_lemma5
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h_two_connected : IsTwoConnected G)
    (u v : V) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete_not_two_connected : ¬IsTwoConnected (deleteVertex G u))
    (h_unique_cut : IsUniqueCutVertex (deleteVertex G u) ⟨v, h_distinct.symm⟩)
    (k : ℕ) (h_k : k ≥ 2)
    (blocks : Fin k → Set {x : V // x ≠ u})
    (h_blocks_injective : Function.Injective blocks)
    (h_blocks_two_connected : ∀ i : Fin k,
      IsTwoConnectedBlock (deleteVertex G u) (blocks i)) :
    External.blockCrossContribution G u v k blocks ≥ 4 := by
  apply blockCrossContribution_ge_four G u v k h_k blocks
  intro i j hij
  exact lemma5 G h_two_connected u v h_distinct h_neighborhood
    h_delete_not_two_connected h_unique_cut (blocks i) (blocks j)
    (h_blocks_two_connected i) (h_blocks_two_connected j)
    (fun h => (ne_of_lt hij) (h_blocks_injective h))

/-- Applying Lemma 5 to every pair of blocks gives exactly the stronger
cross-term estimate required by `theorem6BlockArithmetic`. -/
theorem blockCrossContribution_ge_four_mul_choose_of_lemma5
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h_two_connected : IsTwoConnected G)
    (u v : V) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete_not_two_connected : ¬IsTwoConnected (deleteVertex G u))
    (h_unique_cut : IsUniqueCutVertex (deleteVertex G u) ⟨v, h_distinct.symm⟩)
    (k : ℕ)
    (blocks : Fin k → Set {x : V // x ≠ u})
    (h_blocks_injective : Function.Injective blocks)
    (h_blocks_two_connected : ∀ i : Fin k,
      IsTwoConnectedBlock (deleteVertex G u) (blocks i)) :
    External.blockCrossContribution G u v k blocks ≥
      4 * (Nat.choose k 2 : ℤ) := by
  apply blockCrossContribution_ge_four_mul_choose G u v k blocks
  intro i j hij
  exact lemma5 G h_two_connected u v h_distinct h_neighborhood
    h_delete_not_two_connected h_unique_cut (blocks i) (blocks j)
    (h_blocks_two_connected i) (h_blocks_two_connected j)
    (fun h => (ne_of_lt hij) (h_blocks_injective h))

/-- The complete graph-level finish of the block branch.  Once BKLPS
Lemma 9 supplies the blocks, the BKLPS decomposition relation, Lemma 4 on
each block extension, and Lemma 5 on each pair of blocks exactly discharge
the hypotheses of `theorem6BlockArithmetic`. -/
theorem theorem6BlockFinish
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h_two_connected : IsTwoConnected G)
    (u v : V) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete_not_two_connected : ¬IsTwoConnected (deleteVertex G u))
    (h_unique_cut : IsUniqueCutVertex (deleteVertex G u) ⟨v, h_distinct.symm⟩)
    (k : ℕ) (h_k : k ≥ 2)
    (blocks : Fin k → Set {x : V // x ≠ u})
    (h_blocks_injective : Function.Injective blocks)
    (h_blocks : ∀ C : Set {x : V // x ≠ u},
      IsBlock (deleteVertex G u) C ↔ ∃ i : Fin k, C = blocks i)
    (h_blocks_two_connected : ∀ i : Fin k,
      IsTwoConnectedBlock (deleteVertex G u) (blocks i))
    (h_blocks_unexceptional : ∀ i : Fin k,
      letI : Fintype (blocks i) := Fintype.ofFinite (blocks i)
      IsUnexceptional ((deleteVertex G u).induce (blocks i))) :
    szegedWienerGap G ≥ (2 * Fintype.card V : ℤ) := by
  obtain ⟨h_gap, _h_cross_two, h_orders⟩ :=
    External.bklpsTheorem4BlockRelations G u v h_distinct h_two_connected
      h_neighborhood h_unique_cut k h_k blocks h_blocks_injective h_blocks
  have h_cross := blockCrossContribution_ge_four_mul_choose_of_lemma5
    G h_two_connected u v h_distinct h_neighborhood
      h_delete_not_two_connected h_unique_cut k blocks h_blocks_injective
      h_blocks_two_connected
  apply theorem6BlockArithmetic (Fintype.card V) k h_k
    (szegedWienerGap G) (External.blockCrossContribution G u v k blocks)
    (fun i => (External.blockExtensionOrder u (blocks i) : ℤ))
    (fun i => External.blockExtensionGap G u (blocks i))
  · exact h_gap
  · exact h_cross
  · exact h_orders
  · intro i
    rw [blockExtensionGap_eq_lemma4Gap,
      blockExtensionOrder_eq_card_lemma4VertexSet]
    exact lemma4 G h_two_connected u v h_distinct h_neighborhood
      h_delete_not_two_connected h_unique_cut (blocks i)
      (h_blocks_two_connected i).1 (h_blocks_unexceptional i)

/-- The terminal block-decomposition branch of Theorem 6.  The statement
file performs the induction and earlier case splits; this branch combines
the BKLPS block relations with Lemmas 4 and 5. -/
theorem theorem6Proof1OfFive
    (n : ℕ)
    {W : Type u} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W)
    (hcard : Fintype.card W = n)
    (hn : n ≥ 5)
    (hunexceptional : IsUnexceptional K)
    (htwo : IsTwoConnected K)
    (x y : W) (hxy : x ≠ y)
    (hsub : closedNeighborhood K x ⊆ closedNeighborhood K y)
    (hdeletions : ∀ a b : W, a ≠ b →
      closedNeighborhood K a ⊆ closedNeighborhood K b →
      IsomorphicToKn (deleteVertex K a) ∨
        ¬IsTwoConnected (deleteVertex K a)) :
    szegedWienerGap K ≥ (2 * Fintype.card W : ℤ) := by
  /-
  In the terminal block branch, BKLPS's two decomposition relations,
  Lemma 4, and Lemma 5 give

    `η(G) ≥ ∑ (2mᵢ-4) + 4 * choose k 2`
         `= 2n-4+2k(k-1) ≥ 2n`

  because `k≥2`.
  -/
  classical
  have hnoncomplete : ¬IsomorphicToKn K := by
    intro h
    exact hunexceptional (Or.inl h)
  have hnotK42 : ¬Nonempty (K ≃g Knt 4 2) := by
    rintro ⟨e⟩
    have heq : Fintype.card W = 4 := by simpa using e.card_eq
    omega
  obtain ⟨hdeleteNotTwo, hunique, hblocksUnexceptional⟩ :=
    External.bklpsLemma9 K htwo hnoncomplete hnotK42 hdeletions
      ⟨x, y, hxy, hsub⟩ x y hxy hsub
  let H := deleteVertex K x
  let cut : {z : W // z ≠ x} := ⟨y, hxy.symm⟩
  let k := External.blockCount H
  let blocks : Fin k → Set {z : W // z ≠ x} := External.enumeratedBlock H
  have hk : k ≥ 2 := by
    exact External.two_le_blockCount_of_cutVertex H cut hunique.1
  have hblocksInjective : Function.Injective blocks :=
    External.enumeratedBlock_injective H
  have hblocks : ∀ C : Set {z : W // z ≠ x}, IsBlock H C ↔
      ∃ i : Fin k, C = blocks i := by
    intro C
    exact External.isBlock_iff_eq_enumeratedBlock H C
  have hblocksTwo : ∀ i : Fin k, IsTwoConnectedBlock H (blocks i) := by
    intro i
    have hblock : IsBlock H (blocks i) :=
      External.enumeratedBlock_isBlock H i
    have hunblock := hblocksUnexceptional (blocks i) hblock
    exact ⟨hblock,
      External.isTwoConnected_of_isBlock_unexceptional H (blocks i)
        hblock hunblock⟩
  have hblocksUn : ∀ i : Fin k,
      letI : Fintype (blocks i) := Fintype.ofFinite (blocks i)
      IsUnexceptional (H.induce (blocks i)) := by
    intro i
    exact hblocksUnexceptional (blocks i)
      (External.enumeratedBlock_isBlock H i)
  exact theorem6BlockFinish K htwo x y hxy hsub hdeleteNotTwo hunique
    k hk blocks hblocksInjective hblocks hblocksTwo hblocksUn

/-- The order-ten interface used in the main induction. The block argument
actually works from order five, also allowing the finite base classification
to discard terminal block decompositions at orders six through nine. -/
theorem theorem6Proof1
    (n : ℕ)
    {W : Type u} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W)
    (hcard : Fintype.card W = n)
    (hn : n ≥ 10)
    (hunexceptional : IsUnexceptional K)
    (htwo : IsTwoConnected K)
    (x y : W) (hxy : x ≠ y)
    (hsub : closedNeighborhood K x ⊆ closedNeighborhood K y)
    (hdeletions : ∀ a b : W, a ≠ b →
      closedNeighborhood K a ⊆ closedNeighborhood K b →
        IsomorphicToKn (deleteVertex K a) ∨
          ¬IsTwoConnected (deleteVertex K a)) :
    szegedWienerGap K ≥ (2 * Fintype.card W : ℤ) :=
  theorem6Proof1OfFive n K hcard (by omega) hunexceptional htwo x y hxy hsub hdeletions

end

end BKLPS
