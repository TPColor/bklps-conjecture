import Proof.ExternalResults.BKLPSLemma9
import Proof.ExternalResults.BKLPSTheorem4BlockRelations
import Proof.ExternalResults.BlockEnumeration
import Proof.Theorem3BlockExtensionStructure
import Proof.ExternalResults.BlockStructure
import Proof.Theorem3OrderFiveLowerBound
import Mathlib.Tactic.Ring.RingNF

/-! The block-decomposition branch and assembly of Theorem 3. -/

namespace BKLPS

open SimpleGraph

noncomputable section

universe u

private theorem two_mul_choose_two_ge (k : ℕ) (h_k : k ≥ 2) :
    2 * Nat.choose k 2 ≥ k := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hk : 2 ≤ k
      · have hprev := ih hk
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        omega
      · have hk1 : k = 1 := by omega
        subst k
        decide

/-- The numerical finish of the block branch of Theorem 3.  A block of
order five loses one unit compared with `2mᵢ-4`; there are at most `k` such
blocks, and the `2 * choose k 2` cross-block term pays for all of them. -/
theorem theorem3BlockArithmetic
    (n k r : ℕ) (h_k : k ≥ 2) (h_r : r ≤ k)
    (gap sumGaps sumOrders : ℤ)
    (h_gap : gap ≥ sumGaps + 2 * (Nat.choose k 2 : ℤ))
    (h_sum_gaps : sumGaps ≥ 2 * sumOrders - 4 * (k : ℤ) - (r : ℤ))
    (h_orders : sumOrders = (n : ℤ) + 2 * ((k : ℤ) - 1)) :
    gap ≥ 2 * (n : ℤ) - 4 := by
  have h_pay_nat := two_mul_choose_two_ge k h_k
  have h_pay : (k : ℤ) ≤ 2 * (Nat.choose k 2 : ℤ) := by
    exact_mod_cast h_pay_nat
  have hrz : (r : ℤ) ≤ (k : ℤ) := by exact_mod_cast h_r
  omega

/-- The graph-level numerical finish of the block branch.  It is enough to
have the uniform BKLPS bound `η(Gᵢ) ≥ 2mᵢ-5` for every extension: the
`2 * choose k 2` cross term pays the possible one-unit loss in all `k`
blocks. -/
theorem theorem3BlockFinish
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
      IsBlock (deleteVertex G u) C ↔ ∃ i : Fin k, C = blocks i)
    (h_extension_gaps : ∀ i : Fin k,
      External.blockExtensionGap G u (blocks i) ≥
        2 * External.blockExtensionOrder u (blocks i) - 5) :
    szegedWienerGap G ≥ (2 * Fintype.card V - 4 : ℤ) := by
  obtain ⟨h_gap, h_cross, h_orders⟩ :=
    External.bklpsTheorem4BlockRelations G u v h_distinct h_two_connected
      h_neighborhood h_unique_cut k h_k blocks h_blocks_injective h_blocks
  have h_sum_gaps :
      (∑ i : Fin k, External.blockExtensionGap G u (blocks i)) ≥
        2 * (∑ i : Fin k,
          (External.blockExtensionOrder u (blocks i) : ℤ)) - 5 * (k : ℤ) := by
    have hsum := Finset.sum_le_sum fun i (_hi : i ∈ (Finset.univ : Finset (Fin k))) =>
      h_extension_gaps i
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    rw [← Finset.mul_sum] at hsum
    simpa [mul_comm] using hsum
  apply theorem3BlockArithmetic (Fintype.card V) k k h_k le_rfl
    (szegedWienerGap G)
    (∑ i : Fin k, External.blockExtensionGap G u (blocks i))
    (∑ i : Fin k, (External.blockExtensionOrder u (blocks i) : ℤ))
  · omega
  · omega
  · exact h_orders

/-- The terminal block-decomposition branch of Theorem 3.  The statement
file performs the induction and earlier case splits. -/
theorem theorem3Proof3
    (n : ℕ)
    (ih : ∀ m < n, ∀ (W : Type u) [Fintype W] [DecidableEq W],
      ∀ K : SimpleGraph W,
      Fintype.card W = m → m ≥ 6 → IsUnexceptional K → IsTwoConnected K →
      szegedWienerGap K ≥ (2 * Fintype.card W - 4 : ℤ))
    {W : Type u} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W)
    (hcard : Fintype.card W = n)
    (hn : n ≥ 6)
    (hunexceptional : IsUnexceptional K)
    (htwo : IsTwoConnected K)
    (x y : W) (hxy : x ≠ y)
    (hsub : closedNeighborhood K x ⊆ closedNeighborhood K y)
    (hdeletions : ∀ a b : W, a ≠ b →
      closedNeighborhood K a ⊆ closedNeighborhood K b →
      IsomorphicToKn (deleteVertex K a) ∨
        ¬IsTwoConnected (deleteVertex K a)) :
    szegedWienerGap K ≥ (2 * Fintype.card W - 4 : ℤ) := by
  /-
  In the terminal induction branch, BKLPS Lemma 9 supplies the unique cut vertex and
     unexceptional blocks.  The block relations from the proof of BKLPS
     Theorem 4 give

       `η(G) ≥ ∑ η(Gᵢ) + 2 * choose k 2`,
       `∑ mᵢ = n + 2(k-1)`.

     Apply the induction hypothesis when `mᵢ ≥ 6` and BKLPS Theorem 4 when
     `mᵢ=5`.  If `r` blocks have order five, the resulting lower bound is
     `2n-4-r+k(k-1) ≥ 2n-4` because `r ≤ k ≤ k(k-1)`.
  -/
  classical
  have hnoncomplete : ¬IsomorphicToKn K := by
    intro h
    exact hunexceptional (Or.inl h)
  have hnotK42 : ¬Nonempty (K ≃g Knt 4 2) := by
    rintro ⟨e⟩
    have heq : Fintype.card W = 4 := by simpa using e.card_eq
    omega
  obtain ⟨_hdeleteNotTwo, hunique, hblocksUnexceptional⟩ :=
    External.bklpsLemma9 K htwo hnoncomplete hnotK42 hdeletions
      ⟨x, y, hxy, hsub⟩ x y hxy hsub
  let H := deleteVertex K x
  let cut : {z : W // z ≠ x} := ⟨y, hxy.symm⟩
  let k := External.blockCount H
  let blocks : Fin k → Set {z : W // z ≠ x} :=
    External.enumeratedBlock H
  have hk : k ≥ 2 :=
    External.two_le_blockCount_of_cutVertex H cut hunique.1
  have hblocksInjective : Function.Injective blocks :=
    External.enumeratedBlock_injective H
  have hblocks : ∀ C : Set {z : W // z ≠ x}, IsBlock H C ↔
      ∃ i : Fin k, C = blocks i := by
    intro C
    exact External.isBlock_iff_eq_enumeratedBlock H C
  have hblocksUn : ∀ i : Fin k,
      letI : Fintype (blocks i) := Fintype.ofFinite (blocks i)
      IsUnexceptional (H.induce (blocks i)) := by
    intro i
    exact hblocksUnexceptional (blocks i)
      (External.enumeratedBlock_isBlock H i)
  have hblocksTwo : ∀ i : Fin k,
      letI : Fintype (blocks i) := Fintype.ofFinite (blocks i)
      IsTwoConnected (H.induce (blocks i)) := by
    intro i
    have hblock := External.enumeratedBlock_isBlock H i
    exact External.isTwoConnected_of_isBlock_unexceptional H (blocks i)
      hblock (hblocksUn i)
  have hextensionGaps : ∀ i : Fin k,
      External.blockExtensionGap K x (blocks i) ≥
        2 * External.blockExtensionOrder x (blocks i) - 5 := by
    intro i
    let C := blocks i
    letI : Fintype C := Fintype.ofFinite C
    let Gᵢ := External.blockExtensionGraph K x C
    let xᵢ : External.blockExtensionVertexSet x C :=
      ⟨x, by simp [External.blockExtensionVertexSet]⟩
    have hblock : IsBlock H C := by
      simpa [C] using External.enumeratedBlock_isBlock H i
    have hCcard : 4 ≤ Fintype.card C :=
      External.four_le_card_of_connected_noCut_unexceptional
        (H.induce C) hblock.1.1 hblock.1.2 (hblocksUn i)
    have hdeleteCard : Fintype.card
        {z : External.blockExtensionVertexSet x C // z ≠ xᵢ} =
        Fintype.card (External.blockExtensionVertexSet x C) - 1 := by
      simpa using Fintype.card_subtype_compl
        (fun z : External.blockExtensionVertexSet x C => z = xᵢ)
    have hisoCard := (blockExtensionDeleteIso K x C).card_eq
    have horder : 5 ≤ Fintype.card
        (External.blockExtensionVertexSet x C) := by
      rw [hdeleteCard] at hisoCard
      omega
    have hextTwo : IsTwoConnected Gᵢ :=
      blockExtension_twoConnected K htwo x y hxy hsub hunique
        C hblock (hblocksTwo i)
    have hextUn : IsUnexceptional Gᵢ :=
      blockExtension_unexceptional K x C horder
        (hblocksTwo i) (hblocksUn i)
    by_cases hsix : 6 ≤ Fintype.card
        (External.blockExtensionVertexSet x C)
    · have hcardExt : Fintype.card
          (External.blockExtensionVertexSet x C) < n := by
        obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card
          (by simpa using hk) i
        obtain ⟨z, hzj, hzy, _hxz⟩ :=
          External.exists_u_neighbor_in_block K htwo x y hxy hunique
            (blocks j) (External.enumeratedBlock_isBlock H j)
        have hzNotC : z ∉ C := by
          intro hzC
          have heq : C = blocks j :=
            External.isBlock_eq_of_two_common H C (blocks j) hblock
              (External.enumeratedBlock_isBlock H j) cut z
              (External.uniqueCut_mem_isBlock H cut hunique C hblock)
              (External.uniqueCut_mem_isBlock H cut hunique (blocks j)
                (External.enumeratedBlock_isBlock H j))
              hzC hzj (by
                intro h
                exact hzy (congrArg Subtype.val h).symm)
          exact hji (hblocksInjective (by simpa [C] using heq)).symm
        have hproper : C ⊂ (Set.univ : Set {z : W // z ≠ x}) := by
          apply Set.ssubset_univ_iff.mpr
          intro hEq
          apply hzNotC
          rw [hEq]
          exact Set.mem_univ z
        have hCcardLtUniv :=
          Set.Finite.card_lt_card (Set.toFinite _) hproper
        have hUnivCard :
            Nat.card ↑(Set.univ : Set {z : W // z ≠ x}) =
              Nat.card {z : W // z ≠ x} :=
          Nat.card_congr (Equiv.Set.univ _)
        rw [hUnivCard] at hCcardLtUniv
        have hCcardLt : Nat.card C < Nat.card {z : W // z ≠ x} :=
          hCcardLtUniv
        change External.blockExtensionOrder x C < n
        rw [External.blockExtensionOrder_eq_card_add_one]
        have hdeleteCardW : Fintype.card {z : W // z ≠ x} = n - 1 := by
          rw [← hcard]
          simpa using Fintype.card_subtype_compl (fun z : W => z = x)
        have hdeleteCardNat : Nat.card {z : W // z ≠ x} = n - 1 := by
          simpa only [Nat.card_eq_fintype_card] using hdeleteCardW
        omega
      have hrec := ih _ (by simpa using hcardExt)
        (External.blockExtensionVertexSet x C) Gᵢ rfl hsix hextUn hextTwo
      change szegedWienerGap Gᵢ ≥
        2 * Fintype.card (External.blockExtensionVertexSet x C) - 5
      omega
    · have hfiveOrder : Fintype.card
          (External.blockExtensionVertexSet x C) = 5 := by omega
      have hfiveBound := orderFiveLowerBound Gᵢ hfiveOrder hextTwo hextUn
      change szegedWienerGap Gᵢ ≥
        2 * Fintype.card (External.blockExtensionVertexSet x C) - 5
      omega
  exact theorem3BlockFinish K x y hxy htwo hsub hunique k hk blocks
    hblocksInjective hblocks hextensionGaps

end

end BKLPS
