import Proof.Lemma2
import Proof.Theorem1
import Proof.ExternalResults.BKLPSLemma7
import Mathlib.Tactic.Ring.RingNF
import Proof.ExternalResults.BKLPSLemma9
import Proof.ExternalResults.BKLPSTheorem4BlockRelations
import Proof.ExternalResults.BlockEnumeration
import Proof.Theorem3BlockExtensionStructure
import Proof.ExternalResults.BlockStructure
import Proof.Theorem3OrderFiveLowerBound
import Proof.Theorem3OrderSixCheck
import Proof.ExternalResults.BKLPSLemma10
import Proof.Theorem3Proof3

/-! The 2-connected, noncomplete vertex-deletion branch of Theorem 3. -/

namespace BKLPS

open SimpleGraph

noncomputable section

universe u

/-- The unexceptional-deletion branch: BKLPS Lemma 7 contributes two and
the induction hypothesis on `G-u` contributes `2(n-1)-4`. -/
theorem theorem3Proof2Unexceptional
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_order : Fintype.card V ≥ 7)
    (h_unexceptional : IsUnexceptional G)
    (h_two_connected : IsTwoConnected G)
    (u v : V) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete_two_connected : IsTwoConnected (deleteVertex G u))
    (h_delete_noncomplete : ¬IsomorphicToKn (deleteVertex G u))
    (h_delete_unexceptional : IsUnexceptional (deleteVertex G u))
    (h_induction : szegedWienerGap (deleteVertex G u) ≥
      (2 * (Fintype.card V - 1) - 4 : ℤ)) :
    szegedWienerGap G ≥ (2 * Fintype.card V - 4 : ℤ) := by
  have h_step := External.bklpsLemma7 G u v h_two_connected h_distinct
    h_neighborhood h_delete_two_connected h_delete_noncomplete
  omega

/-- The exceptional-deletion branch: completeness is impossible, while the
two remaining exceptional families are handled by Lemma 2 and Theorem 1. -/
theorem theorem3Proof2Exceptional
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_order : Fintype.card V ≥ 7)
    (h_unexceptional : IsUnexceptional G)
    (h_two_connected : IsTwoConnected G)
    (u v : V) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete_noncomplete : ¬IsomorphicToKn (deleteVertex G u))
    (h_exceptional : IsExceptional (deleteVertex G u)) :
    szegedWienerGap G ≥ (2 * Fintype.card V - 4 : ℤ) := by
  classical
  have h_card_delete :
      Fintype.card {x : V // x ≠ u} = Fintype.card V - 1 := by
    simpa using Fintype.card_subtype_compl (fun x : V => x = u)
  rcases h_exceptional with h_complete | h_K2 | h_Klarge
  · exact False.elim (h_delete_noncomplete h_complete)
  · have h_step := lemma2 G (by omega) h_unexceptional h_two_connected u v
      h_distinct h_neighborhood (Or.inl h_K2)
    have h_gap := theorem1OfIsomorphicToKnt (deleteVertex G u) 2
      (by omega) (by omega) h_K2
    omega
  · have h_Klarge' :
        IsomorphicToKnt (deleteVertex G u) (Fintype.card V - 3) := by
      rw [← show Fintype.card {x : V // x ≠ u} - 2 = Fintype.card V - 3 by omega]
      exact h_Klarge
    have h_step := lemma2 G (by omega) h_unexceptional h_two_connected u v
      h_distinct h_neighborhood (Or.inr h_Klarge')
    have h_gap := theorem1OfIsomorphicToKnt (deleteVertex G u)
      (Fintype.card V - 3) (by omega) (by omega) h_Klarge'
    rw [h_card_delete, Nat.cast_sub (by omega : 1 ≤ Fintype.card V),
      Nat.cast_sub (by omega : 3 ≤ Fintype.card V)] at h_gap
    ring_nf at h_gap
    omega

end

end BKLPS


/-!
Main route of the manuscript proof of Theorem 3.

Use strong induction on `n`.  The base `n=6` is the finite check.  If there
is no proper closed-neighborhood containment, BKLPS Lemma 10 gives the
stronger bound `η(G)≥2n`.

Otherwise choose `N[u] ⊆ N[v]` and set `H=G-u`.  When `H` is 2-connected
and noncomplete, BKLPS Lemma 7 gives `η(G)-η(H)≥2`.  If `H` is
unexceptional, add this to the induction hypothesis.  If `H` is exceptional,
its noncompleteness leaves the two cone families; Lemma 2 contributes
`n-2`, Theorem 1 gives `η(H)=2n-8`, and `n≥7` closes the estimate.

In the terminal branch every dominated deletion is complete or not
2-connected.  BKLPS Lemma 9 gives blocks `C_i`, extensions `G_i`, and
`k≥2`.  The BKLPS relations are

`η(G) ≥ ∑_i η(G_i) + 2 choose k 2`,
`∑_i m_i = n + 2(k-1)`.

Induction gives `2m_i-4` except at order five, where the bound is
`2m_i-5`.  If there are `r` order-five blocks, the resulting expression is
`2n-4-r+k(k-1)`, at least `2n-4` because `r≤k≤k(k-1)`.
-/

namespace BKLPS

open SimpleGraph

noncomputable section

universe u

/-- **Theorem 3.** Every unexceptional 2-connected graph of order `n ≥ 6`
has `η(G) ≥ 2n-4`. -/
theorem theorem3
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_order : Fintype.card V ≥ 6)
    (h_unexceptional : IsUnexceptional G)
    (h_two_connected : IsTwoConnected G) :
    szegedWienerGap G ≥ (2 * Fintype.card V - 4 : ℤ) := by
  /- Follow the informal proof by strong induction.  At each order we first
  discharge the finite base case and the BKLPS Lemma 10 case.  For a
  dominated pair, we split according to whether deletion stays 2-connected
  and noncomplete, and then according to whether that deletion is
  unexceptional.  Only the remaining terminal case is delegated to the
  technical block-decomposition proof. -/
  classical
  have main : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W],
      ∀ K : SimpleGraph W,
      Fintype.card W = n → n ≥ 6 → IsUnexceptional K → IsTwoConnected K →
      szegedWienerGap K ≥ (2 * Fintype.card W - 4 : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ K hcard hn hunexceptional htwo
      by_cases hsix : n = 6
      · have hKsix : Fintype.card W = 6 := hcard.trans hsix
        simpa [hKsix] using orderSixCheck K hKsix htwo hunexceptional
      have hnlarge : n ≥ 7 := by omega
      by_cases hno : ∀ x y : W, x ≠ y →
          ¬(closedNeighborhood K x ⊆ closedNeighborhood K y)
      · have h_noncomplete : ¬IsomorphicToKn K := by
          intro h_complete
          exact hunexceptional (Or.inl h_complete)
        have h_not_C5 : ¬IsomorphicToCn K 5 := by
          rintro ⟨e⟩
          have hfive : Fintype.card W = 5 := by
            simpa [Cn] using Fintype.card_congr e.toEquiv
          omega
        have h_gap := (External.bklpsLemma10 K htwo h_noncomplete h_not_C5 hno).2
        omega
      have hexists : ∃ x y : W, x ≠ y ∧
          closedNeighborhood K x ⊆ closedNeighborhood K y := by
        push_neg at hno
        exact hno
      by_cases hgood : ∃ x y : W, x ≠ y ∧
          closedNeighborhood K x ⊆ closedNeighborhood K y ∧
          IsTwoConnected (deleteVertex K x) ∧
          ¬IsomorphicToKn (deleteVertex K x)
      · obtain ⟨x, y, hxy, hsub, hdeleteTwo, hdeleteNoncomplete⟩ := hgood
        by_cases hdeleteUn : IsUnexceptional (deleteVertex K x)
        · apply theorem3Proof2Unexceptional K (by omega) hunexceptional htwo
            x y hxy hsub hdeleteTwo hdeleteNoncomplete hdeleteUn
          have hcardDelete : Fintype.card {z : W // z ≠ x} = n - 1 := by
            rw [← hcard]
            simpa using Fintype.card_subtype_compl (fun z : W => z = x)
          have hrec := ih (n - 1) (by omega) {z : W // z ≠ x}
            (deleteVertex K x) hcardDelete (by omega) hdeleteUn hdeleteTwo
          rw [hcardDelete] at hrec
          rw [Nat.cast_sub (by omega : 1 ≤ n)] at hrec
          simpa [hcard] using hrec
        · have hdeleteExceptional : IsExceptional (deleteVertex K x) := by
            unfold IsUnexceptional at hdeleteUn
            exact Classical.not_not.mp hdeleteUn
          exact theorem3Proof2Exceptional K (by omega) hunexceptional htwo
            x y hxy hsub hdeleteNoncomplete hdeleteExceptional
      · have hdeletions : ∀ x y : W, x ≠ y →
            closedNeighborhood K x ⊆ closedNeighborhood K y →
            IsomorphicToKn (deleteVertex K x) ∨
              ¬IsTwoConnected (deleteVertex K x) := by
          intro x y hxy hsub
          by_cases hcomplete : IsomorphicToKn (deleteVertex K x)
          · exact Or.inl hcomplete
          · right
            intro hdeleteTwo
            exact hgood ⟨x, y, hxy, hsub, hdeleteTwo, hcomplete⟩
        obtain ⟨x, y, hxy, hsub⟩ := hexists
        exact theorem3Proof3 n ih K hcard hn hunexceptional htwo
          x y hxy hsub hdeletions
  exact main (Fintype.card V) V G rfl h_order h_unexceptional h_two_connected

end

end BKLPS
