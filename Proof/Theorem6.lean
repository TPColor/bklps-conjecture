import Proof.Lemma2
import Proof.Theorem1
import Proof.ExternalResults.BKLPSLemma7
import Mathlib.Tactic.Ring.RingNF
import Proof.Lemma4
import Proof.Lemma5
import Proof.ExternalResults.BKLPSLemma9
import Proof.ExternalResults.BKLPSTheorem4BlockRelations
import Proof.ExternalResults.BlockEnumeration
import Proof.ExternalResults.BlockStructure
import Mathlib.Algebra.BigOperators.Intervals
import Proof.ExternalResults.BKLPSLemma10
import Proof.ExternalResults.BKLPSOrderTenCheck.BKLPSOrderTenCheck
import Proof.Theorem6Proof1

/-! The 2-connected, noncomplete deletion branch of Theorem 6. -/

namespace BKLPS

open SimpleGraph

noncomputable section

universe u

/-- If `G-u` is unexceptional, BKLPS Lemma 7 and the induction hypothesis
sum to the desired `2n` bound. -/
theorem theorem6Proof2Unexceptional
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_order : Fintype.card V ≥ 11)
    (h_unexceptional : IsUnexceptional G)
    (h_two_connected : IsTwoConnected G)
    (u v : V) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete_two_connected : IsTwoConnected (deleteVertex G u))
    (h_delete_noncomplete : ¬IsomorphicToKn (deleteVertex G u))
    (h_delete_unexceptional : IsUnexceptional (deleteVertex G u))
    (h_induction : szegedWienerGap (deleteVertex G u) ≥
      (2 * (Fintype.card V - 1) : ℤ)) :
    szegedWienerGap G ≥ (2 * Fintype.card V : ℤ) := by
  have h_step := External.bklpsLemma7 G u v h_two_connected h_distinct
    h_neighborhood h_delete_two_connected h_delete_noncomplete
  omega

/-- If `G-u` is exceptional, completeness contradicts the branch hypothesis;
the two cone families are settled by Lemma 2 plus Theorem 1. -/
theorem theorem6Proof2Exceptional
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_order : Fintype.card V ≥ 11)
    (h_unexceptional : IsUnexceptional G)
    (h_two_connected : IsTwoConnected G)
    (u v : V) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete_noncomplete : ¬IsomorphicToKn (deleteVertex G u))
    (h_exceptional : IsExceptional (deleteVertex G u)) :
    szegedWienerGap G ≥ (2 * Fintype.card V : ℤ) := by
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
Main route of the manuscript proof of Theorem 6.

Strongly induct on the order, using the BKLPS order-ten computation as the
base.  With no proper closed-neighborhood containment, BKLPS Lemma 10 gives
`η(G)≥2n`.  Otherwise choose `N[u]⊆N[v]` and put `H=G-u`.

If `H` is 2-connected and noncomplete, then BKLPS Lemma 7 contributes two.
For unexceptional `H`, adding the induction bound `2(n-1)` gives `2n`.
For exceptional `H`, Lemma 2 and Theorem 1 instead give
`η(G)≥(n-2)+(2n-8)=3n-10≥2n`.

In the terminal branch BKLPS Lemma 9 supplies `k≥2` unexceptional blocks
and the block decomposition.  Lemma 4 gives `η(G_i)≥2m_i-4` for every
extension, while Lemma 5 gives four for every pair of blocks.  Therefore

`η(G) ≥ ∑_i(2m_i-4) + 4 choose k 2`
`       = 2n-4+2k(k-1) ≥ 2n`.
-/

namespace BKLPS

open SimpleGraph

noncomputable section

universe u

/-- **Theorem 6 (BKLPS Szeged--Wiener Gap Conjecture).** Every
unexceptional 2-connected graph of order `n ≥ 10` has `η(G) ≥ 2n`. -/
theorem theorem6
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_order : Fintype.card V ≥ 10)
    (h_unexceptional : IsUnexceptional G)
    (h_two_connected : IsTwoConnected G) :
    szegedWienerGap G ≥ (2 * Fintype.card V : ℤ) := by
  /- Follow the informal proof by strong induction.  The statement file
  carries the finite base case, the BKLPS Lemma 10 branch, and both the
  unexceptional and exceptional deletion branches.  In the remaining block
  branch, the technical proof combines Lemma 4 on each extension with
  Lemma 5 on every pair of blocks; `4 * choose k 2` upgrades the block sum
  to `2n`. -/
  classical
  have main : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W],
      ∀ K : SimpleGraph W,
      Fintype.card W = n → n ≥ 10 → IsUnexceptional K → IsTwoConnected K →
      szegedWienerGap K ≥ (2 * Fintype.card W : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ K hcard hn hunexceptional htwo
      by_cases hten : n = 10
      · have hKten : Fintype.card W = 10 := hcard.trans hten
        simpa [hKten] using
          External.bklpsOrderTenCheck K hKten htwo hunexceptional
      have hnlarge : n ≥ 11 := by omega
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
        exact (External.bklpsLemma10 K htwo h_noncomplete h_not_C5 hno).2
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
        · apply theorem6Proof2Unexceptional K (by omega) hunexceptional htwo
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
          exact theorem6Proof2Exceptional K (by omega) hunexceptional htwo
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
        exact theorem6Proof1 n K hcard hn hunexceptional htwo
          x y hxy hsub hdeletions
  exact main (Fintype.card V) V G rfl h_order h_unexceptional h_two_connected

end

end BKLPS
