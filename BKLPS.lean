import Proof.Theorem1
import Proof.Lemma2
import Proof.Theorem3
import Proof.Lemma4
import Proof.Lemma5
import Proof.Theorem6
import Proof.Lemma7

/-!
# The BKLPS Szeged--Wiener gap conjecture

Conjecture 5 of Bonamy--Knor--Lužar--Pinlou--Škrekovski (2017), translated
with the hypotheses and exceptional graphs in the same way as in the paper.

The proof route exposed by this umbrella module is the one in the manuscript
formalization.  Theorem 1 computes the gap of both exceptional cone families.
Lemma 2 controls the jump in the gap when a dominated vertex is deleted and
the deletion is exceptional.  Theorem 3 proves the preliminary `2n-4` bound
by strong induction, using BKLPS Lemmas 7, 9, and 10 and the terminal block
decomposition.  Lemmas 4 and 5 strengthen the two ingredients of that block
decomposition: each block extension contributes at least `2m_i-4`, and each
pair of blocks contributes at least four.

Theorem 6 repeats the induction with these strengthened estimates.  In the
ordinary deletion branch its induction hypothesis adds to the two units from
BKLPS Lemma 7.  In the terminal branch the block relations give

`η(G) ≥ ∑_i (2m_i-4) + 4 choose k 2`,

and `∑_i m_i=n+2(k-1)` reduces this to
`2n-4+2k(k-1) ≥ 2n` because `k≥2`.  The theorem below only translates the
paper's three explicit nonisomorphism hypotheses into `IsUnexceptional G`;
the complete induction and its main branches remain visible in
`Proof.Theorem6`. Lemma 7 supplies the construction attaining equality for all `n ≥ 10`.
-/

namespace BKLPS

open SimpleGraph

universe u

/-- **BKLPS, Conjecture 5.** Let `G` be a 2-connected graph of order `n ≥ 10`
not isomorphic to `K_n`, `K_n^2`, or `K_n^(n-2)`. Then `η(G) ≥ 2n`. -/
theorem bklpsConjecture
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_two_connected : IsTwoConnected G)
    (h_order : Fintype.card V ≥ 10)
    (h_not_Kn : ¬ IsomorphicToKn G)
    (h_not_Kn2 : ¬ IsomorphicToKnt G 2)
    (h_not_Knn2 : ¬ IsomorphicToKnt G (Fintype.card V - 2)) :
    szegedWienerGap G ≥ (2 * Fintype.card V : ℤ) := by
  have h_unexceptional : IsUnexceptional G := by
    intro h_exceptional
    rcases h_exceptional with h_Kn | h_Kn2 | h_Knn2
    · exact h_not_Kn h_Kn
    · exact h_not_Kn2 h_Kn2
    · exact h_not_Knn2 h_Knn2
  have h_main := theorem6 G h_order h_unexceptional h_two_connected
  exact h_main

end BKLPS
