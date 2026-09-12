import Proof.Theorem3
import Proof.ExternalResults.BKLPSTheorem4SmallCheck

/-!
Main route to the BKLPS Theorem 4 bound used by this formalization.

The three nonisomorphism assumptions say exactly that `G` is outside the
complete graph and the two exceptional cone families.  Thus `G` is
unexceptional.  At order at least six, the stronger manuscript Theorem 3
gives `η(G)≥2n-4`, hence the BKLPS target `2n-5`.  The only remaining
orders allowed by 2-connectivity are handled by the explicit small-order
check.  The public theorem performs this reduction rather than hiding it in
the numbered proof module.
-/

namespace BKLPS.External

open SimpleGraph

noncomputable section

universe u

/-- Bonamy--Knor--Lužar--Pinlou--Škrekovski, Theorem 4. -/
theorem bklpsTheorem4
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_two_connected : IsTwoConnected G)
    (h_noncomplete : ¬IsomorphicToKn G)
    (h_not_Kn2 : ¬IsomorphicToKnt G 2)
    (h_not_Knn2 : ¬IsomorphicToKnt G (Fintype.card V - 2)) :
    szegedWienerGap G ≥ (2 * Fintype.card V - 5 : ℤ) := by
  have hunexceptional : IsUnexceptional G := by
    rintro (h | h | h)
    · exact h_noncomplete h
    · exact h_not_Kn2 h
    · exact h_not_Knn2 h
  by_cases hsix : 6 ≤ Fintype.card V
  · have hmain := BKLPS.theorem3 G hsix hunexceptional h_two_connected
    omega
  · exact bklpsTheorem4SmallCheck G h_two_connected.1 (by omega)
      h_two_connected hunexceptional

end

end BKLPS.External
