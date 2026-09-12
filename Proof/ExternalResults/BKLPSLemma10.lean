import Proof.ExternalResults.BKLPSGoodEdges
import Proof.ExternalResults.BlockStructure
import Proof.ExternalResults.BKLPSLemma10Proof1

/-!
Main route of BKLPS Lemma 10.

Root a breadth-first layering at a vertex `a` and suppose its contribution
is at most three.  Claim P1 controls vertices with more than one predecessor;
claim P2 controls horizontal edges in a layer.  The absence of proper
closed-neighborhood containment rules out a simultaneous P1/P2
configuration, two overlapping P2 edges, and two disjoint P2 edges.  The
terminal P1 and P2 configurations are then eliminated using extra good
edges.  Consequently every vertex contributes at least four.

Summing `c_G(a)≥4` over all vertices gives `4n`.  Since every unordered
pair contribution occurs at both endpoints of this vertex sum,
`∑_a c_G(a)=2η(G)`, and therefore `η(G)≥2n`.
-/

namespace BKLPS.External

open SimpleGraph

noncomputable section

universe u

/-- Bonamy--Knor--Lužar--Pinlou--Škrekovski, Lemma 10. -/
theorem bklpsLemma10
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_two_connected : IsTwoConnected G)
    (h_noncomplete : ¬IsomorphicToKn G)
    (h_not_C5 : ¬IsomorphicToCn G 5)
    (h_no_containment : ∀ u v : V, u ≠ v →
      ¬(closedNeighborhood G u ⊆ closedNeighborhood G v)) :
    (∀ u : V, vertexContribution G u ≥ (4 : ℤ)) ∧
      szegedWienerGap G ≥ (2 * Fintype.card V : ℤ) := by
  /- The BFS part supplies the local bound at an arbitrary root.  Sum it
  before invoking the good-edge double count, so the public proof retains
  both of BKLPS's mathematical steps. -/
  have h_vertex := bklpsLemma10Proof1 G h_two_connected h_noncomplete h_not_C5
    h_no_containment
  have h_sum_lower :
      (∑ _a : V, (4 : ℤ)) ≤ ∑ a : V, vertexContribution G a := by
    exact Finset.sum_le_sum fun a _ => h_vertex a
  have h_double_count := sum_vertexContribution_eq_two_mul_gap G
  have h_gap : szegedWienerGap G ≥ (2 * Fintype.card V : ℤ) := by
    rw [h_double_count] at h_sum_lower
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h_sum_lower
    omega
  exact ⟨h_vertex, h_gap⟩

end

end BKLPS.External
