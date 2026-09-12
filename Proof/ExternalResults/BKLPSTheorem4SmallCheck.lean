import Proof.Theorem3OrderFiveLowerBound

/-!
The orders below six in the literal statement of BKLPS Theorem 4.

A 2-connected graph has at least three vertices.  At orders three and four,
the file exhausts all canonical edge sets, checks the Boolean forms of
2-connectivity and unexceptionality, and verifies the respective targets
`2n-5 = 1` and `2n-5 = 3`.  At order five it reuses the stronger manuscript
certificate `gap ≥ 5`.

Each Boolean test is converted back to the mathematical graph predicate and
each finite gap to `szegedWienerGap`.  The final theorem splits the cardinal
into `3`, `4`, or `5`, relabels the graph by the matching `Fin n`, applies
the corresponding certificate, and transports the result back.  This is
why `bklpsTheorem4` can retain the paper's statement without an artificial
assumption `6 ≤ n`.
-/

namespace BKLPS.External

open SimpleGraph

noncomputable section

universe u

private theorem orderThreeEncoded :
    ∀ E : Finset (OrderedEdge 3),
      isTwoConnectedBool (codedGraph E) = true →
      isExceptionalBool (codedGraph E) = false →
      finiteGap (codedGraph E) ≥ (1 : ℤ) := by
  native_decide

private theorem orderFourEncoded :
    ∀ E : Finset (OrderedEdge 4),
      isTwoConnectedBool (codedGraph E) = true →
      isExceptionalBool (codedGraph E) = false →
      finiteGap (codedGraph E) ≥ (3 : ℤ) := by
  native_decide

private theorem orderThreeFin
    (G : SimpleGraph (Fin 3))
    (htwo : IsTwoConnected G) (hun : IsUnexceptional G) :
    szegedWienerGap G ≥ (1 : ℤ) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  let E := graphCode G
  have hgraph : codedGraph E = G := codedGraph_graphCode G
  have htwoCode : IsTwoConnected (codedGraph E) := by simpa [hgraph]
  have htwoBool := (isTwoConnectedBool_eq_true (codedGraph E)).2 htwoCode
  have hexc : isExceptionalBool (codedGraph E) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hun (by simpa [hgraph] using
      isExceptionalBool_eq_true_imp (codedGraph E) h)
  have h := orderThreeEncoded E htwoBool hexc
  rw [finiteGap_eq (codedGraph E) htwoCode.2.1] at h
  simpa [hgraph] using h

private theorem orderFourFin
    (G : SimpleGraph (Fin 4))
    (htwo : IsTwoConnected G) (hun : IsUnexceptional G) :
    szegedWienerGap G ≥ (3 : ℤ) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  let E := graphCode G
  have hgraph : codedGraph E = G := codedGraph_graphCode G
  have htwoCode : IsTwoConnected (codedGraph E) := by simpa [hgraph]
  have htwoBool := (isTwoConnectedBool_eq_true (codedGraph E)).2 htwoCode
  have hexc : isExceptionalBool (codedGraph E) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hun (by simpa [hgraph] using
      isExceptionalBool_eq_true_imp (codedGraph E) h)
  have h := orderFourEncoded E htwoBool hexc
  rw [finiteGap_eq (codedGraph E) htwoCode.2.1] at h
  simpa [hgraph] using h

theorem bklpsTheorem4SmallCheck
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hupper : Fintype.card V ≤ 5)
    (htwo : IsTwoConnected G) (hun : IsUnexceptional G) :
    szegedWienerGap G ≥ (2 * Fintype.card V - 5 : ℤ) := by
  have hc : Fintype.card V = 3 ∨ Fintype.card V = 4 ∨
      Fintype.card V = 5 := by omega
  rcases hc with h3 | h4 | h5
  · simpa [h3] using finiteUnexceptionalCheckOfFin G h3 1 orderThreeFin htwo hun
  · simpa [h4] using finiteUnexceptionalCheckOfFin G h4 3 orderFourFin htwo hun
  · simpa [h5] using orderFiveLowerBound G h5 htwo hun

end

end BKLPS.External
