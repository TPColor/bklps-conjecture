import Proof.ExternalResults.GraphIsomorphismInvariants
import Proof.ExternalResults.FiniteGraphCheck

/-!
The order-five estimate at the bottom of the block-extension induction.

Every graph on `Fin 5` is encoded by a subset of the ten possible unordered
edges.  The native certificate exhausts those codes, filters for
2-connectivity and failure of all three exceptional predicates, and checks
the integer inequality `finiteGap ≥ 5`.  The executable definitions are
linked to the mathematical predicates and to `szegedWienerGap` before the
certificate is used.

For an arbitrary five-element vertex type, `G.overFinIso` relabels the
graph by `Fin 5`.  Isomorphism invariance transports 2-connectivity and
unexceptionality to the coded graph, and transports the verified gap bound
back.  The result is the exact `2m-5` exceptional small-order estimate used
when an induction block extension has `m=5`; it is not assumed as an opaque
finite fact.
-/

namespace BKLPS

open SimpleGraph
open External

noncomputable section

universe u

private theorem orderFiveEncodedLowerBound :
    ∀ E : Finset (OrderedEdge 5),
      isTwoConnectedBool (codedGraph E) = true →
      isExceptionalBool (codedGraph E) = false →
      finiteGap (codedGraph E) ≥ (5 : ℤ) := by
  native_decide

private theorem orderFiveFinLowerBound
    (G : SimpleGraph (Fin 5))
    (htwo : IsTwoConnected G) (hunexceptional : IsUnexceptional G) :
    szegedWienerGap G ≥ (5 : ℤ) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  let E : Finset (OrderedEdge 5) := graphCode G
  have hgraph : codedGraph E = G := codedGraph_graphCode G
  have htwoCode : IsTwoConnected (codedGraph E) := by simpa [hgraph]
  have htwoBool : isTwoConnectedBool (codedGraph E) = true :=
    (isTwoConnectedBool_eq_true (codedGraph E)).2 htwoCode
  have hexcBool : isExceptionalBool (codedGraph E) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hexc
    exact hunexceptional (by
      simpa [hgraph] using isExceptionalBool_eq_true_imp (codedGraph E) hexc)
  have hcheck := orderFiveEncodedLowerBound E htwoBool hexcBool
  rw [finiteGap_eq (codedGraph E) htwoCode.2.1] at hcheck
  simpa [hgraph] using hcheck

/-- Every unexceptional 2-connected graph of order five has gap at least
five, exactly the `2m-5` estimate needed in BKLPS Theorem 4. -/
theorem orderFiveLowerBound
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hcard : Fintype.card V = 5)
    (htwo : IsTwoConnected G) (hunexceptional : IsUnexceptional G) :
    szegedWienerGap G ≥ (5 : ℤ) := by
  exact finiteUnexceptionalCheckOfFin G hcard 5 orderFiveFinLowerBound
    htwo hunexceptional

end

end BKLPS
