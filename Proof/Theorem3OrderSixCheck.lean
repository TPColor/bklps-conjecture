import Proof.ExternalResults.GraphIsomorphismInvariants
import Proof.ExternalResults.FiniteGraphCheck

namespace BKLPS

open SimpleGraph
open External

noncomputable section

universe u

/-- At order six the three exceptional graphs have degree multisets
`5^6`, `5^2 4^3 2`, and `5^4 4^2`.  These degree patterns determine the
corresponding graph up to isomorphism. -/
private def orderSixExceptionalShapeBool (G : SimpleGraph (Fin 6))
    [DecidableRel G.Adj] : Bool :=
  let degree := fun v : Fin 6 =>
    ((Finset.univ : Finset (Fin 6)).filter fun w => G.Adj v w).card
  decide (∀ v, degree v = 5) ||
    decide (((Finset.univ.filter fun v => degree v = 5).card = 2) ∧
      ((Finset.univ.filter fun v => degree v = 4).card = 3) ∧
      ((Finset.univ.filter fun v => degree v = 2).card = 1)) ||
    decide (((Finset.univ.filter fun v => degree v = 5).card = 4) ∧
      ((Finset.univ.filter fun v => degree v = 4).card = 2))

/-- A small certificate that the degree-pattern shortcut recognizes only
the three exceptional isomorphism classes.  The expensive relabeling search
is therefore performed only on the 76 exceptional labeled graphs. -/
private theorem orderSixExceptionalShape_sound :
    ∀ E : Finset (OrderedEdge 6),
      orderSixExceptionalShapeBool (codedGraph E) = true →
      isExceptionalBool (codedGraph E) = true := by
  native_decide

/-- Executable exhaustive check on the `2^15` labeled edge sets.  This is the
finite labeled counterpart of the manuscript's 156-unlabeled-graph check and
avoids making the evaluator canonicalize every labeling. -/
private theorem orderSixEncodedCheck :
    ∀ E : Finset (OrderedEdge 6),
      isTwoConnectedBool (codedGraph E) = true →
      orderSixExceptionalShapeBool (codedGraph E) = false →
      finiteGap (codedGraph E) ≥ (8 : ℤ) := by
  native_decide

/-- The exhaustive computation, transferred from edge codes to Mathlib
simple graphs. -/
theorem orderSixCheckProof1
    (G : SimpleGraph (Fin 6))
    (h_two_connected : IsTwoConnected G)
    (h_unexceptional : IsUnexceptional G) :
    szegedWienerGap G ≥ (8 : ℤ) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  let E : Finset (OrderedEdge 6) := graphCode G
  have hgraph : codedGraph E = G := codedGraph_graphCode G
  have htwoCode : IsTwoConnected (codedGraph E) := by simpa [hgraph]
  have htwoBool : isTwoConnectedBool (codedGraph E) = true :=
    (isTwoConnectedBool_eq_true (codedGraph E)).2 htwoCode
  have hexcBool : orderSixExceptionalShapeBool (codedGraph E) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hexc
    have hexc' : isExceptionalBool (codedGraph E) = true :=
      orderSixExceptionalShape_sound E hexc
    have hexceptionalE : IsExceptional (codedGraph E) :=
      isExceptionalBool_eq_true_imp (codedGraph E) hexc'
    exact h_unexceptional (by simpa [hgraph] using hexceptionalE)
  have hcheck := orderSixEncodedCheck E htwoBool hexcBool
  rw [finiteGap_eq (codedGraph E) htwoCode.2.1] at hcheck
  simpa [hgraph] using hcheck

end

end BKLPS


/-!
The base case of Theorem 3.

The finite proof enumerates all graphs on `Fin 6`, retaining exactly the
2-connected unexceptional ones and verifying `szegedWienerGap ≥ 8`.  The
public statement below handles an arbitrary six-element vertex type:
`G.overFinIso` supplies a labeling, isomorphism invariance transports the
two hypotheses to the canonical graph, and the same invariance transports
the computed inequality back.  Thus the finite certificate proves the
literal order-six statement used by the induction.
-/

namespace BKLPS

open SimpleGraph
open External

noncomputable section

universe u

/-- The finite computation is performed on `Fin 6`; the manuscript's
order-six assertion follows for any six-element vertex type by relabeling. -/
theorem orderSixCheck
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_order : Fintype.card V = 6)
    (h_two_connected : IsTwoConnected G)
    (h_unexceptional : IsUnexceptional G) :
    szegedWienerGap G ≥ (8 : ℤ) := by
  /- Choose a labeling of `V(G)` by `Fin 6`.  Isomorphism preserves
  2-connectivity, all three exceptional families, and the gap.  The finite
  certificate is applied only after transporting both hypotheses to the
  relabeled graph, and its conclusion is then transported back to `G`. -/
  let e := G.overFinIso h_order
  have htwoFin : IsTwoConnected (G.overFin h_order) :=
    (isoIsTwoConnected e).mp h_two_connected
  have hunexceptionalFin : IsUnexceptional (G.overFin h_order) :=
    (isoIsUnexceptional e).mp h_unexceptional
  have hfinite : szegedWienerGap (G.overFin h_order) ≥ (8 : ℤ) :=
    orderSixCheckProof1 (G.overFin h_order) htwoFin hunexceptionalFin
  rw [isoSzegedWienerGap e] at hfinite
  exact hfinite

end

end BKLPS
