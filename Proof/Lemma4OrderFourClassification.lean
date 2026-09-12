import Proof.ExternalResults.FiniteGraphCheck
import Proof.ExternalResults.GraphIsomorphismInvariants

/-!
The small classification used verbatim in Lemma 4: a 2-connected graph on
four vertices is `C₄`, `K₄²`, or `K₄`; hence the unexceptional case is `C₄`.
The six possible edges make this a transparent exhaustive verification.

Concretely, a graph on `Fin 4` is encoded by a subset of those six edges.
The native certificate assumes the executable 2-connectivity test succeeds
and the executable exceptional-family test fails, then verifies that the
isomorphism test with `C₄` succeeds.  Soundness lemmas turn each Boolean
fact into its mathematical counterpart.  For an arbitrary four-element
vertex type, `overFinIso` transports the hypotheses to the canonical code;
the certified cycle isomorphism is then composed with that relabeling to
produce `G ≃g C₄`.  This is the classification invoked in the `m=5`
branch of Lemma 4.
-/

namespace BKLPS

open SimpleGraph
open External

noncomputable section

universe u

private instance : DecidableRel (Cn 4).Adj := by
  dsimp [Cn]
  infer_instance

private theorem orderFourCodeCheck :
    ∀ E : Finset (OrderedEdge 4),
      isTwoConnectedBool (codedGraph E) = true →
      isExceptionalBool (codedGraph E) = false →
      isomorphicBool (codedGraph E) (Cn 4) = true := by
  native_decide

/-- Every unexceptional 2-connected graph of order four is a four-cycle. -/
theorem orderFour_unexceptional_twoConnected_isCycle
    {W : Type u} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (hcard : Fintype.card W = 4)
    (htwo : IsTwoConnected G) (hunexceptional : IsUnexceptional G) :
    Nonempty (G ≃g Cn 4) := by
  letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
  let K := G.overFin hcard
  letI : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  let e : G ≃g K := G.overFinIso hcard
  have htwoK : IsTwoConnected K := (isoIsTwoConnected e).mp htwo
  have hunK : IsUnexceptional K := (isoIsUnexceptional e).mp hunexceptional
  let E := graphCode K
  have hcode : codedGraph E = K := codedGraph_graphCode K
  have htwoBool : isTwoConnectedBool (codedGraph E) = true :=
    (isTwoConnectedBool_eq_true (codedGraph E)).mpr (hcode ▸ htwoK)
  have hexceptionalFalse : isExceptionalBool (codedGraph E) = false := by
    cases h : isExceptionalBool (codedGraph E) with
    | false => rfl
    | true =>
        exfalso
        have hexCode := isExceptionalBool_eq_true_imp (codedGraph E) h
        have hexK : IsExceptional K := by
          rw [← hcode]
          exact hexCode
        exact hunK hexK
  have hisoCode := isomorphicBool_eq_true_imp (codedGraph E) (Cn 4)
    (orderFourCodeCheck E htwoBool hexceptionalFalse)
  rcases hisoCode with ⟨f⟩
  rw [hcode] at f
  exact ⟨e.trans f⟩

end

end BKLPS
