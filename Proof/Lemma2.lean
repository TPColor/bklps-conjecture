import Proof.ExternalResults.GraphIsomorphismInvariants
import Proof.ExternalResults.FiniteGraphCheck
import Proof.Definitions
import Proof.ExternalResults.BKLPSLemma7
import Proof.ExternalResults.BlockStructure
import Proof.Lemma2ExceptionalCones
import Proof.ExternalResults.BKLPSLemma7GoodsLowerBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.RingNF
import Proof.Lemma2Proof2
import Proof.Lemma2Proof3

/-! Small-order (`n = 4,5`) part of the exceptional-deletion proof. -/

namespace BKLPS

open SimpleGraph

noncomputable section

universe u

open External

/-- Executable form of the dominated closed-neighborhood condition. -/
private def closedNeighborhoodSubsetBool {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (u v : Fin n) : Bool :=
  decide (∀ x : Fin n, (x = u ∨ G.Adj u x) → (x = v ∨ G.Adj v x))

private theorem closedNeighborhoodSubsetBool_eq_true {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    closedNeighborhoodSubsetBool G u v = true ↔
      closedNeighborhood G u ⊆ closedNeighborhood G v := by
  rw [closedNeighborhoodSubsetBool, decide_eq_true_eq, Finset.subset_iff]
  constructor
  · intro h x hx
    have hx' := h x (by
      simpa [closedNeighborhood, openNeighborhood, eq_comm] using hx)
    simpa [closedNeighborhood, openNeighborhood, eq_comm] using hx'
  · intro h x hx
    have hx' := h (by
      simpa [closedNeighborhood, openNeighborhood, eq_comm] using hx)
    simpa [closedNeighborhood, openNeighborhood, eq_comm] using hx'

private def exceptionalShapeFour (G : SimpleGraph (Fin 4))
    [DecidableRel G.Adj] : Bool :=
  let degree := fun v : Fin 4 =>
    ((Finset.univ : Finset (Fin 4)).filter fun w => G.Adj v w).card
  decide (∀ v, degree v = 3) ||
    decide (((Finset.univ.filter fun v => degree v = 3).card = 2) ∧
      ((Finset.univ.filter fun v => degree v = 2).card = 2))

private def exceptionalShapeFive (G : SimpleGraph (Fin 5))
    [DecidableRel G.Adj] : Bool :=
  let degree := fun v : Fin 5 =>
    ((Finset.univ : Finset (Fin 5)).filter fun w => G.Adj v w).card
  decide (∀ v, degree v = 4) ||
    decide (((Finset.univ.filter fun v => degree v = 4).card = 2) ∧
      ((Finset.univ.filter fun v => degree v = 3).card = 2) ∧
      ((Finset.univ.filter fun v => degree v = 2).card = 1)) ||
    decide (((Finset.univ.filter fun v => degree v = 4).card = 3) ∧
      ((Finset.univ.filter fun v => degree v = 3).card = 2))

private theorem exceptionalShapeFour_sound :
    ∀ E : Finset (OrderedEdge 4),
      exceptionalShapeFour (codedGraph E) = true →
      isExceptionalBool (codedGraph E) = true := by
  native_decide

private theorem exceptionalShapeFive_sound :
    ∀ E : Finset (OrderedEdge 5),
      exceptionalShapeFive (codedGraph E) = true →
      isExceptionalBool (codedGraph E) = true := by
  native_decide

/-- At order four the hypotheses themselves leave no counterexample. -/
private theorem lemma2OrderFourEncodedCheck :
    ∀ E : Finset (OrderedEdge 4),
      isTwoConnectedBool (codedGraph E) = true →
      exceptionalShapeFour (codedGraph E) = false →
      ∀ u v : Fin 4,
      u ≠ v → closedNeighborhoodSubsetBool (codedGraph E) u v = true →
      finiteGap (codedGraph E) - finiteGap (deleteVertex (codedGraph E) u) ≥
        (2 : ℤ) := by
  native_decide

/-- At order five, `G-u ≅ K₄²` is equivalently the five-edge condition used
by the executable check. -/
private theorem lemma2OrderFiveEncodedCheck :
    ∀ E : Finset (OrderedEdge 5),
      isTwoConnectedBool (codedGraph E) = true →
      exceptionalShapeFive (codedGraph E) = false →
      ∀ u v : Fin 5,
      u ≠ v → closedNeighborhoodSubsetBool (codedGraph E) u v = true →
      (deleteVertex (codedGraph E) u).edgeFinset.card = 5 →
      finiteGap (codedGraph E) - finiteGap (deleteVertex (codedGraph E) u) ≥
        (3 : ℤ) := by
  native_decide

private theorem kFourTwoEdgeCount : (Knt 4 2).edgeFinset.card = 5 := by
  native_decide

private theorem lemma2OrderFourFinCheck
    (G : SimpleGraph (Fin 4)) (h_unexceptional : IsUnexceptional G)
    (h_two_connected : IsTwoConnected G) (u v : Fin 4) (huv : u ≠ v)
    (hsub : closedNeighborhood G u ⊆ closedNeighborhood G v) :
    szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥ (2 : ℤ) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  let E : Finset (OrderedEdge 4) := graphCode G
  have hgraph : codedGraph E = G := codedGraph_graphCode G
  have htwoCode : IsTwoConnected (codedGraph E) := by simpa [hgraph]
  have htwoBool := (isTwoConnectedBool_eq_true (codedGraph E)).2 htwoCode
  have hexcBool : exceptionalShapeFour (codedGraph E) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hexc
    have hexc' := exceptionalShapeFour_sound E hexc
    exact h_unexceptional (by
      simpa [hgraph] using isExceptionalBool_eq_true_imp (codedGraph E) hexc')
  have hsubBool : closedNeighborhoodSubsetBool (codedGraph E) u v = true :=
    (closedNeighborhoodSubsetBool_eq_true (codedGraph E) u v).2 (by simpa [hgraph])
  have hcheck := lemma2OrderFourEncodedCheck E htwoBool hexcBool u v huv hsubBool
  rw [finiteGap_eq (codedGraph E) htwoCode.2.1,
    finiteGap_eq (deleteVertex (codedGraph E) u) (htwoCode.2.2 u)] at hcheck
  simpa [hgraph] using hcheck

private theorem lemma2OrderFiveFinCheck
    (G : SimpleGraph (Fin 5)) (h_unexceptional : IsUnexceptional G)
    (h_two_connected : IsTwoConnected G) (u v : Fin 5) (huv : u ≠ v)
    (hsub : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (hdelete : IsomorphicToKnt (deleteVertex G u) 2) :
    szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥ (3 : ℤ) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  let E : Finset (OrderedEdge 5) := graphCode G
  have hgraph : codedGraph E = G := codedGraph_graphCode G
  have htwoCode : IsTwoConnected (codedGraph E) := by simpa [hgraph]
  have htwoBool := (isTwoConnectedBool_eq_true (codedGraph E)).2 htwoCode
  have hexcBool : exceptionalShapeFive (codedGraph E) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hexc
    have hexc' := exceptionalShapeFive_sound E hexc
    exact h_unexceptional (by
      simpa [hgraph] using isExceptionalBool_eq_true_imp (codedGraph E) hexc')
  have hsubBool : closedNeighborhoodSubsetBool (codedGraph E) u v = true :=
    (closedNeighborhoodSubsetBool_eq_true (codedGraph E) u v).2 (by simpa [hgraph])
  have hcardDelete : Fintype.card {x : Fin 5 // x ≠ u} = 4 := by
    simpa using Fintype.card_subtype_compl (fun x : Fin 5 => x = u)
  have hdelete' : Nonempty (deleteVertex G u ≃g Knt 4 2) := by
    unfold IsomorphicToKnt at hdelete
    rw [hcardDelete] at hdelete
    exact hdelete
  obtain ⟨f⟩ := hdelete'
  have hedgeG : (deleteVertex G u).edgeFinset.card = 5 := by
    have hedge := f.card_edgeFinset_eq
    rw [kFourTwoEdgeCount] at hedge
    exact hedge
  have hedgeCode : (deleteVertex (codedGraph E) u).edgeFinset.card = 5 := by
    let eGraph : codedGraph E ≃g G :=
      { toEquiv := Equiv.refl _
        map_rel_iff' := by simpa [hgraph] }
    calc
      (deleteVertex (codedGraph E) u).edgeFinset.card =
          (deleteVertex G u).edgeFinset.card :=
        (deleteVertexIso eGraph u).card_edgeFinset_eq
      _ = 5 := hedgeG
  have hcheck := lemma2OrderFiveEncodedCheck E htwoBool hexcBool u v huv
    hsubBool hedgeCode
  rw [finiteGap_eq (codedGraph E) htwoCode.2.1,
    finiteGap_eq (deleteVertex (codedGraph E) u) (htwoCode.2.2 u)] at hcheck
  simpa [hgraph] using hcheck

/-- The finite small-order part of Lemma 2. -/
theorem lemma2Proof1
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_order_lower : Fintype.card V ≥ 4)
    (h_order_upper : Fintype.card V ≤ 5)
    (h_unexceptional : IsUnexceptional G)
    (h_two_connected : IsTwoConnected G)
    (u v : V) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete : IsomorphicToKnt (deleteVertex G u) 2 ∨
      IsomorphicToKnt (deleteVertex G u) (Fintype.card V - 3)) :
    szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥
      (Fintype.card V : ℤ) - 2 := by
  classical
  have hcard : Fintype.card V = 4 ∨ Fintype.card V = 5 := by omega
  rcases hcard with hfour | hfive
  · let K := G.overFin hfour
    let e : G ≃g K := G.overFinIso hfour
    have hresult := lemma2OrderFourFinCheck K
      ((External.isoIsUnexceptional e).mp h_unexceptional)
      ((External.isoIsTwoConnected e).mp h_two_connected)
      (e u) (e v) (e.injective.ne h_distinct)
      ((isoClosedNeighborhoodSubset e u v).mp h_neighborhood)
    rw [External.isoSzegedWienerGap e,
      External.isoSzegedWienerGap (External.deleteVertexIso e u)] at hresult
    simpa [hfour] using hresult
  · let K := G.overFin hfive
    let e : G ≃g K := G.overFinIso hfive
    have hdeleteTwo : IsomorphicToKnt (deleteVertex G u) 2 := by
      rcases h_delete with h | h
      · exact h
      · simpa [hfive] using h
    have hdeleteK : IsomorphicToKnt (deleteVertex K (e u)) 2 :=
      (External.isoIsomorphicToKnt (External.deleteVertexIso e u) 2).mp hdeleteTwo
    have hresult := lemma2OrderFiveFinCheck K
      ((External.isoIsUnexceptional e).mp h_unexceptional)
      ((External.isoIsTwoConnected e).mp h_two_connected)
      (e u) (e v) (e.injective.ne h_distinct)
      ((isoClosedNeighborhoodSubset e u v).mp h_neighborhood) hdeleteK
    rw [External.isoSzegedWienerGap e,
      External.isoSzegedWienerGap (External.deleteVertexIso e u)] at hresult
    simpa [hfive] using hresult

end

end BKLPS


/-!
Main route of the manuscript's Exceptional Deletion Lemma.

Write `H = G-u`.  Order four is impossible and order five is a finite
check.  For `n ≥ 6`, BKLPS Lemma 7 supplies

`gap G - gap H = ∑_x pairGap G u x + q`,

with `pairGap G u x ≥ 2(p_x-1)` and `q ≥ 2t` when the neighborhood of
`u` contains `t` nonedges.

If `H ≅ K_(n-1)^2`, choose its degree-two vertex `z`, its neighbors
`a,b`, the remaining clique vertices `R`, and `S=N_G(u)`.  The proof splits
on `z ∈ S`; in the latter case it splits again on `T=R∩S`.  The three
numerical lower bounds are

* `2(n-2-s)(s-1)` when `z ∉ S`;
* `2t(n-3-t)` when `z ∈ S` and `T` is nonempty;
* `2+(n-4)` in the final two-neighbor configuration.

Each is at least `n-2`.  If `H ≅ K_(n-1)^(n-3)=K_(n-1)-e`, all but at
most one vertex outside `S` have `p_x=s`, giving
`2(s-1)(n-1-s)-2 ≥ n-2`.
-/

namespace BKLPS

open SimpleGraph

noncomputable section

universe u

/-- **Lemma 2 (Exceptional Deletion).** This is the manuscript statement with
`n` represented by the cardinality of the vertex type. -/
theorem lemma2
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_order : Fintype.card V ≥ 4)
    (h_unexceptional : IsUnexceptional G)
    (h_two_connected : IsTwoConnected G)
    (u v : V) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete : IsomorphicToKnt (deleteVertex G u) 2 ∨
      IsomorphicToKnt (deleteVertex G u) (Fintype.card V - 3)) :
    szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥
      (Fintype.card V : ℤ) - 2 := by
  /- Keep the manuscript's final case split at the public theorem.  Orders
  four and five are the finite check in `lemma2Proof1`.  From order six on,
  the two disjuncts are exactly Case 1 (`K_(n-1)^2`) and Case 2
  (`K_(n-1)^(n-3)`) of the informal proof. -/
  by_cases h_small : Fintype.card V ≤ 5
  · exact lemma2Proof1 G h_order h_small h_unexceptional h_two_connected u v
      h_distinct h_neighborhood h_delete
  · have h_large : Fintype.card V ≥ 6 := by omega
    rcases h_delete with h_K2 | h_Klarge
    · exact lemma2Proof2 G h_large h_unexceptional h_two_connected u v h_distinct
        h_neighborhood h_K2
    · exact lemma2Proof3 G h_large h_unexceptional h_two_connected u v h_distinct
        h_neighborhood h_Klarge

end

end BKLPS
