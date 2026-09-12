import Proof.ExternalResults.GraphIsomorphismInvariants
import Proof.ExternalResults.FiniteGraphCheck
import Proof.Theorem3
import Proof.Theorem6Proof1
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenClassification
import Std.Tactic.BVDecide
import Batteries.Data.BitVec.Lemmas

/-! ## Compact encoding for the residual finite check -/

namespace BKLPS.External.OrderTen

abbrev Word := BitVec 12

def edgeIndex (a b : Nat) : Nat :=
  if a < b then b * (b - 1) / 2 + a else a * (a - 1) / 2 + b

def adj (g : BitVec 45) (a b : Nat) : Bool :=
  decide (a ≠ b) && g.getLsbD (edgeIndex a b)

theorem edgeIndex_comm (a b : Nat) : edgeIndex a b = edgeIndex b a := by
  by_cases hab : a < b
  · have hba : ¬ b < a := Nat.not_lt_of_ge (Nat.le_of_lt hab)
    simp [edgeIndex, hab, hba]
  · by_cases hba : b < a
    · simp [edgeIndex, hab, hba]
    · have hab' : a = b := Nat.le_antisymm (Nat.le_of_not_gt hba)
          (Nat.le_of_not_gt hab)
      simp [edgeIndex, hab']

/-- The simple graph represented by a 45-bit edge word. -/
def encodedGraph (g : BitVec 45) : SimpleGraph (Fin 10) where
  Adj a b := adj g a b = true
  symm a b h := by
    simpa [adj, edgeIndex_comm, ne_comm] using h
  loopless a := by simp [adj]

@[simp] theorem encodedGraph_adj (g : BitVec 45) (a b : Fin 10) :
    (encodedGraph g).Adj a b ↔ adj g a b = true := Iff.rfl

/-- The rank of a canonical unordered edge in the 45-bit word. -/
def edgeRank (e : OrderedEdge 10) : Fin 45 := ⟨edgeIndex e.1.1 e.1.2, by
  rcases e with ⟨⟨a, b⟩, hab⟩
  change a.val < b.val at hab
  change edgeIndex a.val b.val < 45
  rw [edgeIndex, if_pos hab]
  have hb : b.val ≤ 9 := by omega
  have hbsub : b.val - 1 ≤ 8 := by omega
  have hprod : b.val * (b.val - 1) ≤ 72 := Nat.mul_le_mul hb hbsub
  omega⟩

theorem edgeRank_injective : Function.Injective edgeRank := by
  decide

/-- Canonical unordered edges are in bijection with the bit positions. -/
noncomputable def edgeEquiv : OrderedEdge 10 ≃ Fin 45 :=
  Equiv.ofBijective edgeRank <|
    (Fintype.bijective_iff_injective_and_card edgeRank).2 ⟨edgeRank_injective, by
      decide⟩

@[simp] theorem edgeEquiv_apply (e : OrderedEdge 10) :
    edgeEquiv e = edgeRank e := rfl

/-- Encode a graph by reading its adjacency relation on the 45 canonical
unordered edges. -/
noncomputable def graphBits
    (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj] : BitVec 45 :=
  BitVec.ofFnLE fun i =>
    let e := edgeEquiv.symm i
    decide (G.Adj e.1.1 e.1.2)

@[simp] theorem graphBits_get_edgeRank
    (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (e : OrderedEdge 10) :
    (graphBits G).getLsbD (edgeRank e).val =
      decide (G.Adj e.1.1 e.1.2) := by
  simp [graphBits, ← edgeEquiv_apply]

/-- Every graph on `Fin 10` is represented by its 45-bit edge word. -/
theorem encodedGraph_graphBits
    (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj] :
    encodedGraph (graphBits G) = G := by
  ext a b
  rcases lt_trichotomy a b with hab | hab | hab
  · let e : OrderedEdge 10 := ⟨(a, b), hab⟩
    have hrank : edgeIndex a.val b.val = (edgeRank e).val := by
      simp [edgeRank, e]
    have habne : a.val ≠ b.val := by omega
    change ((decide (a.val ≠ b.val) &&
      (graphBits G).getLsbD (edgeIndex a.val b.val)) = true) ↔ G.Adj a b
    rw [hrank, graphBits_get_edgeRank G e]
    simp [habne, e]
  · subst b
    simp [encodedGraph, adj]
  · let e : OrderedEdge 10 := ⟨(b, a), hab⟩
    have hrank : edgeIndex a.val b.val = (edgeRank e).val := by
      simp [edgeRank, edgeIndex_comm, e]
    have habne : a.val ≠ b.val := by omega
    change ((decide (a.val ≠ b.val) &&
      (graphBits G).getLsbD (edgeIndex a.val b.val)) = true) ↔ G.Adj a b
    rw [hrank, graphBits_get_edgeRank G e]
    simp [habne, e]
    exact G.adj_comm b a

instance (g : BitVec 45) : DecidableRel (encodedGraph g).Adj := by
  intro a b
  exact inferInstanceAs (Decidable (adj g a b = true))

end BKLPS.External.OrderTen

namespace BKLPS.External

open SimpleGraph

noncomputable section

universe u

/-- The residual dominated-deletion case follows from the checked low-gap
classification. The hypotheses are retained for compatibility with the
structural decomposition below. -/
theorem bklpsOrderTenDominatedDeletionComputation
    (G : SimpleGraph (Fin 10))
    (h_unexceptional : IsUnexceptional G)
    (h_two_connected : IsTwoConnected G)
    (u v : Fin 10) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete_two_connected : IsTwoConnected (deleteVertex G u))
    (h_delete_noncomplete : ¬IsomorphicToKn (deleteVertex G u))
    (h_delete_unexceptional : IsUnexceptional (deleteVertex G u)) :
    szegedWienerGap G ≥ (20 : ℤ) := by
  exact OrderTenCertificate.orderTenBound G (by simp) h_two_connected h_unexceptional

/-- If a dominated deletion is exceptional, completeness contradicts the
branch assumption and the two cone families are handled by Lemma 2 and the
closed formula from Theorem 1. -/
private theorem orderTenExceptionalDeletion
    (G : SimpleGraph (Fin 10))
    (h_unexceptional : IsUnexceptional G)
    (h_two_connected : IsTwoConnected G)
    (u v : Fin 10) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete_noncomplete : ¬IsomorphicToKn (deleteVertex G u))
    (h_exceptional : IsExceptional (deleteVertex G u)) :
    szegedWienerGap G ≥ (20 : ℤ) := by
  classical
  have h_card_delete :
      Fintype.card {x : Fin 10 // x ≠ u} = 9 := by
    simp
  rcases h_exceptional with h_complete | h_K2 | h_Klarge
  · exact False.elim (h_delete_noncomplete h_complete)
  · have h_step := BKLPS.lemma2 G (by simp) h_unexceptional
      h_two_connected u v h_distinct h_neighborhood (Or.inl h_K2)
    have h_gap := BKLPS.theorem1OfIsomorphicToKnt
      (deleteVertex G u) 2 (by omega) (by omega) h_K2
    rw [h_card_delete] at h_gap
    norm_num at h_step h_gap
    omega
  · have h_Klarge' : IsomorphicToKnt (deleteVertex G u) 7 := by
      simpa [h_card_delete] using h_Klarge
    have h_step := BKLPS.lemma2 G (by simp) h_unexceptional
      h_two_connected u v h_distinct h_neighborhood (Or.inr h_Klarge')
    have h_gap := BKLPS.theorem1OfIsomorphicToKnt
      (deleteVertex G u) 7 (by omega) (by omega) h_Klarge'
    rw [h_card_delete] at h_gap
    norm_num at h_step h_gap
    omega

/-- The broad order-ten computation follows from the existing structural
lemmas and the single residual dominated-deletion check above. -/
theorem bklpsOrderTenComputation
    (G : SimpleGraph (Fin 10))
    (h_two_connected : IsTwoConnected G)
    (h_unexceptional : IsUnexceptional G) :
    szegedWienerGap G ≥ (20 : ℤ) := by
  classical
  by_cases hno : ∀ x y : Fin 10, x ≠ y →
      ¬(closedNeighborhood G x ⊆ closedNeighborhood G y)
  · have h_noncomplete : ¬IsomorphicToKn G := by
      intro h_complete
      exact h_unexceptional (Or.inl h_complete)
    have h_not_C5 : ¬IsomorphicToCn G 5 := by
      rintro ⟨e⟩
      have : Fintype.card (Fin 10) = 5 := by
        simpa [Cn] using Fintype.card_congr e.toEquiv
      norm_num at this
    simpa using
      (BKLPS.External.bklpsLemma10 G h_two_connected h_noncomplete
        h_not_C5 hno).2
  · have hexists : ∃ x y : Fin 10, x ≠ y ∧
        closedNeighborhood G x ⊆ closedNeighborhood G y := by
      push_neg at hno
      exact hno
    by_cases hgood : ∃ x y : Fin 10, x ≠ y ∧
        closedNeighborhood G x ⊆ closedNeighborhood G y ∧
        IsTwoConnected (deleteVertex G x) ∧
        ¬IsomorphicToKn (deleteVertex G x)
    · obtain ⟨x, y, hxy, hsub, hdeleteTwo, hdeleteNoncomplete⟩ := hgood
      by_cases hdeleteUn : IsUnexceptional (deleteVertex G x)
      · exact bklpsOrderTenDominatedDeletionComputation G
          h_unexceptional h_two_connected x y hxy hsub hdeleteTwo
          hdeleteNoncomplete hdeleteUn
      · have hdeleteExceptional : IsExceptional (deleteVertex G x) := by
          exact Classical.not_not.mp hdeleteUn
        exact orderTenExceptionalDeletion G h_unexceptional h_two_connected
          x y hxy hsub hdeleteNoncomplete hdeleteExceptional
    · have hdeletions : ∀ x y : Fin 10, x ≠ y →
          closedNeighborhood G x ⊆ closedNeighborhood G y →
          IsomorphicToKn (deleteVertex G x) ∨
            ¬IsTwoConnected (deleteVertex G x) := by
        intro x y hxy hsub
        by_cases hcomplete : IsomorphicToKn (deleteVertex G x)
        · exact Or.inl hcomplete
        · right
          intro hdeleteTwo
          exact hgood ⟨x, y, hxy, hsub, hdeleteTwo, hcomplete⟩
      obtain ⟨x, y, hxy, hsub⟩ := hexists
      exact BKLPS.theorem6Proof1 10 G rfl (by simp)
        h_unexceptional h_two_connected x y hxy hsub hdeletions

end

end BKLPS.External


/-!
The order-ten computation cited by BKLPS for the base of the conjectured
`2n` bound.

The structural proof above dispatches the no-containment, exceptional
deletion, and block-decomposition cases mathematically. The remaining
dominated-deletion case is proved by `OrderTenClassification`: checked
labeling witnesses cover every graph below gap `2n` at orders five through
ten, and all three order-ten representatives are exceptional. The
statement below then handles an arbitrary graph of order ten: relabel by
`G.overFinIso`, carry both hypotheses across that isomorphism, apply the
canonical result, and use gap invariance to return to the original labels.
-/

namespace BKLPS.External

open SimpleGraph

noncomputable section

universe u

/-- The BKLPS computation is stated on the canonical type `Fin 10`; the
paper's order-ten assertion follows for an arbitrary vertex type by
relabeling. -/
theorem bklpsOrderTenCheck
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_order : Fintype.card V = 10)
    (h_two_connected : IsTwoConnected G)
    (h_unexceptional : IsUnexceptional G) :
    szegedWienerGap G ≥ (20 : ℤ) := by
  /- The computation in BKLPS is represented on the canonical vertex set
  `Fin 10`.  Relabel `G`, transport 2-connectivity and unexceptionality,
  invoke the canonical computation, and finally use invariance of the
  Szeged--Wiener gap to return to the original labeling. -/
  let e := G.overFinIso h_order
  have htwoFin : IsTwoConnected (G.overFin h_order) :=
    (isoIsTwoConnected e).mp h_two_connected
  have hunexceptionalFin : IsUnexceptional (G.overFin h_order) :=
    (isoIsUnexceptional e).mp h_unexceptional
  have hfinite : szegedWienerGap (G.overFin h_order) ≥ (20 : ℤ) :=
    bklpsOrderTenComputation (G.overFin h_order) htwoFin hunexceptionalFin
  rw [isoSzegedWienerGap e] at hfinite
  exact hfinite

end

end BKLPS.External
