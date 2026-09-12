import Proof.ExternalResults.UniqueCutBlocks
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finite.Card
import Mathlib.Tactic.Ring.RingNF
import Proof.ExternalResults.BKLPSTheorem4BlockRelationsProof1

/-!
The two numerical relations used in the block branch of the proof of BKLPS
Theorem 4.  The enumeration is explicitly injective: the paper's phrase
"let `C₁, ..., Cₖ` be the blocks" lists every block exactly once.

For the first relation, retract the whole graph onto each extension
`G_i=G[V(C_i)∪{u}]`.  Distances inside an extension are unchanged, and every
good edge there remains good in `G`; hence its non-core pair contributions
embed into the global gap.  These internal pair sets are mutually disjoint
and are disjoint from the cross-block pair sets, which yields
`η(G)≥∑_iη(G_i)+cross`.

For every `i<j`, 2-connectivity provides neighbors of `u` on both sides of
the cut vertex.  The two edges incident with `u` are good for the resulting
cross-block pair, so each pair of blocks contributes at least two and
`cross≥2 choose k 2`.

Finally, blocks cover `G-u`, distinct blocks meet only in the unique cut
vertex `v`, and every extension also includes `u`.  Double-counting these
two shared vertices gives `∑_i m_i=n+2(k-1)`.
-/

namespace BKLPS.External

open SimpleGraph
open scoped BigOperators

noncomputable section

universe u

/-- If `C₁, ..., Cₖ` is a duplicate-free enumeration of the blocks of
`G-u`, then the gap of `G` contains the gaps of all block extensions and two
units for every pair of distinct blocks.  Counting the shared vertices `u`
and `v` gives the second displayed identity. -/
theorem bklpsTheorem4BlockRelations
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (u v : V) (h_distinct : u ≠ v)
    (h_two_connected : IsTwoConnected G)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_unique_cut : IsUniqueCutVertex (deleteVertex G u) ⟨v, h_distinct.symm⟩)
    (k : ℕ) (h_k : k ≥ 2)
    (blocks : Fin k → Set {x : V // x ≠ u})
    (h_blocks_injective : Function.Injective blocks)
    (h_blocks : ∀ C : Set {x : V // x ≠ u},
      IsBlock (deleteVertex G u) C ↔ ∃ i : Fin k, C = blocks i) :
    szegedWienerGap G ≥
        (∑ i : Fin k, blockExtensionGap G u (blocks i)) +
          blockCrossContribution G u v k blocks ∧
      blockCrossContribution G u v k blocks ≥ 2 * Nat.choose k 2 ∧
      (∑ i : Fin k, (blockExtensionOrder u (blocks i) : ℤ)) =
        (Fintype.card V : ℤ) + 2 * ((k : ℤ) - 1) := by
  /- First embed the internal pair contributions of every extension into the
  global pair sum.  Next retain, from the still unused cross-block pairs, two
  good-edge units for each unordered pair of blocks.  Independently count
  the vertices of the extensions, remembering that `u` and the unique cut
  vertex `v` occur in every extension. -/
  have h_core := bklpsTheorem4BlockRelationsCore G u v h_distinct
    h_two_connected h_neighborhood h_unique_cut k h_k blocks
    h_blocks_injective h_blocks
  have h_internal :
      szegedWienerGap G ≥
        (∑ i : Fin k, blockExtensionGap G u (blocks i)) +
          blockCrossContribution G u v k blocks := h_core.1
  have h_cross :
      blockCrossContribution G u v k blocks ≥ 2 * Nat.choose k 2 := h_core.2.1
  have h_orders :
      (∑ i : Fin k, (blockExtensionOrder u (blocks i) : ℤ)) =
        (Fintype.card V : ℤ) + 2 * ((k : ℤ) - 1) := h_core.2.2
  exact ⟨h_internal, h_cross, h_orders⟩

end

end BKLPS.External
