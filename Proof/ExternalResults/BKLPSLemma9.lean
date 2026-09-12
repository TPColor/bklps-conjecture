import Proof.ExternalResults.BlockStructure
import Mathlib.Tactic.FinCases
import Proof.ExternalResults.UniqueCutBlocks
import Proof.ExternalResults.GraphIsomorphismInvariants
import Proof.ExternalResults.BKLPSLemma9Proof1
import Proof.ExternalResults.BKLPSLemma9Proof3

/-!
BKLPS Lemma 9 is split into its cut-vertex and block conclusions in the two
proof files imported above.  This module is the stable import point.

Main route of the BKLPS argument: apply the terminal hypothesis to a fixed
dominated pair `N[u]⊆N[v]`.  If `G-u` were complete, the noncompleteness of
`G`, 2-connectivity, and a second dominated deletion force the excluded
`K₄²` configuration.  Hence `G-u` is not 2-connected.  Connectivity of
`G-u-v`, followed by the corresponding contradiction for every other
candidate, makes `v` its unique cut vertex.

Now inspect an arbitrary block of `G-u`.  If that block were complete or
one of the two exceptional cone graphs, its dominating vertices can be
lifted to closed-neighborhood containments in `G`.  Rerouting paths inside
the block then makes the associated deletion 2-connected and noncomplete,
contradicting the terminal hypothesis.  Thus every block is unexceptional.
-/

namespace BKLPS.External

open SimpleGraph

noncomputable section

universe u

/-- Bonamy--Knor--Lužar--Pinlou--Škrekovski, Lemma 9.  For every dominated
vertex selected in the terminal induction branch, deletion is not
2-connected, the dominating vertex is its unique cut vertex, and every block
of the deletion avoids all three exceptional graph families. -/
theorem bklpsLemma9
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_two_connected : IsTwoConnected G)
    (h_noncomplete : ¬IsomorphicToKn G)
    (h_not_K42 : ¬Nonempty (G ≃g Knt 4 2))
    (h_deletions : ∀ x y : V, x ≠ y →
      closedNeighborhood G x ⊆ closedNeighborhood G y →
      IsomorphicToKn (deleteVertex G x) ∨ ¬IsTwoConnected (deleteVertex G x))
    (h_exists : ∃ x y : V, x ≠ y ∧
      closedNeighborhood G x ⊆ closedNeighborhood G y)
    (u v : V) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v) :
    ¬IsTwoConnected (deleteVertex G u) ∧
      IsUniqueCutVertex (deleteVertex G u) ⟨v, h_distinct.symm⟩ ∧
      ∀ C : Set {x : V // x ≠ u}, IsBlock (deleteVertex G u) C →
        letI : Fintype C := Fintype.ofFinite C
        IsUnexceptional ((deleteVertex G u).induce C) := by
  have hcut := bklpsLemma9Proof1 G h_two_connected h_noncomplete h_not_K42
    h_deletions h_exists u v h_distinct h_neighborhood
  /- The unique-cut conclusion is then the structural input for the block
  analysis: an exceptional block would create another admissible dominated
  deletion, contradicting the terminal-branch hypothesis. -/
  have hblocks := bklpsLemma9Proof3 G h_two_connected h_noncomplete h_not_K42
    h_deletions h_exists u v h_distinct h_neighborhood hcut.2
  exact ⟨hcut.1, hcut.2, hblocks⟩

end

end BKLPS.External
