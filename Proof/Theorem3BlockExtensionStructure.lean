import Proof.ExternalResults.BKLPSTheorem4BlockRelations
import Proof.Lemma4ExceptionalDeletion
import Proof.ExternalResults.UniqueCutBlocks

/-!
Structural facts about the block extensions in the terminal induction
branch.

For a block `C` of `G-u`, its extension is the induced graph on
`V(C) ∪ {u}`.  Removing the added copy of `u` recovers the induced block;
the file constructs this isomorphism explicitly, in both directions, so it
can be used by the deletion lemmas rather than only informally.

The unique-cut structure shows that `u` has at least two attachment
vertices in every 2-connected block.  Paths within the block connect all
old vertices, while those two attachments keep the graph connected after
any single vertex is removed: after deleting `u` use the block itself;
after deleting an old vertex, enter the surviving block through the other
attachment.  Hence every extension is 2-connected.

Finally, if the induced block is unexceptional and the extension has order
at least six, the exceptional-deletion theorem rules out exceptionality of
the extension.  These facts are precisely what permit Theorem 3 or Lemma 4
to be applied separately to each `G_i` in the block sum.
-/

namespace BKLPS

open SimpleGraph
open External

noncomputable section

universe u

noncomputable instance instFintypeBlockExtensionVertexSetStructure
    {V : Type u} [Fintype V] [DecidableEq V]
    (u : V) (C : Set {x : V // x ≠ u}) :
    Fintype (blockExtensionVertexSet u C) := Fintype.ofFinite _

/-- Removing the added vertex from a block extension recovers the block. -/
def blockExtensionDeleteIso
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (C : Set {x : V // x ≠ u}) :
    deleteVertex (blockExtensionGraph G u C)
        ⟨u, by simp [blockExtensionVertexSet]⟩ ≃g
      (deleteVertex G u).induce C where
  toEquiv :=
    { toFun := fun x =>
        ⟨⟨x.1.1, by
            intro hxu
            apply x.2
            apply Subtype.ext
            exact hxu⟩, by
          rcases x.1.2 with hu | hC
          · exact False.elim (x.2 (by
              apply Subtype.ext
              simpa using hu))
          · exact hC.choose_spec⟩
      invFun := fun x =>
        ⟨⟨x.1.1, Or.inr ⟨x.1.2, x.2⟩⟩, by
          intro h
          exact x.1.2 (congrArg Subtype.val h)⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl }
  map_rel_iff' := by rfl

/-- In the BKLPS unique-cut situation, adjoining `u` to any unexceptional
block produces a 2-connected graph. -/
theorem blockExtension_twoConnected
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u})
    (hC : IsBlock (deleteVertex G u) C)
    (hCtwo :
      letI : Fintype C := Fintype.ofFinite C
      IsTwoConnected ((deleteVertex G u).induce C)) :
    IsTwoConnected (blockExtensionGraph G u C) := by
  letI : Fintype C := Fintype.ofFinite C
  let u₀ : blockExtensionVertexSet u C :=
    ⟨u, by simp [blockExtensionVertexSet]⟩
  have hvC : (⟨v, huv.symm⟩ : {x : V // x ≠ u}) ∈ C :=
    uniqueCut_mem_isBlock (deleteVertex G u) ⟨v, huv.symm⟩ hunique C hC
  let v₀ : blockExtensionVertexSet u C :=
    ⟨v, Or.inr ⟨huv.symm, hvC⟩⟩
  obtain ⟨w, hwC, hwv, huw⟩ :=
    exists_u_neighbor_in_twoConnectedBlock G htwo u v huv hunique C hC hCtwo
  let w₀ : blockExtensionVertexSet u C :=
    ⟨w.1, Or.inr ⟨w.2, hwC⟩⟩
  have huvAdj : G.Adj u v := by
    have hu : u ∈ closedNeighborhood G u := by
      simp [closedNeighborhood, openNeighborhood]
    have hout := hN hu
    have hvu : G.Adj v u := by
      simpa [closedNeighborhood, openNeighborhood, huv, huv.symm] using hout
    exact hvu.symm
  have hv₀u₀ : v₀ ≠ u₀ := by
    intro h
    exact huv (congrArg Subtype.val h).symm
  have hw₀u₀ : w₀ ≠ u₀ := by
    intro h
    exact w.2 (congrArg Subtype.val h)
  have hv₀w₀ : v₀ ≠ w₀ := by
    intro h
    exact hwv (congrArg Subtype.val h).symm
  have hdeleteTwo : IsTwoConnected
      (deleteVertex (blockExtensionGraph G u C) u₀) :=
    (isoIsTwoConnected (blockExtensionDeleteIso G u C)).mpr hCtwo
  exact twoConnected_of_delete_twoConnected_with_two_neighbors
    (blockExtensionGraph G u C) u₀ v₀ w₀ hv₀u₀ hw₀u₀ hv₀w₀
      huvAdj huw hdeleteTwo

/-- An exceptional block extension of order at least five would have an
exceptional 2-connected deletion.  Therefore an unexceptional block has an
unexceptional extension. -/
theorem blockExtension_unexceptional
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (C : Set {x : V // x ≠ u})
    (horder : 5 ≤ Fintype.card (blockExtensionVertexSet u C))
    (hCtwo :
      letI : Fintype C := Fintype.ofFinite C
      IsTwoConnected ((deleteVertex G u).induce C))
    (hCun :
      letI : Fintype C := Fintype.ofFinite C
      IsUnexceptional ((deleteVertex G u).induce C)) :
    IsUnexceptional (blockExtensionGraph G u C) := by
  letI : Fintype C := Fintype.ofFinite C
  let u₀ : blockExtensionVertexSet u C :=
    ⟨u, by simp [blockExtensionVertexSet]⟩
  let eDelete := blockExtensionDeleteIso G u C
  have hdeleteTwo : IsTwoConnected
      (deleteVertex (blockExtensionGraph G u C) u₀) :=
    (isoIsTwoConnected eDelete).mpr hCtwo
  intro hex
  have hdeleteExceptional := exceptional_of_twoConnected_delete_isExceptional
    (blockExtensionGraph G u C) u₀ horder hex hdeleteTwo
  exact hCun ((isoIsExceptional eDelete).mp hdeleteExceptional)

end

end BKLPS
