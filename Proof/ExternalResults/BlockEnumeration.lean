import Proof.ExternalResults.BlockStructure

/-!
Finite enumeration of the manuscript's blocks.  This is bookkeeping needed
to turn the paper's notation `C₁, …, Cₖ` into an actual `Fin k`-indexed
family without assuming an enumeration as extra mathematical data.

A block is represented by its characteristic function on the finite vertex
type, which proves that the subtype of all blocks is finite.  Choosing its
canonical equivalence with `Fin (blockCount G)` gives `enumeratedBlock`.
Injectivity follows from injectivity of that equivalence, while surjectivity
says that every block occurs.  These two facts produce the exact biconditional

`IsBlock G C ↔ ∃ i, C = enumeratedBlock G i`

required by the BKLPS notation, with no duplicates.  If a graph is connected
but not 2-connected, the component structure around a cut vertex supplies at
least two distinct blocks, yielding `2 ≤ blockCount G` for the numerical
block estimates.
-/

namespace BKLPS.External

open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The finite type of blocks of `G`. -/
def BlockType (G : SimpleGraph V) :=
  {C : Set V // IsBlock G C}

noncomputable instance (G : SimpleGraph V) : Fintype (BlockType G) := by
  classical
  let encode : BlockType G → V → Bool := fun C x => decide (x ∈ C.1)
  have hinj : Function.Injective encode := by
    intro A B h
    apply Subtype.ext
    ext x
    have hx := congrFun h x
    exact Iff.of_eq (by
      simpa only [encode, decide_eq_true_eq] using congrArg (fun b => b = true) hx)
  letI : Finite (BlockType G) := Finite.of_injective encode hinj
  exact Fintype.ofFinite _

/-- The number of blocks of a finite graph. -/
def blockCount (G : SimpleGraph V) : ℕ :=
  Fintype.card (BlockType G)

/-- A canonical duplicate-free enumeration of all blocks. -/
def enumeratedBlock (G : SimpleGraph V) (i : Fin (blockCount G)) : Set V :=
  ((Fintype.equivFin (BlockType G)).symm i).1

theorem enumeratedBlock_isBlock (G : SimpleGraph V) (i : Fin (blockCount G)) :
    IsBlock G (enumeratedBlock G i) :=
  ((Fintype.equivFin (BlockType G)).symm i).2

theorem enumeratedBlock_injective (G : SimpleGraph V) :
    Function.Injective (enumeratedBlock G) := by
  intro i j hij
  apply (Fintype.equivFin (BlockType G)).symm.injective
  apply Subtype.ext
  exact hij

theorem isBlock_iff_eq_enumeratedBlock (G : SimpleGraph V) (C : Set V) :
    IsBlock G C ↔ ∃ i : Fin (blockCount G), C = enumeratedBlock G i := by
  constructor
  · intro hC
    let B : BlockType G := ⟨C, hC⟩
    refine ⟨Fintype.equivFin (BlockType G) B, ?_⟩
    change C = ((Fintype.equivFin (BlockType G)).symm
      (Fintype.equivFin (BlockType G) B)).1
    simp [B]
  · rintro ⟨i, rfl⟩
    exact enumeratedBlock_isBlock G i

/-- A cut vertex forces at least two members in the canonical block
enumeration. -/
theorem two_le_blockCount_of_cutVertex (G : SimpleGraph V) (v : V)
    (hcut : IsCutVertex G v) : 2 ≤ blockCount G := by
  obtain ⟨C, D, hC, hD, hCD, _hvC, _hvD⟩ :=
    exists_two_blocks_of_cutVertex G v hcut
  have hne : (⟨C, hC⟩ : BlockType G) ≠ ⟨D, hD⟩ := by
    intro h
    exact hCD (congrArg Subtype.val h)
  letI : Nontrivial (BlockType G) := ⟨⟨_, _, hne⟩⟩
  exact Fintype.one_lt_card

end

end BKLPS.External
