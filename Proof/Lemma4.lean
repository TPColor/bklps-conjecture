import Proof.Definitions
import Proof.ExternalResults.BKLPSLemma7
import Proof.ExternalResults.GraphIsomorphismInvariants
import Mathlib.Tactic.FinCases
import Proof.Theorem3
import Proof.Lemma4ExceptionalDeletion
import Proof.Lemma4OrderFourClassification
import Proof.ExternalResults.UniqueCutBlocks
import Mathlib.Data.Finite.Card

/-! The order-five (`C ≅ C₄`) branch of Lemma 4. -/

namespace BKLPS

open SimpleGraph

noncomputable section

universe u

local instance : DecidableRel (Cn 4).Adj := by
  dsimp [Cn]
  infer_instance

private theorem c4Connected : (Cn 4).Connected := by
  simpa [Cn] using (cycleGraph_connected (n := 3))

private theorem c4Dist_le_two (a b : Fin 4) : (Cn 4).dist a b ≤ 2 := by
  fin_cases a <;> fin_cases b
  all_goals try simp
  all_goals first
    | have h := SimpleGraph.dist_le
        (Walk.cons (show (Cn 4).Adj (0 : Fin 4) 1 by decide)
          (Walk.cons (show (Cn 4).Adj (1 : Fin 4) 2 by decide) Walk.nil));
      simp at h ⊢; omega
    | have h := SimpleGraph.dist_le
        (Walk.cons (show (Cn 4).Adj (0 : Fin 4) 3 by decide)
          (Walk.cons (show (Cn 4).Adj (3 : Fin 4) 2 by decide) Walk.nil));
      simp at h ⊢; omega
    | have h := SimpleGraph.dist_le
        (Walk.cons (show (Cn 4).Adj (1 : Fin 4) 0 by decide)
          (Walk.cons (show (Cn 4).Adj (0 : Fin 4) 3 by decide) Walk.nil));
      simp at h ⊢; omega
    | have h := SimpleGraph.dist_le
        (Walk.cons (show (Cn 4).Adj (1 : Fin 4) 2 by decide)
          (Walk.cons (show (Cn 4).Adj (2 : Fin 4) 3 by decide) Walk.nil));
      simp at h ⊢; omega
    | have h := SimpleGraph.dist_le
        (Walk.cons (show (Cn 4).Adj (2 : Fin 4) 1 by decide)
          (Walk.cons (show (Cn 4).Adj (1 : Fin 4) 0 by decide) Walk.nil));
      simp at h ⊢; omega
    | have h := SimpleGraph.dist_le
        (Walk.cons (show (Cn 4).Adj (2 : Fin 4) 3 by decide)
          (Walk.cons (show (Cn 4).Adj (3 : Fin 4) 0 by decide) Walk.nil));
      simp at h ⊢; omega
    | have h := SimpleGraph.dist_le
        (Walk.cons (show (Cn 4).Adj (3 : Fin 4) 0 by decide)
          (Walk.cons (show (Cn 4).Adj (0 : Fin 4) 1 by decide) Walk.nil));
      simp at h ⊢; omega
    | have h := SimpleGraph.dist_le
        (Walk.cons (show (Cn 4).Adj (3 : Fin 4) 2 by decide)
          (Walk.cons (show (Cn 4).Adj (2 : Fin 4) 1 by decide) Walk.nil));
      simp at h ⊢; omega
    | have h := SimpleGraph.dist_le
        (show (Cn 4).Adj (0 : Fin 4) 1 by decide).toWalk;
      simp at h ⊢; omega
    | have h := SimpleGraph.dist_le
        (show (Cn 4).Adj (0 : Fin 4) 3 by decide).toWalk;
      simp at h ⊢; omega
    | have h := SimpleGraph.dist_le
        (show (Cn 4).Adj (1 : Fin 4) 0 by decide).toWalk;
      simp at h ⊢; omega
    | have h := SimpleGraph.dist_le
        (show (Cn 4).Adj (1 : Fin 4) 2 by decide).toWalk;
      simp at h ⊢; omega
    | have h := SimpleGraph.dist_le
        (show (Cn 4).Adj (2 : Fin 4) 1 by decide).toWalk;
      simp at h ⊢; omega
    | have h := SimpleGraph.dist_le
        (show (Cn 4).Adj (2 : Fin 4) 3 by decide).toWalk;
      simp at h ⊢; omega
    | have h := SimpleGraph.dist_le
        (show (Cn 4).Adj (3 : Fin 4) 0 by decide).toWalk;
      simp at h ⊢; omega
    | have h := SimpleGraph.dist_le
        (show (Cn 4).Adj (3 : Fin 4) 2 by decide).toWalk;
      simp at h ⊢; omega

private theorem c4Dist (a b : Fin 4) :
    (Cn 4).dist a b = if a = b then 0 else if (Cn 4).Adj a b then 1 else 2 := by
  by_cases hab : a = b
  · subst b
    simp
  · by_cases hadj : (Cn 4).Adj a b
    · simp [hab, hadj, dist_eq_one_iff_adj.mpr hadj]
    · simp only [hab, hadj, if_false]
      have hlo := c4Connected.one_lt_dist_of_ne_of_not_adj hab hadj
      have hup := c4Dist_le_two a b
      omega

private theorem c4CloserOfAdj (a b : Fin 4) (hab : (Cn 4).Adj a b) :
    closerCount (Cn 4) a b = 2 := by
  have hn00 : ¬(Cn 4).Adj (0 : Fin 4) 0 := by decide
  have hn02 : ¬(Cn 4).Adj (0 : Fin 4) 2 := by decide
  have hn11 : ¬(Cn 4).Adj (1 : Fin 4) 1 := by decide
  have hn13 : ¬(Cn 4).Adj (1 : Fin 4) 3 := by decide
  have hn20 : ¬(Cn 4).Adj (2 : Fin 4) 0 := by decide
  have hn22 : ¬(Cn 4).Adj (2 : Fin 4) 2 := by decide
  have hn31 : ¬(Cn 4).Adj (3 : Fin 4) 1 := by decide
  have hn33 : ¬(Cn 4).Adj (3 : Fin 4) 3 := by decide
  unfold closerCount closerVertices
  simp_rw [c4Dist]
  fin_cases a <;> fin_cases b
  all_goals first | contradiction | native_decide

/-- The exact computation `η(C₄)=16-8=8` used in the manuscript's
order-five branch of Lemma 4. -/
theorem cycleFourGap : szegedWienerGap (Cn 4) = 8 := by
  have hW : wienerIndex (Cn 4) = 8 := by
    unfold wienerIndex
    let d : Sym2 (Fin 4) → ℕ :=
      Sym2.lift ⟨fun a b =>
        if a = b then 0 else if (Cn 4).Adj a b then 1 else 2, by
          intro a b
          simp only [eq_comm, (Cn 4).adj_comm b a]⟩
    change (∑ p : Sym2 (Fin 4),
      Sym2.lift ⟨(Cn 4).dist, fun a b => dist_comm⟩ p) = 8
    rw [show (∑ p : Sym2 (Fin 4),
        Sym2.lift ⟨(Cn 4).dist, fun a b => dist_comm⟩ p) = ∑ p, d p by
      apply Fintype.sum_congr
      intro p
      induction p using Sym2.inductionOn with
      | _ a b => simp [d, c4Dist]]
    native_decide
  have hSz : szegedIndex (Cn 4) = 16 := by
    unfold szegedIndex
    have hedge : (Cn 4).edgeFinset =
        {s((0 : Fin 4), 1), s((1 : Fin 4), 2),
          s((2 : Fin 4), 3), s((3 : Fin 4), 0)} := by
      ext e
      induction e using Sym2.inductionOn with
      | _ a b =>
          simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
            Finset.mem_insert, Finset.mem_singleton]
          fin_cases a <;> fin_cases b <;> native_decide
    have hcard : (Cn 4).edgeFinset.card = 4 := by
      rw [hedge]
      native_decide
    rw [← Finset.sum_subtype (Cn 4).edgeFinset
      (fun e => SimpleGraph.mem_edgeFinset)]
    have hterm (e : Sym2 (Fin 4)) (he : e ∈ (Cn 4).edgeFinset) :
        szegedContribution (Cn 4) e = 4 := by
      induction e using Sym2.inductionOn with
      | _ a b =>
          have hab : (Cn 4).Adj a b := by
            simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
          simp [szegedContribution, c4CloserOfAdj a b hab,
            c4CloserOfAdj b a hab.symm]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, hcard]
    simp
  unfold szegedWienerGap
  omega

/-- The remaining order-five computation in Lemma 4. -/
theorem lemma4Proof1
    {W : Type u} [Fintype W] [DecidableEq W]
    (G₀ : SimpleGraph W)
    (h_order : Fintype.card W = 5)
    (u₀ v₀ : W)
    (h_u₀v₀ : u₀ ≠ v₀)
    (h_G₀_two_connected : IsTwoConnected G₀)
    (h_G₀_neighborhood :
      closedNeighborhood G₀ u₀ ⊆ closedNeighborhood G₀ v₀)
    (h_delete_two_connected :
      IsTwoConnected (deleteVertex G₀ u₀))
    (h_delete_noncomplete :
      ¬IsomorphicToKn (deleteVertex G₀ u₀))
    (h_delete_cycle :
      Nonempty (deleteVertex G₀ u₀ ≃g Cn 4)) :
    szegedWienerGap G₀ ≥ (2 * Fintype.card W - 4 : ℤ) := by
  have hstep := External.bklpsLemma7 G₀ u₀ v₀
    h_G₀_two_connected h_u₀v₀ h_G₀_neighborhood
    h_delete_two_connected h_delete_noncomplete
  rcases h_delete_cycle with ⟨e⟩
  have hcycleIso := External.isoSzegedWienerGap e
  have hdeleteGap :
      szegedWienerGap (deleteVertex G₀ u₀) = 8 := by
    rw [cycleFourGap] at hcycleIso
    exact hcycleIso.symm
  rw [hdeleteGap] at hstep
  omega

end

end BKLPS


/-!
Main route of Lemma 4.

The graph `G₀` is literally the induced graph on the block vertices together
with `u`; deleting its copy of `u` recovers the block.  The unique-cut
structure supplies two distinct neighbors of `u` in `G₀`, which lifts the
2-connectivity of the block to 2-connectivity of `G₀`.  An unexceptional
block has at least four vertices, so `m=|G₀|≥5`.

For `m≥6`, exceptionality of `G₀` would force exceptionality of its
2-connected deletion, contradicting the block hypothesis; Theorem 3 then
applies.  For `m=5`, the four-vertex 2-connected unexceptional block is
`C₄`.  The domination relation restricts to `G₀`; BKLPS Lemma 7 adds two
to `η(C₄)=8`, yielding `η(G₀)≥10≥2m-4`.
-/

namespace BKLPS

open SimpleGraph

noncomputable section

universe u

/-- The vertex set `V(C) ∪ {u}` occurring in the statement of Lemma 4. -/
def lemma4VertexSet
    {V : Type u} [Fintype V] [DecidableEq V]
    (u : V) (C : Set {x : V // x ≠ u}) : Set V :=
  {u} ∪ {x : V | ∃ hx : x ≠ u, (⟨x, hx⟩ : {x : V // x ≠ u}) ∈ C}

/-- `G₀ = G[V(C) ∪ {u}]`, as defined in the statement of Lemma 4. -/
def lemma4Graph
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (C : Set {x : V // x ≠ u}) :
    SimpleGraph (lemma4VertexSet u C) :=
  G.induce (lemma4VertexSet u C)

noncomputable instance instFintypeLemma4VertexSet
    {V : Type u} [Fintype V] [DecidableEq V]
    (u : V) (C : Set {x : V // x ≠ u}) : Fintype (lemma4VertexSet u C) :=
  Fintype.ofFinite _

instance instDecidableRelLemma4Graph
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (C : Set {x : V // x ≠ u}) : DecidableRel (lemma4Graph G u C).Adj := by
  intro a b
  exact inferInstanceAs (Decidable (G.Adj a.1 b.1))

/-- The vertices of a block extension are literally the block vertices plus
one new vertex `u`.  This is the cardinality identity `m = |C| + 1` used at
the start of the informal proof of Lemma 4. -/
def lemma4VertexSetEquivOption
    {V : Type u} [Fintype V] [DecidableEq V]
    (u : V) (C : Set {x : V // x ≠ u}) :
    lemma4VertexSet u C ≃ Option C where
  toFun x :=
    if hx : x.1 = u then none
    else some ⟨⟨x.1, hx⟩, by
      rcases x.2 with hu | hC
      · exact False.elim (hx (by simpa using hu))
      · rcases hC with ⟨hx', hC⟩
        simpa using hC⟩
  invFun x := match x with
    | none => ⟨u, by simp [lemma4VertexSet]⟩
    | some c => ⟨c.1.1, by
        right
        exact ⟨c.1.2, c.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    by_cases hx : x.1 = u
    · simp [hx]
    · simp [hx]
  right_inv x := by
    cases x with
    | none => simp
    | some c => simp [c.1.2]

theorem card_lemma4VertexSet
    {V : Type u} [Fintype V] [DecidableEq V]
    (u : V) (C : Set {x : V // x ≠ u}) :
    Fintype.card (lemma4VertexSet u C) = Nat.card C + 1 := by
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (lemma4VertexSetEquivOption u C)]
  simp [Nat.add_comm]

/-- Deleting the newly adjoined vertex `u` from the block extension literally
recovers the induced block.  This identifies the graph called `G₀-u` in the
informal proof with `C`. -/
def lemma4DeleteIso
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (C : Set {x : V // x ≠ u}) :
    deleteVertex (lemma4Graph G u C)
        ⟨u, by simp [lemma4VertexSet]⟩ ≃g
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
          · rcases hC with ⟨hxu, hxC⟩
            exact hxC⟩
      invFun := fun x =>
        ⟨⟨x.1.1, by
            right
            exact ⟨x.1.2, x.2⟩⟩, by
          intro h
          exact x.1.2 (congrArg Subtype.val h)⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl }
  map_rel_iff' := by rfl

/-- **Lemma 4.** An unexceptional block extension has gap at least `2m-4`. -/
theorem lemma4
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_two_connected : IsTwoConnected G)
    (u v : V) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete_not_two_connected : ¬IsTwoConnected (deleteVertex G u))
    (h_unique_cut : IsUniqueCutVertex (deleteVertex G u) ⟨v, h_distinct.symm⟩)
    (C : Set {x : V // x ≠ u})
    (h_block : IsBlock (deleteVertex G u) C)
    (h_block_unexceptional :
      letI : Fintype C := Fintype.ofFinite C
      IsUnexceptional ((deleteVertex G u).induce C)) :
    szegedWienerGap (lemma4Graph G u C) ≥
      (2 * Fintype.card (lemma4VertexSet u C) - 4 : ℤ) := by
  /-
  Put `m = |V(C) ∪ {u}|`.  Unexceptionality of the block rules out `m≤4`.
  For `m≥6`, the induced graph is 2-connected and unexceptional, so Theorem 3
  applies.  For `m=5`, the four-vertex block must be `C₄`; BKLPS Lemma 7 and
  `η(C₄)=8` give `η(G₀)≥10≥2m-4`.
  -/
  let H := deleteVertex G u
  let G₀ := lemma4Graph G u C
  let u₀ : lemma4VertexSet u C := ⟨u, by simp [lemma4VertexSet]⟩
  letI : Fintype C := Fintype.ofFinite C
  have hCtwo : IsTwoConnected (H.induce C) :=
    External.isTwoConnected_of_isBlock_unexceptional H C h_block
      h_block_unexceptional
  have hvC : (⟨v, h_distinct.symm⟩ : {x : V // x ≠ u}) ∈ C :=
    External.uniqueCut_mem_isBlock H ⟨v, h_distinct.symm⟩
      h_unique_cut C h_block
  let v₀ : lemma4VertexSet u C :=
    ⟨v, Or.inr ⟨h_distinct.symm, hvC⟩⟩
  obtain ⟨w, hwC, hwv, huw⟩ :=
    External.exists_u_neighbor_in_twoConnectedBlock G h_two_connected
      u v h_distinct h_unique_cut C h_block hCtwo
  let w₀ : lemma4VertexSet u C :=
    ⟨w.1, Or.inr ⟨w.2, hwC⟩⟩
  have huv : G.Adj u v := by
    have hu : u ∈ closedNeighborhood G u := by
      simp [closedNeighborhood, openNeighborhood]
    have hout := h_neighborhood hu
    have hvu : G.Adj v u := by
      simpa [closedNeighborhood, openNeighborhood, h_distinct,
        h_distinct.symm] using hout
    exact hvu.symm
  have hu₀v₀ : G₀.Adj u₀ v₀ := huv
  have hu₀w₀ : G₀.Adj u₀ w₀ := huw
  have hv₀u₀ : v₀ ≠ u₀ := by
    intro h
    exact h_distinct (congrArg Subtype.val h).symm
  have hw₀u₀ : w₀ ≠ u₀ := by
    intro h
    exact w.2 (congrArg Subtype.val h)
  have hv₀w₀ : v₀ ≠ w₀ := by
    intro h
    exact hwv (congrArg Subtype.val h).symm
  let eDelete := lemma4DeleteIso G u C
  have hdeleteTwo : IsTwoConnected (deleteVertex G₀ u₀) :=
    (External.isoIsTwoConnected eDelete).mpr hCtwo
  have hG₀two : IsTwoConnected G₀ :=
    External.twoConnected_of_delete_twoConnected_with_two_neighbors
      G₀ u₀ v₀ w₀ hv₀u₀ hw₀u₀ hv₀w₀ hu₀v₀ hu₀w₀ hdeleteTwo
  have hcardC : 4 ≤ Fintype.card C := by
    exact External.four_le_card_of_connected_noCut_unexceptional
      (H.induce C) h_block.1.1 h_block.1.2 h_block_unexceptional
  have hcardFormula : Fintype.card (lemma4VertexSet u C) = Fintype.card C + 1 := by
    rw [card_lemma4VertexSet, Nat.card_eq_fintype_card]
  have horderFive : 5 ≤ Fintype.card (lemma4VertexSet u C) := by omega
  by_cases horderSix : 6 ≤ Fintype.card (lemma4VertexSet u C)
  · have hG₀unexceptional : IsUnexceptional G₀ := by
      intro hG₀exceptional
      have hdeleteExceptional :=
        exceptional_of_twoConnected_delete_isExceptional
          G₀ u₀ horderFive hG₀exceptional hdeleteTwo
      have hCexceptional : IsExceptional (H.induce C) :=
        (External.isoIsExceptional eDelete).mp hdeleteExceptional
      exact h_block_unexceptional hCexceptional
    exact theorem3 G₀ horderSix hG₀unexceptional hG₀two
  · have horder : Fintype.card (lemma4VertexSet u C) = 5 := by omega
    have hcardCeq : Fintype.card C = 4 := by omega
    have hCcycle : Nonempty (H.induce C ≃g Cn 4) :=
      orderFour_unexceptional_twoConnected_isCycle
        (H.induce C) hcardCeq hCtwo h_block_unexceptional
    have hdeleteCycle : Nonempty (deleteVertex G₀ u₀ ≃g Cn 4) := by
      rcases hCcycle with ⟨eCycle⟩
      exact ⟨eDelete.trans eCycle⟩
    have hdeleteNoncomplete : ¬IsomorphicToKn (deleteVertex G₀ u₀) := by
      intro hcomplete
      have hblockComplete : IsomorphicToKn (H.induce C) :=
        (External.isoIsomorphicToKn eDelete).mp hcomplete
      exact h_block_unexceptional (Or.inl hblockComplete)
    have hG₀neighborhood :
        closedNeighborhood G₀ u₀ ⊆ closedNeighborhood G₀ v₀ := by
      intro z hz
      have hzG : z.1 ∈ closedNeighborhood G u := by
        have hz' : z = u₀ ∨ G₀.Adj u₀ z := by
          simpa [closedNeighborhood, openNeighborhood] using hz
        rcases hz' with hz' | hz'
        · apply Finset.mem_insert.mpr
          exact Or.inl (congrArg Subtype.val hz')
        · apply Finset.mem_insert.mpr
          exact Or.inr (by simpa [openNeighborhood] using hz')
      have hout := h_neighborhood hzG
      have hout' : z.1 = v ∨ G.Adj v z.1 := by
        simpa [closedNeighborhood, openNeighborhood] using hout
      rcases hout' with hout' | hout'
      · apply Finset.mem_insert.mpr
        left
        apply Subtype.ext
        exact hout'
      · apply Finset.mem_insert.mpr
        right
        simpa [openNeighborhood] using hout'
    exact lemma4Proof1 G₀ horder u₀ v₀ hv₀u₀.symm hG₀two
      hG₀neighborhood hdeleteTwo hdeleteNoncomplete hdeleteCycle

end

end BKLPS
