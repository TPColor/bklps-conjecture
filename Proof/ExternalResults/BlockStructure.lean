import Proof.ExternalResults.BKLPSLemma7GoodsLowerBounds
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
Elementary structural facts about the manuscript's blocks.  They make
explicit the step used in Lemma 4: a connected block with no cut vertex and
which is not complete has at least four vertices and is 2-connected.

The proof first disposes of orders at most two: connectedness supplies an
edge between every pair of distinct vertices, so the graph is complete.  At
order three, any connected noncomplete graph has a middle vertex on its
unique length-two path; deleting that vertex disconnects the other two.
Thus a connected graph with at least two vertices, no cut vertex, and which
is not complete has order at least four.

For an induced block, maximality and the no-cut condition turn paths in the
ambient graph into paths staying in the block.  Distinct blocks cannot share
two vertices, since their union would still be connected and have no cut
vertex, contradicting maximality.  These intersection and path lemmas are
then used to show that every nontrivial noncomplete block is 2-connected.
They also justify all later claims that cross-block vertex pairs are
disjoint and that different blocks meet only at the unique cut vertex.
-/

namespace BKLPS.External

open SimpleGraph

noncomputable section

universe u

/-- A connected simple graph on at most two vertices is complete. -/
theorem eq_completeGraph_of_connected_card_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hcard : Fintype.card V ≤ 2) : G = completeGraph V := by
  ext a b
  constructor
  · intro hab
    simpa [completeGraph] using hab.ne
  · intro hab
    have hab' : a ≠ b := by simpa [completeGraph] using hab
    obtain ⟨p, hp⟩ := hconn.exists_isPath a b
    have hlt : p.length < Fintype.card V := hp.length_lt
    have hne : p.length ≠ 0 := by
      intro hzero
      exact hab' (Walk.eq_of_length_eq_zero hzero)
    have hone : p.length = 1 := by omega
    exact Walk.adj_of_length_eq_one hone

/-- In particular such a graph belongs to the complete exceptional family. -/
theorem isomorphicToKn_of_connected_card_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hcard : Fintype.card V ≤ 2) : IsomorphicToKn G := by
  rw [eq_completeGraph_of_connected_card_le_two G hconn hcard]
  exact ⟨SimpleGraph.Iso.completeGraph (Fintype.equivFin V)⟩

/-- A graph isomorphic to the complete graph has every possible nonloop
edge. -/
theorem adj_of_isomorphicToKn
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hcomplete : IsomorphicToKn G)
    {a b : V} (hab : a ≠ b) : G.Adj a b := by
  unfold IsomorphicToKn at hcomplete
  obtain ⟨e⟩ := hcomplete
  apply e.map_rel_iff.mp
  simpa [completeGraph] using e.injective.ne hab

/-- Deleting a vertex after inducing a set is the same as inducing the set
with that vertex removed. -/
def deleteInduceIso
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Set V) (x : V) (hx : x ∈ S) :
    deleteVertex (G.induce S) ⟨x, hx⟩ ≃g G.induce (S \ {x}) where
  toEquiv :=
    { toFun := fun y => ⟨y.1.1, y.1.2, by
          intro heq
          exact y.2 (by apply Subtype.ext; exact heq)⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, by
          intro heq
          exact y.2.2 (congrArg Subtype.val heq)⟩
      left_inv := fun y => by ext; rfl
      right_inv := fun y => by ext; rfl }
  map_rel_iff' := by rfl

/-- For a connected graph of order at least two, `HasNoCutVertex` gives
connectedness after every vertex deletion. -/
theorem delete_connected_of_connected_noCut
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hcard : 2 ≤ Fintype.card V)
    (hconn : G.Connected) (hno : HasNoCutVertex G) (x : V) :
    (deleteVertex G x).Connected := by
  by_contra h
  exact hno x ⟨hcard, hconn, h⟩

/-- Deleting two distinct vertices commutes up to the evident relabeling. -/
def deleteDeleteIso
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x u : V) (hux : u ≠ x) :
    deleteVertex (deleteVertex G x) ⟨u, hux⟩ ≃g
      deleteVertex (deleteVertex G u) ⟨x, hux.symm⟩ where
  toEquiv :=
    { toFun := fun y =>
        ⟨⟨y.1.1, by
            intro hyu
            exact y.2 (by apply Subtype.ext; exact hyu)⟩, by
          intro hyx
          exact y.1.2 (congrArg (fun z => z.1) hyx)⟩
      invFun := fun y =>
        ⟨⟨y.1.1, by
            intro hyx
            exact y.2 (by apply Subtype.ext; exact hyx)⟩, by
          intro hyu
          exact y.1.2 (congrArg (fun z => z.1) hyu)⟩
      left_inv := fun y => by ext; rfl
      right_inv := fun y => by ext; rfl }
  map_rel_iff' := by rfl

/-- Two successive vertex deletions are the induced graph on vertices
avoiding both deleted vertices.  This simultaneous form is convenient for
constructing paths by a single retraction. -/
def deleteTwoIso
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (z w : V) (hzw : w ≠ z) :
    deleteVertex (deleteVertex G z) ⟨w, hzw⟩ ≃g
      G.induce {x : V | x ≠ z ∧ x ≠ w} where
  toEquiv :=
    { toFun := fun x => ⟨x.1.1, x.1.2, by
          intro h
          exact x.2 (by apply Subtype.ext; exact h)⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
          intro h
          exact x.2.2 (congrArg Subtype.val h)⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl }
  map_rel_iff' := by rfl

/-- A graph is connected when deleting `u` leaves a connected graph and
`u` has a neighbor in the remaining graph. -/
theorem connected_of_delete_connected_with_neighbor
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u p : V) (hpu : p ≠ u) (hup : G.Adj u p)
    (hdelete : (deleteVertex G u).Connected) : G.Connected := by
  letI : Nonempty V := ⟨u⟩
  let inclusion : deleteVertex G u →g G :=
    { toFun := Subtype.val
      map_rel' := fun h => h }
  have remainingReach (a b : V) (hau : a ≠ u) (hbu : b ≠ u) :
      G.Reachable a b := by
    simpa [inclusion] using (hdelete ⟨a, hau⟩ ⟨b, hbu⟩).map inclusion
  refine ⟨?_⟩
  intro a b
  by_cases hau : a = u
  · subst a
    by_cases hbu : b = u
    · subst b
      exact ⟨Walk.nil⟩
    · exact hup.reachable.trans (remainingReach p b hpu hbu)
  · by_cases hbu : b = u
    · subst b
      exact (hup.reachable.trans (remainingReach p a hpu hau)).symm
    · exact remainingReach a b hau hbu

/-- Adding a vertex with two distinct neighbors to a 2-connected deletion
preserves 2-connectivity.  This is the abstract form of the block-extension
argument used throughout the manuscript. -/
theorem twoConnected_of_delete_twoConnected_with_two_neighbors
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u p q : V)
    (hpu : p ≠ u) (hqu : q ≠ u) (hpq : p ≠ q)
    (hup : G.Adj u p) (huq : G.Adj u q)
    (hdelete : IsTwoConnected (deleteVertex G u)) : IsTwoConnected G := by
  have hthree : 3 ≤ Fintype.card V := by
    have hsub : ({u, p, q} : Finset V) ⊆ Finset.univ := by simp
    have hsetcard : ({u, p, q} : Finset V).card = 3 := by
      simp [hup.ne, huq.ne, hpq]
    calc
      3 = ({u, p, q} : Finset V).card := hsetcard.symm
      _ ≤ (Finset.univ : Finset V).card := Finset.card_le_card hsub
      _ = Fintype.card V := Finset.card_univ
  refine ⟨hthree,
    connected_of_delete_connected_with_neighbor G u p hpu hup hdelete.2.1, ?_⟩
  intro x
  by_cases hxu : x = u
  · subst x
    exact hdelete.2.1
  · let r : V := if x = p then q else p
    have hru : r ≠ u := by
      by_cases hxp : x = p <;> simp [r, hxp, hpu, hqu]
    have hrx : r ≠ x := by
      by_cases hxp : x = p
      · simp [r, hxp, hpq.symm]
      · have hpx : p ≠ x := fun h => hxp h.symm
        simp [r, hxp, hpx]
    have hur : G.Adj u r := by
      by_cases hxp : x = p <;> simp [r, hxp, hup, huq]
    have htwiceRight :
        (deleteVertex (deleteVertex G u) ⟨x, hxu⟩).Connected :=
      hdelete.2.2 ⟨x, hxu⟩
    have htwiceLeft :
        (deleteVertex (deleteVertex G x) ⟨u, Ne.symm hxu⟩).Connected :=
      (deleteDeleteIso G x u (Ne.symm hxu)).connected_iff.mpr htwiceRight
    exact connected_of_delete_connected_with_neighbor (deleteVertex G x)
      ⟨u, Ne.symm hxu⟩ ⟨r, hrx⟩
      (by intro h; exact hru (congrArg Subtype.val h)) hur htwiceLeft

/-- Closed-neighborhood domination survives deletion of a third vertex. -/
theorem closedNeighborhood_subset_delete_of_subset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v x : V) (hux : u ≠ x) (hvx : v ≠ x)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v) :
    closedNeighborhood (deleteVertex G x) ⟨u, hux⟩ ⊆
      closedNeighborhood (deleteVertex G x) ⟨v, hvx⟩ := by
  intro z hz
  have hzG : z.1 ∈ closedNeighborhood G u := by
    simp [closedNeighborhood, openNeighborhood] at hz ⊢
    rcases hz with hz | hz
    · exact Or.inl (congrArg Subtype.val hz)
    · exact Or.inr hz
  have hout := hN hzG
  simp [closedNeighborhood, openNeighborhood] at hout ⊢
  rcases hout with hout | hout
  · left
    apply Subtype.ext
    exact hout
  · exact Or.inr hout

/-- In a 2-connected graph, after deleting a vertex other than a dominated
vertex and its dominator, deleting the dominated vertex as well leaves a
connected graph. -/
theorem delete_dominated_then_other_connected
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G)
    (u v x : V) (huv : u ≠ v) (hux : u ≠ x) (hvx : v ≠ x)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v) :
    (deleteVertex (deleteVertex G u) ⟨x, hux.symm⟩).Connected := by
  let K := deleteVertex G x
  have hKconn : K.Connected := htwo.2.2 x
  have huv' : (⟨u, hux⟩ : {z : V // z ≠ x}) ≠ ⟨v, hvx⟩ := by
    intro h
    exact huv (congrArg Subtype.val h)
  have hdom := closedNeighborhood_subset_delete_of_subset G u v x hux hvx hN
  have hleft := deleteVertex_connected_of_closedNeighborhood_subset K hKconn
    ⟨u, hux⟩ ⟨v, hvx⟩ huv' hdom
  exact (deleteDeleteIso G x u hux).connected_iff.mp hleft

/-- If `z` is dominated by two distinct vertices, deleting `z` preserves
2-connectivity.  When checking a second deletion, use whichever dominator
was not deleted.  This packages the repeated argument in BKLPS Lemma 9. -/
theorem delete_two_dominated_twoConnected
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G)
    (z w₁ w₂ r : V)
    (hzw₁ : z ≠ w₁) (hzw₂ : z ≠ w₂) (hw₁w₂ : w₁ ≠ w₂)
    (hrz : r ≠ z) (hrw₁ : r ≠ w₁) (hrw₂ : r ≠ w₂)
    (hN₁ : closedNeighborhood G z ⊆ closedNeighborhood G w₁)
    (hN₂ : closedNeighborhood G z ⊆ closedNeighborhood G w₂) :
    IsTwoConnected (deleteVertex G z) := by
  have hcard : 3 ≤ Fintype.card {x : V // x ≠ z} := by
    let a : {x : V // x ≠ z} := ⟨w₁, hzw₁.symm⟩
    let b : {x : V // x ≠ z} := ⟨w₂, hzw₂.symm⟩
    let c : {x : V // x ≠ z} := ⟨r, hrz⟩
    have hab : a ≠ b := by
      intro h
      exact hw₁w₂ (congrArg Subtype.val h)
    have hac : a ≠ c := by
      intro h
      exact hrw₁ (congrArg Subtype.val h).symm
    have hbc : b ≠ c := by
      intro h
      exact hrw₂ (congrArg Subtype.val h).symm
    have hsub : ({a, b, c} : Finset {x : V // x ≠ z}) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hc := Finset.card_le_card hsub
    simpa [hab, hac, hbc] using hc
  refine ⟨hcard, htwo.2.2 z, ?_⟩
  intro y
  by_cases hyw₁ : y.1 = w₁
  · exact delete_dominated_then_other_connected G htwo z w₂ y.1
      hzw₂ (Ne.symm y.2) (by
        intro h
        exact hw₁w₂ (hyw₁.symm.trans h.symm)) hN₂
  · exact delete_dominated_then_other_connected G htwo z w₁ y.1
      hzw₁ (Ne.symm y.2) (Ne.symm hyw₁) hN₁

/-- Removing a point from an induced connected/no-cut set of size at least
two leaves a connected induced graph. -/
theorem induce_sdiff_singleton_connected
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Set V)
    (hcard : 2 ≤ Nat.card S)
    (hconn : (G.induce S).Connected)
    (hno : letI : Fintype S := Fintype.ofFinite S
      HasNoCutVertex (G.induce S))
    (x : V) (hx : x ∈ S) :
    (G.induce (S \ {x})).Connected := by
  letI : Fintype S := Fintype.ofFinite S
  have hdelete := delete_connected_of_connected_noCut
    (G.induce S) (by simpa [Nat.card_eq_fintype_card] using hcard) hconn hno ⟨x, hx⟩
  exact (deleteInduceIso G S x hx).connected_iff.mp hdelete

/-- Two connected no-cut induced subgraphs sharing two distinct vertices
have a connected no-cut union. -/
theorem union_connected_noCut_of_two_common
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C D : Set V)
    (hC : letI : Fintype C := Fintype.ofFinite C
      (G.induce C).Connected ∧ HasNoCutVertex (G.induce C))
    (hD : letI : Fintype D := Fintype.ofFinite D
      (G.induce D).Connected ∧ HasNoCutVertex (G.induce D))
    (a b : V) (haC : a ∈ C) (haD : a ∈ D)
    (hbC : b ∈ C) (hbD : b ∈ D) (hab : a ≠ b) :
    letI : Fintype (C ∪ D : Set V) := Fintype.ofFinite (C ∪ D : Set V)
    (G.induce (C ∪ D)).Connected ∧ HasNoCutVertex (G.induce (C ∪ D)) := by
  letI : Fintype C := Fintype.ofFinite C
  letI : Fintype D := Fintype.ofFinite D
  letI : Fintype (C ∪ D : Set V) := Fintype.ofFinite (C ∪ D : Set V)
  haveI : Nontrivial C :=
    ⟨⟨⟨a, haC⟩, ⟨b, hbC⟩, by
      intro h
      exact hab (congrArg Subtype.val h)⟩⟩
  haveI : Nontrivial D :=
    ⟨⟨⟨a, haD⟩, ⟨b, hbD⟩, by
      intro h
      exact hab (congrArg Subtype.val h)⟩⟩
  have hcardC : 2 ≤ Nat.card C := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hcardD : 2 ≤ Nat.card D := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hconnected : (G.induce (C ∪ D)).Connected :=
    G.induce_union_connected hC.1.preconnected hD.1.preconnected
      ⟨a, haC, haD⟩
  refine ⟨hconnected, ?_⟩
  intro z hcut
  let C' : Set V := C \ {z.1}
  let D' : Set V := D \ {z.1}
  have hC' : (G.induce C').Connected := by
    by_cases hzC : z.1 ∈ C
    · exact induce_sdiff_singleton_connected G C hcardC hC.1 hC.2 z.1 hzC
    · have heq : C' = C := by
        ext x
        simp [C', hzC]
      rw [heq]
      exact hC.1
  have hD' : (G.induce D').Connected := by
    by_cases hzD : z.1 ∈ D
    · exact induce_sdiff_singleton_connected G D hcardD hD.1 hD.2 z.1 hzD
    · have heq : D' = D := by
        ext x
        simp [D', hzD]
      rw [heq]
      exact hD.1
  let w : V := if z.1 = a then b else a
  have hwC' : w ∈ C' := by
    by_cases hza : z.1 = a
    · simp [w, C', hza, hbC, hab.symm]
    · have haz : a ≠ z.1 := fun h => hza h.symm
      simp [w, C', hza, haz, haC]
  have hwD' : w ∈ D' := by
    by_cases hza : z.1 = a
    · simp [w, D', hza, hbD, hab.symm]
    · have haz : a ≠ z.1 := fun h => hza h.symm
      simp [w, D', hza, haz, haD]
  have hunionRemoved : (G.induce (C' ∪ D')).Connected :=
    G.induce_union_connected hC'.preconnected hD'.preconnected
      ⟨w, hwC', hwD'⟩
  have hsets : C' ∪ D' = (C ∪ D) \ {z.1} := by
    ext x
    simp only [C', D', Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
    aesop
  have hdelete : (deleteVertex (G.induce (C ∪ D)) z).Connected :=
    (deleteInduceIso G (C ∪ D) z.1 z.2).connected_iff.mpr (by
      rw [← hsets]
      exact hunionRemoved)
  exact hcut.2.2 hdelete

/-- Distinct blocks cannot share two vertices. -/
theorem isBlock_eq_of_two_common
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C D : Set V)
    (hC : IsBlock G C) (hD : IsBlock G D)
    (a b : V) (haC : a ∈ C) (haD : a ∈ D)
    (hbC : b ∈ C) (hbD : b ∈ D) (hab : a ≠ b) : C = D := by
  have hunion := union_connected_noCut_of_two_common G C D hC.1 hD.1
    a b haC haD hbC hbD hab
  have hCD : C ∪ D ⊆ C := hC.2 hunion Set.subset_union_left
  have hDC : C ∪ D ⊆ D := hD.2 hunion Set.subset_union_right
  exact Set.Subset.antisymm
    (fun x hx => hDC (Or.inl hx)) (fun x hx => hCD (Or.inr hx))

/-- A connected graph of order at most two has no cut vertex. -/
theorem hasNoCutVertex_of_connected_card_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hcard : Fintype.card V ≤ 2) : HasNoCutVertex G := by
  intro x hcut
  have hlow : 2 ≤ Fintype.card V := hcut.1
  have htwo : Fintype.card V = 2 := by omega
  have hcardDelete : Fintype.card {y : V // y ≠ x} = 1 := by
    simpa [htwo] using Fintype.card_subtype_compl (fun y : V => y = x)
  letI : Nonempty {y : V // y ≠ x} :=
    Fintype.card_pos_iff.mp (by omega)
  letI : Subsingleton {y : V // y ≠ x} :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  apply hcut.2.2
  exact ⟨SimpleGraph.Preconnected.of_subsingleton⟩

/-- Every edge is contained in a block. -/
theorem exists_isBlock_of_adj
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {a b : V} (hab : G.Adj a b) :
    ∃ C : Set V, IsBlock G C ∧ a ∈ C ∧ b ∈ C := by
  let S : Set V := {a, b}
  letI : Fintype S := Fintype.ofFinite S
  have hconn : (G.induce S).Connected := by
    simpa [S] using G.induce_pair_connected_of_adj hab
  have hcard : Fintype.card S ≤ 2 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simp [S, Set.ncard_pair hab.ne]
  have hproperty :
      letI : Fintype S := Fintype.ofFinite S
      (G.induce S).Connected ∧ HasNoCutVertex (G.induce S) :=
    ⟨hconn, hasNoCutVertex_of_connected_card_le_two (G.induce S) hconn hcard⟩
  let property : Set V → Prop := fun T =>
    letI : Fintype T := Fintype.ofFinite T
    (G.induce T).Connected ∧ HasNoCutVertex (G.induce T)
  obtain ⟨C, hSC, hmax⟩ := Finite.exists_le_maximal (p := property) hproperty
  refine ⟨C, hmax, hSC (by simp [S]), hSC (by simp [S])⟩

/-- Along a shortest path from `v` to `a`, the first neighbor of `v` still
reaches `a` after `v` is deleted. -/
theorem exists_neighbor_reaching_after_delete
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (v a : V) (hav : a ≠ v) :
    ∃ x : V, ∃ hxv : x ≠ v, G.Adj v x ∧
      (deleteVertex G v).Reachable ⟨x, hxv⟩ ⟨a, hav⟩ := by
  obtain ⟨p, hp⟩ := hconn.exists_isPath v a
  cases p with
  | nil => exact False.elim (hav rfl)
  | @cons _ x _ hvx q =>
      have hpath := (Walk.cons_isPath_iff hvx q).mp hp
      have hxv : x ≠ v := hvx.ne.symm
      have hsupport : ∀ z ∈ q.support, z ∈ {z : V | z ≠ v} := by
        intro z hz hzv
        subst z
        exact hpath.2 hz
      refine ⟨x, hxv, hvx, ?_⟩
      let q' := q.induce {z : V | z ≠ v} hsupport
      have hreach : (deleteVertex G v).Reachable
          ⟨x, hsupport x q.start_mem_support⟩
          ⟨a, hsupport a q.end_mem_support⟩ := ⟨q'⟩
      simpa only [deleteVertex, Subtype.coe_eta] using hreach

/-- Every vertex of a 2-connected graph has two distinct neighbors. -/
theorem exists_two_neighbors_of_twoConnected
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G) (u : V) :
    ∃ a b : V, a ≠ b ∧ G.Adj u a ∧ G.Adj u b := by
  by_contra h
  push_neg at h
  have hcard := htwo.1
  obtain ⟨a, hau⟩ := Fintype.exists_ne_of_one_lt_card (by omega) u
  obtain ⟨p⟩ := htwo.2.1 u a
  cases p with
  | nil => exact hau rfl
  | @cons _ x _ hux q =>
      have hxu : x ≠ u := hux.ne.symm
      have hcardErase : ((Finset.univ.erase u).erase x).card =
          Fintype.card V - 2 := by
        simp only [Finset.card_erase_of_mem, Finset.mem_univ, Finset.mem_erase,
          ne_eq, hxu, not_false_eq_true, and_true, Finset.card_univ]
        omega
      have hnonempty : ((Finset.univ.erase u).erase x).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        have hz : ((Finset.univ.erase u).erase x).card = 0 := by simp [hempty]
        omega
      obtain ⟨y, hy⟩ := hnonempty
      have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
      have hyu : y ≠ u :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
      have hdeleteReach := htwo.2.2 x ⟨u, hxu.symm⟩ ⟨y, hyx⟩
      obtain ⟨r⟩ := hdeleteReach
      cases r with
      | nil => exact hyu rfl
      | @cons _ z _ huz tail =>
          have huzG : G.Adj u z.1 := huz
          exact h x z.1 (fun hxz => z.2 hxz.symm) hux huzG

/-- A clique together with one extra vertex adjacent to a clique vertex is
connected. -/
theorem connected_of_clique_away_with_neighbor
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u p : V) (hpu : p ≠ u) (hup : G.Adj u p)
    (hclique : ∀ a b : V, a ≠ u → b ≠ u → a ≠ b → G.Adj a b) :
    G.Connected := by
  letI : Nonempty V := ⟨u⟩
  refine ⟨?_⟩
  intro a b
  by_cases hab : a = b
  · subst b
    exact ⟨Walk.nil⟩
  by_cases hau : a = u
  · subst a
    by_cases hbp : b = p
    · subst b
      exact hup.reachable
    · exact hup.reachable.trans
        (hclique p b hpu (fun h => hab h.symm) (fun h => hbp h.symm)).reachable
  by_cases hbu : b = u
  · subst b
    by_cases hap : a = p
    · subst a
      exact hup.symm.reachable
    · exact (hup.reachable.trans
        (hclique p a hpu hau (fun h => hap h.symm)).reachable).symm
  · exact (hclique a b hau hbu hab).reachable

/-- A clique plus one vertex with two distinct clique neighbors is
2-connected. -/
theorem twoConnected_of_clique_away_with_two_neighbors
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u p q : V)
    (hpu : p ≠ u) (hqu : q ≠ u) (hpq : p ≠ q)
    (hup : G.Adj u p) (huq : G.Adj u q)
    (hclique : ∀ a b : V, a ≠ u → b ≠ u → a ≠ b → G.Adj a b) :
    IsTwoConnected G := by
  have hthree : 3 ≤ Fintype.card V := by
    have hsub : ({u, p, q} : Finset V) ⊆ Finset.univ := by simp
    have hsetcard : ({u, p, q} : Finset V).card = 3 := by
      simp [hup.ne, huq.ne, hpq]
    calc
      3 = ({u, p, q} : Finset V).card := hsetcard.symm
      _ ≤ (Finset.univ : Finset V).card := Finset.card_le_card hsub
      _ = Fintype.card V := Finset.card_univ
  refine ⟨hthree,
    connected_of_clique_away_with_neighbor G u p hpu hup hclique, ?_⟩
  intro x
  by_cases hxu : x = u
  · have hdel : (deleteVertex G u).Connected := by
      letI : Nonempty {z : V // z ≠ u} := ⟨⟨p, hpu⟩⟩
      refine ⟨?_⟩
      intro a b
      by_cases hab : a = b
      · subst b
        exact ⟨Walk.nil⟩
      · have hadj : (deleteVertex G u).Adj a b := hclique a.1 b.1 a.2 b.2
          (fun h => hab (Subtype.ext h))
        exact hadj.reachable
    subst x
    exact hdel
  · let r : V := if x = p then q else p
    have hru : r ≠ u := by
      by_cases hxp : x = p <;> simp [r, hxp, hpu, hqu]
    have hrx : r ≠ x := by
      by_cases hxp : x = p
      · simp [r, hxp, hpq.symm]
      · have hpx : p ≠ x := fun h => hxp h.symm
        simp [r, hxp, hpx]
    have hur : G.Adj u r := by
      by_cases hxp : x = p <;> simp [r, hxp, hup, huq]
    apply connected_of_clique_away_with_neighbor (deleteVertex G x)
      ⟨u, fun h => hxu h.symm⟩ ⟨r, hrx⟩
    · intro h
      exact hru (congrArg Subtype.val h)
    · exact hur
    · intro a b hau hbu hab
      exact hclique a.1 b.1
        (fun h => hau (Subtype.ext h)) (fun h => hbu (Subtype.ext h))
        (fun h => hab (Subtype.ext h))

/-- A cut vertex of a connected graph lies in at least two distinct blocks. -/
theorem exists_two_blocks_of_cutVertex
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (hcut : IsCutVertex G v) :
    ∃ C D : Set V, IsBlock G C ∧ IsBlock G D ∧ C ≠ D ∧
      v ∈ C ∧ v ∈ D := by
  have hcardDelete : 0 < Fintype.card {x : V // x ≠ v} := by
    have hcard : Fintype.card {x : V // x ≠ v} = Fintype.card V - 1 := by
      simpa using Fintype.card_subtype_compl (fun x : V => x = v)
    have hlower := hcut.1
    omega
  letI : Nonempty {x : V // x ≠ v} := Fintype.card_pos_iff.mp hcardDelete
  have hnotpre : ¬(deleteVertex G v).Preconnected := by
    intro hpre
    exact hcut.2.2 ⟨hpre⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hnotpre
  obtain ⟨a, hnotall⟩ := hnotpre
  obtain ⟨b, hab⟩ := hnotall
  obtain ⟨x, hxv, hvx, hxa⟩ :=
    exists_neighbor_reaching_after_delete G hcut.2.1 v a.1 a.2
  obtain ⟨y, hyv, hvy, hyb⟩ :=
    exists_neighbor_reaching_after_delete G hcut.2.1 v b.1 b.2
  obtain ⟨C, hC, hvC, hxC⟩ := exists_isBlock_of_adj G hvx
  obtain ⟨D, hD, hvD, hyD⟩ := exists_isBlock_of_adj G hvy
  refine ⟨C, D, hC, hD, ?_, hvC, hvD⟩
  intro hCD
  subst D
  letI : Fintype C := Fintype.ofFinite C
  haveI : Nontrivial C :=
    ⟨⟨⟨v, hvC⟩, ⟨x, hxC⟩, by
      intro h
      exact hxv (congrArg Subtype.val h).symm⟩⟩
  have hcardC : 2 ≤ Nat.card C := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hremoved := induce_sdiff_singleton_connected G C hcardC
    hC.1.1 hC.1.2 v hvC
  have hxySmall : (G.induce (C \ {v})).Reachable
      ⟨x, hxC, by simpa using hxv⟩ ⟨y, hyD, by simpa using hyv⟩ :=
    hremoved _ _
  have hsubset : C \ {v} ⊆ {z : V | z ≠ v} := by
    intro z hz
    exact hz.2
  obtain ⟨q⟩ := hxySmall
  have q' := q.map (G.induceHomOfLE hsubset).toHom
  have hxy : (deleteVertex G v).Reachable ⟨x, hxv⟩ ⟨y, hyv⟩ := by
    refine ⟨?_⟩
    simpa only [deleteVertex, SimpleGraph.induceHomOfLE_apply, Set.inclusion]
      using q'
  exact hab (hxa.symm.trans (hxy.trans hyb))

/-- A connected graph without a cut vertex which is not exceptional has at
least four vertices. -/
theorem four_le_card_of_connected_noCut_unexceptional
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (hno : HasNoCutVertex G)
    (hunexceptional : IsUnexceptional G) : 4 ≤ Fintype.card V := by
  by_contra hfour
  have hcard : Fintype.card V ≤ 3 := by omega
  by_cases hsmall : Fintype.card V ≤ 2
  · exact hunexceptional (Or.inl
      (isomorphicToKn_of_connected_card_le_two G hconn hsmall))
  · have hthree : Fintype.card V = 3 := by omega
    have hnotcomplete : ¬IsomorphicToKn G := fun h => hunexceptional (Or.inl h)
    obtain ⟨a, b, hab, hnab⟩ :=
      exists_nonedge_of_not_isomorphicToKn G hnotcomplete
    obtain ⟨p, hp⟩ := hconn.exists_isPath a b
    have hlt : p.length < 3 := by simpa [hthree] using hp.length_lt
    have hnotzero : p.length ≠ 0 := by
      intro hzero
      exact hab (Walk.eq_of_length_eq_zero hzero)
    have hnotone : p.length ≠ 1 := by
      intro hone
      exact hnab (Walk.adj_of_length_eq_one hone)
    have htwo : p.length = 2 := by omega
    cases p with
    | nil => simp at htwo
    | @cons _ c _ hac q =>
        have hqone : q.length = 1 := by simpa [Walk.length_cons] using htwo
        have hcb : G.Adj c b := Walk.adj_of_length_eq_one hqone
        have hacne : a ≠ c := hac.ne
        have hbcne : b ≠ c := hcb.ne.symm
        apply hno c
        refine ⟨by omega, hconn, ?_⟩
        intro hdelete
        have hcardDelete : Fintype.card {x : V // x ≠ c} = 2 := by
          simpa [hthree] using Fintype.card_subtype_compl (fun x : V => x = c)
        have hcomplete := eq_completeGraph_of_connected_card_le_two
          (deleteVertex G c) hdelete (by omega)
        have hadjDelete : (deleteVertex G c).Adj ⟨a, hacne⟩ ⟨b, hbcne⟩ := by
          rw [hcomplete]
          simpa [completeGraph] using hab
        exact hnab hadjDelete

/-- The predicate defining a block holds at the block itself. -/
theorem isBlock_connected_noCut
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Set V) (hblock : IsBlock G C) :
    letI : Fintype C := Fintype.ofFinite C
    (G.induce C).Connected ∧ HasNoCutVertex (G.induce C) := by
  exact hblock.1

/-- Every unexceptional block in the informal proof is 2-connected. -/
theorem isTwoConnected_of_isBlock_unexceptional
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : Set V) (hblock : IsBlock G C)
    (hunexceptional :
      letI : Fintype C := Fintype.ofFinite C
      IsUnexceptional (G.induce C)) :
    letI : Fintype C := Fintype.ofFinite C
    IsTwoConnected (G.induce C) := by
  letI : Fintype C := Fintype.ofFinite C
  have hstructure := isBlock_connected_noCut G C hblock
  have hcard := four_le_card_of_connected_noCut_unexceptional
    (G.induce C) hstructure.1 hstructure.2 hunexceptional
  refine ⟨by omega, hstructure.1, ?_⟩
  intro c
  by_contra hdisconnect
  exact hstructure.2 c ⟨by omega, hstructure.1, hdisconnect⟩

end

end BKLPS.External
