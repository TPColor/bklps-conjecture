import Proof.ExternalResults.BlockStructure
import Proof.ExternalResults.BKLPSLemma7GoodsLowerBounds

/-!
The block decomposition of a connected graph with a unique cut vertex.

Delete the cut vertex `v`.  Each connected component of the deletion is
extended by adjoining `v`; paths inside the component prove connectedness,
and uniqueness of the cut vertex proves that the extension has no cut
vertex.  Maximality then identifies these component extensions with the
blocks of the original graph.  It follows that every block contains `v`,
that vertices other than `v` lie in a unique block, and that distinct blocks
meet exactly in `{v}`.

Applied to `G-u`, the domination `N[u] ⊆ N[v]` and 2-connectivity of `G`
force `u` to have a neighbor in the non-cut part of every block; in fact the
arguments used for block extensions supply enough surviving attachment to
route paths after a deletion.  The final counting lemmas partition
`V(G) \ {u,v}` by blocks.  Since every block extension contains both shared
vertices `u` and `v`, summing their orders counts each of them `k` times and
every other vertex once, giving

`∑_i |V(C_i) ∪ {u}| = |V(G)| + 2(k-1)`.

These results provide the structural, disjointness, and cardinality facts
used in Lemmas 4--5 and in both terminal induction branches.
-/

namespace BKLPS.External

open SimpleGraph

noncomputable section

universe u

/-- Adjoin the deleted vertex to one component of its deletion. -/
def cutComponentExtension
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V)
    (D : (deleteVertex G v).ConnectedComponent) : Set V :=
  {x | x = v ∨ ∃ hx : x ≠ v,
    (⟨x, hx⟩ : {z : V // z ≠ v}) ∈ D.supp}

private theorem component_reachable
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V)
    (D : (deleteVertex G v).ConnectedComponent)
    (a b : {z : V // z ≠ v}) (ha : a ∈ D.supp) (hb : b ∈ D.supp) :
    (deleteVertex G v).Reachable a b := by
  rw [← ConnectedComponent.eq]
  exact (ConnectedComponent.mem_supp_iff D a).mp ha |>.trans
    ((ConnectedComponent.mem_supp_iff D b).mp hb).symm

private theorem component_walk_support
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V)
    (D : (deleteVertex G v).ConnectedComponent)
    {a b : {z : V // z ≠ v}}
    (ha : a ∈ D.supp) (p : (deleteVertex G v).Walk a b) :
    ∀ z ∈ p.support, z ∈ D.supp := by
  intro z hz
  rw [ConnectedComponent.mem_supp_iff]
  rw [← (ConnectedComponent.mem_supp_iff D a).mp ha]
  exact (ConnectedComponent.sound (p.takeUntil z hz).reachable).symm

private theorem component_reachable_in_extension
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V)
    (D : (deleteVertex G v).ConnectedComponent)
    (a b : {z : V // z ∈ cutComponentExtension G v D})
    (ha : a.1 ≠ v) (hb : b.1 ≠ v) :
    (G.induce (cutComponentExtension G v D)).Reachable a b := by
  have haD : (⟨a.1, ha⟩ : {z : V // z ≠ v}) ∈ D.supp := by
    rcases a.2 with hav | haD
    · exact False.elim (ha hav)
    · exact haD.choose_spec
  have hbD : (⟨b.1, hb⟩ : {z : V // z ≠ v}) ∈ D.supp := by
    rcases b.2 with hbv | hbD
    · exact False.elim (hb hbv)
    · exact hbD.choose_spec
  obtain ⟨p⟩ := component_reachable G v D ⟨a.1, ha⟩ ⟨b.1, hb⟩ haD hbD
  let inclusion : deleteVertex G v →g G :=
    { toFun := Subtype.val
      map_rel' := fun h => h }
  let pG := p.map inclusion
  have hsupp : ∀ z ∈ pG.support, z ∈ cutComponentExtension G v D := by
    intro z hz
    change z ∈ (p.map inclusion).support at hz
    rw [Walk.support_map] at hz
    obtain ⟨z', hz', hEq⟩ := List.mem_map.mp hz
    have hzEq : z'.1 = z := by simpa [inclusion] using hEq
    subst z
    right
    exact ⟨z'.2, component_walk_support G v D haD p z' hz'⟩
  let q := pG.induce (cutComponentExtension G v D) hsupp
  exact ⟨by simpa [q, pG, inclusion] using q⟩

/-- A component of `G-v`, with `v` put back, induces a connected graph. -/
theorem cutComponentExtension_connected
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (v : V)
    (D : (deleteVertex G v).ConnectedComponent) :
    (G.induce (cutComponentExtension G v D)).Connected := by
  obtain ⟨d, hdD⟩ := D.nonempty_supp
  obtain ⟨p, hpv, hvp, hpD⟩ :=
    exists_neighbor_reaching_after_delete G hconn v d.1 d.2
  have hpMem : (⟨p, hpv⟩ : {z : V // z ≠ v}) ∈ D.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    rw [← (ConnectedComponent.mem_supp_iff D d).mp hdD]
    exact ConnectedComponent.sound hpD
  let vv : {z : V // z ∈ cutComponentExtension G v D} :=
    ⟨v, Or.inl rfl⟩
  let pp : {z : V // z ∈ cutComponentExtension G v D} :=
    ⟨p, Or.inr ⟨hpv, hpMem⟩⟩
  have hvp' : (G.induce (cutComponentExtension G v D)).Adj vv pp := hvp
  letI : Nonempty {z : V // z ∈ cutComponentExtension G v D} := ⟨vv⟩
  refine ⟨?_⟩
  intro a b
  by_cases hav : a.1 = v
  · have havv : a = vv := by apply Subtype.ext; exact hav
    subst a
    by_cases hbv : b.1 = v
    · have hbvv : b = vv := by apply Subtype.ext; exact hbv
      subst b
      exact ⟨Walk.nil⟩
    · exact hvp'.reachable.trans
        (component_reachable_in_extension G v D pp b hpv hbv)
  · by_cases hbv : b.1 = v
    · have hbvv : b = vv := by apply Subtype.ext; exact hbv
      subst b
      exact (hvp'.reachable.trans
        (component_reachable_in_extension G v D pp a hpv hav)).symm
    · exact component_reachable_in_extension G v D a b hav hbv

/-- Deleting the adjoined cut vertex recovers the chosen connected
component, up to the subtype bookkeeping. -/
def deleteCutComponentExtensionIso
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V)
    (D : (deleteVertex G v).ConnectedComponent) :
    let vv : {z : V // z ∈ cutComponentExtension G v D} :=
      ⟨v, Or.inl rfl⟩
    deleteVertex (G.induce (cutComponentExtension G v D)) vv ≃g D.toSimpleGraph := by
  let vv : {z : V // z ∈ cutComponentExtension G v D} :=
    ⟨v, Or.inl rfl⟩
  let toComp : {z : {x : V // x ∈ cutComponentExtension G v D} // z ≠ vv} →
      D.supp := fun z =>
    ⟨⟨z.1.1, by
        intro hzv
        apply z.2
        apply Subtype.ext
        exact hzv⟩, by
      rcases z.1.2 with hzv | hzD
      · exact False.elim (z.2 (by apply Subtype.ext; exact hzv))
      · exact hzD.choose_spec⟩
  let fromComp : D.supp →
      {z : {x : V // x ∈ cutComponentExtension G v D} // z ≠ vv} := fun z =>
    ⟨⟨z.1.1, Or.inr ⟨z.1.2, z.2⟩⟩, by
      intro h
      exact z.1.2 (congrArg (fun x => x.1) h)⟩
  exact
    { toEquiv :=
        { toFun := toComp
          invFun := fromComp
          left_inv := fun z => by ext; rfl
          right_inv := fun z => by ext; rfl }
      map_rel_iff' := by rfl }

private theorem cutComponentExtension_delete_other_connected
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v z : V)
    (D : (deleteVertex G v).ConnectedComponent)
    (hzB : z ∈ cutComponentExtension G v D) (hzv : z ≠ v)
    (hdelete : (deleteVertex G z).Connected) :
    deleteVertex (G.induce (cutComponentExtension G v D)) ⟨z, hzB⟩ |>.Connected := by
  let B := cutComponentExtension G v D
  let zz : B := ⟨z, hzB⟩
  let vv : B := ⟨v, Or.inl rfl⟩
  letI : DecidablePred (fun x : V => x ∈ B) := Classical.decPred _
  let proj : {x : V // x ≠ z} → {x : B // x ≠ zz} := fun x =>
    if hxB : x.1 ∈ B then
      ⟨⟨x.1, hxB⟩, by
        intro h
        exact x.2 (congrArg (fun y => y.1) h)⟩
    else
      ⟨vv, by
        intro h
        exact hzv (Eq.symm (congrArg (fun y => y.1) h))⟩
  have hadjOrEq {a b : {x : V // x ≠ z}}
      (hab : (deleteVertex G z).Adj a b) :
      proj a = proj b ∨ (deleteVertex (G.induce B) zz).Adj (proj a) (proj b) := by
    by_cases haB : a.1 ∈ B
    · by_cases hbB : b.1 ∈ B
      · right
        dsimp [proj]
        rw [dif_pos haB, dif_pos hbB]
        exact hab
      · have hav : a.1 = v := by
          by_contra hav
          have haD : (⟨a.1, hav⟩ : {x : V // x ≠ v}) ∈ D.supp := by
            rcases haB with hav' | haD
            · exact False.elim (hav hav')
            · exact haD.choose_spec
          have hbv : b.1 ≠ v := by
            intro hbv
            apply hbB
            exact Or.inl hbv
          have hab' : (deleteVertex G v).Adj ⟨a.1, hav⟩ ⟨b.1, hbv⟩ := hab
          have hbD := (D.mem_supp_congr_adj hab').mp haD
          exact hbB (Or.inr ⟨hbv, hbD⟩)
        left
        apply Subtype.ext
        apply Subtype.ext
        dsimp [proj]
        rw [dif_pos haB, dif_neg hbB]
        exact hav
    · by_cases hbB : b.1 ∈ B
      · have hbv : b.1 = v := by
          by_contra hbv
          have hbD : (⟨b.1, hbv⟩ : {x : V // x ≠ v}) ∈ D.supp := by
            rcases hbB with hbv' | hbD
            · exact False.elim (hbv hbv')
            · exact hbD.choose_spec
          have hav : a.1 ≠ v := by
            intro hav
            apply haB
            exact Or.inl hav
          have hab' : (deleteVertex G v).Adj ⟨a.1, hav⟩ ⟨b.1, hbv⟩ := hab
          have haD := (D.mem_supp_congr_adj hab').mpr hbD
          exact haB (Or.inr ⟨hav, haD⟩)
        left
        apply Subtype.ext
        apply Subtype.ext
        dsimp [proj]
        rw [dif_neg haB, dif_pos hbB]
        exact hbv.symm
      · left
        apply Subtype.ext
        apply Subtype.ext
        simp [proj, haB, hbB]
  letI : Nonempty {x : B // x ≠ zz} := by
    exact ⟨⟨vv, by
      intro h
      exact hzv (Eq.symm (congrArg (fun y => y.1) h))⟩⟩
  refine ⟨?_⟩
  intro a b
  let a' : {x : V // x ≠ z} := ⟨a.1.1, by
    intro h
    exact a.2 (by apply Subtype.ext; exact h)⟩
  let b' : {x : V // x ≠ z} := ⟨b.1.1, by
    intro h
    exact b.2 (by apply Subtype.ext; exact h)⟩
  obtain ⟨p⟩ := hdelete a' b'
  have hpa : proj a' = a := by
    apply Subtype.ext
    apply Subtype.ext
    simp [proj, a', a.1.2, B]
  have hpb : proj b' = b := by
    apply Subtype.ext
    apply Subtype.ext
    simp [proj, b', b.1.2, B]
  exact ⟨hpa ▸ hpb ▸ Walk.mapAdjOrEq proj (fun h => hadjOrEq h) p⟩

/-- With a unique cut vertex, adjoining that cut vertex to any component of
its deletion gives a connected graph with no cut vertex. -/
theorem cutComponentExtension_connected_noCut
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (hunique : IsUniqueCutVertex G v)
    (D : (deleteVertex G v).ConnectedComponent) :
    letI : Fintype (cutComponentExtension G v D) := Fintype.ofFinite _
    (G.induce (cutComponentExtension G v D)).Connected ∧
      HasNoCutVertex (G.induce (cutComponentExtension G v D)) := by
  let B := cutComponentExtension G v D
  let vv : B := ⟨v, Or.inl rfl⟩
  have hconn : G.Connected := hunique.1.2.1
  have hBconn : (G.induce B).Connected :=
    cutComponentExtension_connected G hconn v D
  refine ⟨hBconn, ?_⟩
  intro z hzcut
  by_cases hzv : z.1 = v
  · have hzvv : z = vv := by apply Subtype.ext; exact hzv
    subst z
    have hcomp : D.toSimpleGraph.Connected := D.connected_toSimpleGraph
    exact hzcut.2.2
      ((deleteCutComponentExtensionIso G v D).connected_iff.mpr hcomp)
  · have hGdelete : (deleteVertex G z.1).Connected := by
      by_contra hnot
      have hzCutG : IsCutVertex G z.1 :=
        ⟨hunique.1.1, hconn, hnot⟩
      exact hzv (hunique.2 z.1 hzCutG)
    exact hzcut.2.2
      (cutComponentExtension_delete_other_connected G v z.1 D z.2 hzv hGdelete)

/-- In a connected graph whose only cut vertex is `v`, the conventional
blocks are exactly the sets obtained by adjoining `v` to a component of
`G-v`. -/
theorem cutComponentExtension_isBlock
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (hunique : IsUniqueCutVertex G v)
    (D : (deleteVertex G v).ConnectedComponent) :
    IsBlock G (cutComponentExtension G v D) := by
  classical
  let B := cutComponentExtension G v D
  have hproperty :
      letI : Fintype B := Fintype.ofFinite B
      (G.induce B).Connected ∧ HasNoCutVertex (G.induce B) :=
    cutComponentExtension_connected_noCut G v hunique D
  let property : Set V → Prop := fun S =>
    letI : Fintype S := Fintype.ofFinite S
    (G.induce S).Connected ∧ HasNoCutVertex (G.induce S)
  refine ⟨hproperty, ?_⟩
  intro S hS hBS y hyS
  letI : Fintype S := Fintype.ofFinite S
  change (G.induce S).Connected ∧ HasNoCutVertex (G.induce S) at hS
  by_contra hyB
  have hyv : y ≠ v := by
    intro hyv
    apply hyB
    exact Or.inl hyv
  obtain ⟨d, hdD⟩ := D.nonempty_supp
  have hdB : d.1 ∈ B := Or.inr ⟨d.2, hdD⟩
  have hdS : d.1 ∈ S := hBS hdB
  have hdy : d.1 ≠ y := by
    intro h
    subst y
    exact hyB hdB
  let vv : S := ⟨v, hBS (Or.inl rfl)⟩
  let dd : S := ⟨d.1, hdS⟩
  let yy : S := ⟨y, hyS⟩
  have hdv : dd ≠ vv := by
    intro h
    exact d.2 (congrArg Subtype.val h)
  have hyv' : yy ≠ vv := by
    intro h
    exact hyv (congrArg Subtype.val h)
  have hcardS : 2 ≤ Fintype.card S := by
    have hsub : ({dd, yy} : Finset S) ⊆ Finset.univ := by simp
    have hcard : ({dd, yy} : Finset S).card = 2 := by
      simp [dd, yy, hdy]
    calc
      2 = ({dd, yy} : Finset S).card := hcard.symm
      _ ≤ (Finset.univ : Finset S).card := Finset.card_le_card hsub
      _ = Fintype.card S := Finset.card_univ
  have hdeleteNotConnected : ¬(deleteVertex (G.induce S) vv).Connected := by
    intro hdelete
    have hreach := hdelete ⟨dd, hdv⟩ ⟨yy, hyv'⟩
    let inclusion : deleteVertex (G.induce S) vv →g deleteVertex G v :=
      { toFun := fun z => ⟨z.1.1, by
          intro hzv
          apply z.2
          apply Subtype.ext
          exact hzv⟩
        map_rel' := fun h => h }
    have hreach' : (deleteVertex G v).Reachable d ⟨y, hyv⟩ := by
      simpa [inclusion, dd, yy] using hreach.map inclusion
    have hyD : (⟨y, hyv⟩ : {z : V // z ≠ v}) ∈ D.supp := by
      rw [ConnectedComponent.mem_supp_iff]
      rw [← (ConnectedComponent.mem_supp_iff D d).mp hdD]
      exact ConnectedComponent.sound hreach'.symm
    exact hyB (Or.inr ⟨hyv, hyD⟩)
  exact False.elim (hS.2 vv ⟨hcardS, hS.1, hdeleteNotConnected⟩)

/-- Every block of a connected graph with unique cut vertex `v` is one of
the component extensions above. -/
theorem isBlock_eq_cutComponentExtension
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (hunique : IsUniqueCutVertex G v)
    (C : Set V) (hC : IsBlock G C) :
    ∃ D : (deleteVertex G v).ConnectedComponent,
      C = cutComponentExtension G v D := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  have hCprop : (G.induce C).Connected ∧ HasNoCutVertex (G.induce C) := hC.1
  by_cases hex : ∃ x : V, x ∈ C ∧ x ≠ v
  · obtain ⟨x, hxC, hxv⟩ := hex
    let xx : {z : V // z ≠ v} := ⟨x, hxv⟩
    let D : (deleteVertex G v).ConnectedComponent :=
      (deleteVertex G v).connectedComponentMk xx
    have hCB : C ⊆ cutComponentExtension G v D := by
      intro y hyC
      by_cases hyv : y = v
      · exact Or.inl hyv
      · right
        refine ⟨hyv, ?_⟩
        rw [ConnectedComponent.mem_supp_iff]
        change (deleteVertex G v).connectedComponentMk ⟨y, hyv⟩ =
          (deleteVertex G v).connectedComponentMk xx
        rw [ConnectedComponent.eq]
        by_cases hvC : v ∈ C
        · let vv : C := ⟨v, hvC⟩
          let xC : C := ⟨x, hxC⟩
          let yC : C := ⟨y, hyC⟩
          have hcardC : 2 ≤ Fintype.card C := by
            have hsub : ({vv, xC} : Finset C) ⊆ Finset.univ := by simp
            have hcard : ({vv, xC} : Finset C).card = 2 := by
              simp [vv, xC, Ne.symm hxv]
            calc
              2 = ({vv, xC} : Finset C).card := hcard.symm
              _ ≤ (Finset.univ : Finset C).card := Finset.card_le_card hsub
              _ = Fintype.card C := Finset.card_univ
          have hdelC := delete_connected_of_connected_noCut
            (G.induce C) hcardC hCprop.1 hCprop.2 vv
          have hxne : xC ≠ vv := by
            intro h
            exact hxv (congrArg Subtype.val h)
          have hyne : yC ≠ vv := by
            intro h
            exact hyv (congrArg Subtype.val h)
          have hr := hdelC ⟨xC, hxne⟩ ⟨yC, hyne⟩
          let inclusion : deleteVertex (G.induce C) vv →g deleteVertex G v :=
            { toFun := fun z => ⟨z.1.1, by
                intro hzv
                apply z.2
                apply Subtype.ext
                exact hzv⟩
              map_rel' := fun h => h }
          simpa [inclusion, xx, xC, yC] using (hr.map inclusion).symm
        · let xC : C := ⟨x, hxC⟩
          let yC : C := ⟨y, hyC⟩
          have hr := hCprop.1 xC yC
          let inclusion : G.induce C →g deleteVertex G v :=
            { toFun := fun z => ⟨z.1, fun hzv => hvC (hzv ▸ z.2)⟩
              map_rel' := fun h => h }
          simpa [inclusion, xx, xC, yC] using (hr.map inclusion).symm
    have hBprop := cutComponentExtension_connected_noCut G v hunique D
    have hBC : cutComponentExtension G v D ⊆ C := hC.2 hBprop hCB
    exact ⟨D, Set.Subset.antisymm hCB hBC⟩
  · obtain ⟨x, hxv⟩ := Fintype.exists_ne_of_one_lt_card hunique.1.1 v
    let xx : {z : V // z ≠ v} := ⟨x, hxv⟩
    let D : (deleteVertex G v).ConnectedComponent :=
      (deleteVertex G v).connectedComponentMk xx
    have hCB : C ⊆ cutComponentExtension G v D := by
      intro y hyC
      have hyv : y = v := by
        by_contra hyv
        exact hex ⟨y, hyC, hyv⟩
      exact Or.inl hyv
    have hBprop := cutComponentExtension_connected_noCut G v hunique D
    have hBC : cutComponentExtension G v D ⊆ C := hC.2 hBprop hCB
    exact ⟨D, Set.Subset.antisymm hCB hBC⟩

/-- Consequently every block contains the unique cut vertex. -/
theorem uniqueCut_mem_isBlock
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (hunique : IsUniqueCutVertex G v)
    (C : Set V) (hC : IsBlock G C) : v ∈ C := by
  obtain ⟨D, rfl⟩ := isBlock_eq_cutComponentExtension G v hunique C hC
  exact Or.inl rfl

/-- An edge out of a non-cut vertex of a block cannot leave that block. -/
theorem adj_mem_isBlock_of_uniqueCut
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (hunique : IsUniqueCutVertex G v)
    (C : Set V) (hC : IsBlock G C)
    {x y : V} (hxC : x ∈ C) (hxv : x ≠ v) (hxy : G.Adj x y) : y ∈ C := by
  obtain ⟨D, rfl⟩ := isBlock_eq_cutComponentExtension G v hunique C hC
  have hxD : (⟨x, hxv⟩ : {z : V // z ≠ v}) ∈ D.supp := by
    rcases hxC with hx | hx
    · exact False.elim (hxv hx)
    · exact hx.choose_spec
  by_cases hyv : y = v
  · exact Or.inl hyv
  · have hxy' : (deleteVertex G v).Adj ⟨x, hxv⟩ ⟨y, hyv⟩ := hxy
    exact Or.inr ⟨hyv, (D.mem_supp_congr_adj hxy').mp hxD⟩

/-- Non-cut vertices in two distinct blocks are nonadjacent. -/
theorem not_adj_of_mem_distinct_blocks
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (hunique : IsUniqueCutVertex G v)
    (C₁ C₂ : Set V) (hC₁ : IsBlock G C₁) (hC₂ : IsBlock G C₂)
    (hne : C₁ ≠ C₂) {x y : V}
    (hx : x ∈ C₁) (hy : y ∈ C₂) (hxv : x ≠ v) (hyv : y ≠ v) :
    ¬G.Adj x y := by
  intro hxy
  have hyC₁ := adj_mem_isBlock_of_uniqueCut G v hunique C₁ hC₁ hx hxv hxy
  have hvC₁ := uniqueCut_mem_isBlock G v hunique C₁ hC₁
  have hvC₂ := uniqueCut_mem_isBlock G v hunique C₂ hC₂
  exact hne (isBlock_eq_of_two_common G C₁ C₂ hC₁ hC₂
    v y hvC₁ hvC₂ hyC₁ hy hyv.symm)

/-- A shortest path after deleting `v` supplies a neighbor of `u` whose
remaining tail avoids both `u` and `v`. -/
theorem exists_neighbor_reaching_after_two_deletions
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v c : V)
    (huv : u ≠ v) (hcv : c ≠ v) (hcu : c ≠ u)
    (hconn : (deleteVertex G v).Connected) :
    ∃ w : V, ∃ hwv : w ≠ v, ∃ hwu : w ≠ u,
      G.Adj u w ∧
      (deleteVertex (deleteVertex G v) ⟨u, huv⟩).Reachable
        ⟨⟨w, hwv⟩, by
          intro h
          exact hwu (congrArg Subtype.val h)⟩
        ⟨⟨c, hcv⟩, by
          intro h
          exact hcu (congrArg Subtype.val h)⟩ := by
  obtain ⟨p, hp⟩ := hconn.exists_isPath ⟨u, huv⟩ ⟨c, hcv⟩
  cases p with
  | nil => exact False.elim (hcu rfl)
  | @cons _ w _ huw q =>
      have hpath := (Walk.cons_isPath_iff huw q).mp hp
      have hwuSub : w ≠ (⟨u, huv⟩ : {z : V // z ≠ v}) := huw.ne.symm
      have hsupport : ∀ z ∈ q.support,
          z ≠ (⟨u, huv⟩ : {z : V // z ≠ v}) := by
        intro z hz hzu
        subst z
        exact hpath.2 hz
      let q' := q.induce
        {z : {x : V // x ≠ v} | z ≠ (⟨u, huv⟩ : {x : V // x ≠ v})}
        hsupport
      have hreach :
          (deleteVertex (deleteVertex G v) ⟨u, huv⟩).Reachable
            ⟨w, hwuSub⟩ ⟨⟨c, hcv⟩, by
              intro h
              exact hcu (congrArg Subtype.val h)⟩ := ⟨q'⟩
      refine ⟨w.1, w.2, ?_, huw, ?_⟩
      · intro h
        exact hwuSub (by apply Subtype.ext; exact h)
      · simpa [q'] using hreach

/-- In the BKLPS situation, `u` has a neighbor other than the cut vertex in
every block of `G-u`, including a possible two-vertex block. -/
theorem exists_u_neighbor_in_block
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G)
    (u v : V) (huv : u ≠ v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u})
    (hC : IsBlock (deleteVertex G u) C) :
    ∃ w : {x : V // x ≠ u},
      w ∈ C ∧ w.1 ≠ v ∧ G.Adj u w.1 := by
  classical
  let H := deleteVertex G u
  let vc : {x : V // x ≠ u} := ⟨v, huv.symm⟩
  obtain ⟨D, hCD⟩ := isBlock_eq_cutComponentExtension H vc hunique C hC
  obtain ⟨c, hcD⟩ := D.nonempty_supp
  have hcuv : c.1.1 ≠ v := by
    intro h
    exact c.2 (by apply Subtype.ext; exact h)
  obtain ⟨w, hwv, hwu, huw, hreach⟩ :=
    exists_neighbor_reaching_after_two_deletions G u v c.1.1 huv hcuv
      c.1.2 (htwo.2.2 v)
  have hreachH :
      (deleteVertex H vc).Reachable
        ⟨⟨w, hwu⟩, by
          intro h
          exact hwv (congrArg Subtype.val h)⟩ c := by
    have hmapped := hreach.map (deleteDeleteIso G v u huv).toHom
    simpa [H, vc] using hmapped
  have hwD :
      (⟨⟨w, hwu⟩, by
        intro h
        exact hwv (congrArg Subtype.val h)⟩ :
          {z : {x : V // x ≠ u} // z ≠ vc}) ∈ D.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact (ConnectedComponent.sound hreachH).trans
      ((ConnectedComponent.mem_supp_iff D c).mp hcD)
  let wH : {x : V // x ≠ u} := ⟨w, hwu⟩
  have hwC : wH ∈ C := by
    rw [hCD]
    exact Or.inr ⟨by
      intro h
      exact hwv (congrArg Subtype.val h), hwD⟩
  exact ⟨wH, hwC, hwv, huw⟩

/-- In the BKLPS situation, `u` has a neighbor other than the cut vertex in
every 2-connected block of `G-u`. -/
theorem exists_u_neighbor_in_twoConnectedBlock
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G)
    (u v : V) (huv : u ≠ v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u})
    (hC : IsBlock (deleteVertex G u) C)
    (hCtwo :
      letI : Fintype C := Fintype.ofFinite C
      IsTwoConnected ((deleteVertex G u).induce C)) :
    ∃ w : {x : V // x ≠ u},
      w ∈ C ∧ w.1 ≠ v ∧ G.Adj u w.1 := by
  classical
  let H := deleteVertex G u
  let vc : {x : V // x ≠ u} := ⟨v, huv.symm⟩
  letI : Fintype C := Fintype.ofFinite C
  change IsTwoConnected ((deleteVertex G u).induce C) at hCtwo
  have hvC : vc ∈ C := uniqueCut_mem_isBlock H vc hunique C hC
  let vcC : C := ⟨vc, hvC⟩
  obtain ⟨cC, hcne⟩ := Fintype.exists_ne_of_one_lt_card (by
    have := hCtwo.1
    omega : 1 < Fintype.card C) vcC
  have hcuv : cC.1.1 ≠ v := by
    intro h
    apply hcne
    apply Subtype.ext
    apply Subtype.ext
    exact h
  obtain ⟨w, hwv, hwu, huw, hreach⟩ :=
    exists_neighbor_reaching_after_two_deletions G u v cC.1.1 huv hcuv
      cC.1.2 (htwo.2.2 v)
  have hreachH :
      (deleteVertex H vc).Reachable
        ⟨⟨w, hwu⟩, by
          intro h
          exact hwv (congrArg Subtype.val h)⟩
        ⟨cC.1, by
          intro h
          exact hcuv (congrArg Subtype.val h)⟩ := by
    have hmapped := hreach.map (deleteDeleteIso G v u huv).toHom
    simpa [H, vc] using hmapped
  obtain ⟨D, hCD⟩ := isBlock_eq_cutComponentExtension H vc hunique C hC
  have hcD :
      (⟨cC.1, by
        intro h
        exact hcuv (congrArg Subtype.val h)⟩ : {z : {x : V // x ≠ u} // z ≠ vc}) ∈
          D.supp := by
    have hcMem : cC.1 ∈ cutComponentExtension H vc D := by
      exact hCD ▸ cC.2
    rcases hcMem with h | h
    · exact False.elim (hcuv (congrArg Subtype.val h))
    · exact h.choose_spec
  have hwD :
      (⟨⟨w, hwu⟩, by
        intro h
        exact hwv (congrArg Subtype.val h)⟩ : {z : {x : V // x ≠ u} // z ≠ vc}) ∈
          D.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact (ConnectedComponent.sound hreachH).trans
      ((ConnectedComponent.mem_supp_iff D _).mp hcD)
  let wH : {x : V // x ≠ u} := ⟨w, hwu⟩
  have hwC : wH ∈ C := by
    rw [hCD]
    exact Or.inr ⟨by
      intro h
      exact hwv (congrArg Subtype.val h), hwD⟩
  exact ⟨wH, hwC, hwv, huw⟩

/-- Distinct non-cut vertices belong to the same block exactly when they
belong to the same component after the cut vertex is deleted. -/
theorem isBlock_noncut_mem_iff_component
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (hunique : IsUniqueCutVertex G v)
    (C : Set V) (hC : IsBlock G C) (x : V) (hxv : x ≠ v) :
    x ∈ C ↔ ∃ D : (deleteVertex G v).ConnectedComponent,
      C = cutComponentExtension G v D ∧
        (⟨x, hxv⟩ : {z : V // z ≠ v}) ∈ D.supp := by
  obtain ⟨D, hCD⟩ := isBlock_eq_cutComponentExtension G v hunique C hC
  subst C
  constructor
  · intro hx
    rcases hx with hx | hx
    · exact False.elim (hxv hx)
    · exact ⟨D, rfl, hx.choose_spec⟩
  · rintro ⟨E, hDE, hxE⟩
    rw [hDE]
    exact Or.inr ⟨hxv, hxE⟩

end

end BKLPS.External
