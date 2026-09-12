import Proof.ExternalResults.BlockStructure
import Mathlib.Tactic.FinCases

/-! The cut-vertex conclusion from the proof of BKLPS Lemma 9. -/

namespace BKLPS.External

open SimpleGraph

noncomputable section

universe u

/-- The unique-cut conclusion once the complete-deletion alternative has
been excluded.  This is the dominated-retraction argument implicit in the
second paragraph of the BKLPS proof. -/
private theorem bklpsLemma9_of_delete_noncomplete
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h_two_connected : IsTwoConnected G)
    (u v : V) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_deletions : ∀ x y : V, x ≠ y →
      closedNeighborhood G x ⊆ closedNeighborhood G y →
      IsomorphicToKn (deleteVertex G x) ∨ ¬IsTwoConnected (deleteVertex G x))
    (h_delete_noncomplete : ¬IsomorphicToKn (deleteVertex G u)) :
    ¬IsTwoConnected (deleteVertex G u) ∧
      IsUniqueCutVertex (deleteVertex G u) ⟨v, h_distinct.symm⟩ := by
  let W : Type u := {z : V // z ≠ u}
  let H : SimpleGraph W := deleteVertex G u
  let vc : W := ⟨v, h_distinct.symm⟩
  change ¬IsTwoConnected H ∧ IsUniqueCutVertex H vc
  have hHconnected : H.Connected := h_two_connected.2.2 u
  have hHnotTwo : ¬IsTwoConnected H := by
    rcases h_deletions u v h_distinct h_neighborhood with hcomplete | hnot
    · exact False.elim (h_delete_noncomplete hcomplete)
    · exact hnot
  have hcardH : Fintype.card W = Fintype.card V - 1 := by
    simpa [W] using Fintype.card_subtype_compl (fun x : V => x = u)
  have hcardHtwo : 2 ≤ Fintype.card W := by
    have := h_two_connected.1
    omega
  have hcardHthree : 3 ≤ Fintype.card W := by
    by_contra hsmall
    have hcomplete := isomorphicToKn_of_connected_card_le_two H hHconnected (by omega)
    exact h_delete_noncomplete hcomplete
  have hdelete_other (x : W) (hxv : x ≠ vc) :
      (deleteVertex H x).Connected := by
    have hxvBase : x.1 ≠ v := by
      intro h
      apply hxv
      apply Subtype.ext
      exact h
    exact delete_dominated_then_other_connected G h_two_connected u v x.1
      h_distinct x.2.symm hxvBase.symm h_neighborhood
  have hvcCut : IsCutVertex H vc := by
    refine ⟨hcardHtwo, hHconnected, ?_⟩
    intro hvcConnected
    apply hHnotTwo
    refine ⟨hcardHthree, hHconnected, ?_⟩
    intro x
    by_cases hx : x = vc
    · subst x
      exact hvcConnected
    · exact hdelete_other x hx
  refine ⟨hHnotTwo, hvcCut, ?_⟩
  intro x hxcut
  by_contra hx
  exact hxcut.2.2 (hdelete_other x hx)


/-- The first conclusion of BKLPS Lemma 9: a dominated-vertex deletion is not
2-connected, and the dominating vertex is its unique cut vertex. -/
theorem bklpsLemma9Proof1
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
      IsUniqueCutVertex (deleteVertex G u) ⟨v, h_distinct.symm⟩ := by
  by_cases hdeleteComplete : IsomorphicToKn (deleteVertex G u)
  · have hclique : ∀ a b : V, a ≠ u → b ≠ u → a ≠ b → G.Adj a b := by
      intro a b hau hbu hab
      exact adj_of_isomorphicToKn (deleteVertex G u) hdeleteComplete
        (show (⟨a, hau⟩ : {x : V // x ≠ u}) ≠ ⟨b, hbu⟩ by
          intro h
          exact hab (congrArg Subtype.val h))
    have hGnoncomplete : ¬IsomorphicToKn G := h_noncomplete
    obtain ⟨a, b, hab, hnab⟩ :=
      exists_nonedge_of_not_isomorphicToKn G hGnoncomplete
    have hnonneighbor : ∃ w : V, w ≠ u ∧ ¬G.Adj u w := by
      by_cases hau : a = u
      · subst a
        exact ⟨b, hab.symm, hnab⟩
      · by_cases hbu : b = u
        · subst b
          exact ⟨a, hau, fun h => hnab h.symm⟩
        · exact False.elim (hnab (hclique a b hau hbu hab))
    obtain ⟨w, hwu, hnuw⟩ := hnonneighbor
    obtain ⟨p, q, hpq, hup, huq⟩ :=
      exists_two_neighbors_of_twoConnected G h_two_connected u
    have hpu : p ≠ u := hup.ne.symm
    have hqu : q ≠ u := huq.ne.symm
    have hpw : p ≠ w := by
      intro h
      subst p
      exact hnuw hup
    have hqw : q ≠ w := by
      intro h
      subst q
      exact hnuw huq
    have uniqueNonneighbor : ∀ z : V, z ≠ u → ¬G.Adj u z → z = w := by
      intro z hzu hnuz
      by_contra hzw
      have hsub : closedNeighborhood G w ⊆ closedNeighborhood G z := by
        intro t ht
        have htu : t ≠ u := by
          intro htu
          subst t
          have ht' : u = w ∨ G.Adj w u := by
            simpa [closedNeighborhood, openNeighborhood] using ht
          rcases ht' with huw | hwuAdj
          · exact hwu huw.symm
          · exact hnuw hwuAdj.symm
        by_cases htz : t = z
        · subst t
          simp [closedNeighborhood]
        · have hzt := hclique z t hzu htu (Ne.symm htz)
          simp [closedNeighborhood, openNeighborhood, htz, hzt]
      have hdeleteTwo : IsTwoConnected (deleteVertex G w) := by
        apply twoConnected_of_clique_away_with_two_neighbors
          (deleteVertex G w) ⟨u, hwu.symm⟩ ⟨p, hpw⟩ ⟨q, hqw⟩
        · intro h
          exact hpu (congrArg Subtype.val h)
        · intro h
          exact hqu (congrArg Subtype.val h)
        · intro h
          exact hpq (congrArg Subtype.val h)
        · exact hup
        · exact huq
        · intro r s hru hsu hrs
          exact hclique r.1 s.1
            (fun h => hru (Subtype.ext h)) (fun h => hsu (Subtype.ext h))
            (fun h => hrs (Subtype.ext h))
      have hdeleteNoncomplete : ¬IsomorphicToKn (deleteVertex G w) := by
        intro hcomplete
        have hadj := adj_of_isomorphicToKn (deleteVertex G w) hcomplete
          (show (⟨u, hwu.symm⟩ : {x : V // x ≠ w}) ≠ ⟨z, hzw⟩ by
            intro h
            exact hzu (Eq.symm (congrArg Subtype.val h)))
        exact hnuz hadj
      rcases h_deletions w z (Ne.symm hzw) hsub with hcomplete | hnotTwo
      · exact hdeleteNoncomplete hcomplete
      · exact hnotTwo hdeleteTwo
    have onlyTwoNeighbors : ∀ r : V, r ≠ u → G.Adj u r → r = p ∨ r = q := by
      intro r hru hur
      by_contra hr
      push_neg at hr
      have hrp : r ≠ p := hr.1
      have hrq : r ≠ q := hr.2
      have hqDominates : ∀ t : V, t ≠ q → G.Adj q t := by
        intro t htq
        by_cases htu : t = u
        · subst t
          exact huq.symm
        · exact hclique q t hqu htu (Ne.symm htq)
      have hsub : closedNeighborhood G p ⊆ closedNeighborhood G q := by
        intro t _ht
        by_cases htq : t = q
        · subst t
          simp [closedNeighborhood]
        · have hqt := hqDominates t htq
          simp [closedNeighborhood, openNeighborhood, htq, hqt]
      have hdeleteTwo : IsTwoConnected (deleteVertex G p) := by
        apply twoConnected_of_clique_away_with_two_neighbors
          (deleteVertex G p) ⟨u, hpu.symm⟩ ⟨q, hpq.symm⟩ ⟨r, hrp⟩
        · intro h
          exact hqu (congrArg Subtype.val h)
        · intro h
          exact hru (congrArg Subtype.val h)
        · intro h
          exact hrq.symm (congrArg Subtype.val h)
        · exact huq
        · exact hur
        · intro c d hcu hdu hcd
          exact hclique c.1 d.1
            (fun h => hcu (Subtype.ext h)) (fun h => hdu (Subtype.ext h))
            (fun h => hcd (Subtype.ext h))
      have hdeleteNoncomplete : ¬IsomorphicToKn (deleteVertex G p) := by
        intro hcomplete
        have hadj := adj_of_isomorphicToKn (deleteVertex G p) hcomplete
          (show (⟨u, hpu.symm⟩ : {x : V // x ≠ p}) ≠ ⟨w, hpw.symm⟩ by
            intro h
            exact hwu (Eq.symm (congrArg Subtype.val h)))
        exact hnuw hadj
      rcases h_deletions p q hpq hsub with hcomplete | hnotTwo
      · exact hdeleteNoncomplete hcomplete
      · exact hnotTwo hdeleteTwo
    let f : Fin 4 → V := fun i =>
      if i = 0 then u else if i = 1 then p else if i = 2 then q else w
    have hfInjective : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [f, hpu, hpu.symm, hqu, hqu.symm, hwu, hwu.symm,
          hpq, hpq.symm, hpw, hpw.symm, hqw, hqw.symm] at hij ⊢
    have hfSurjective : Function.Surjective f := by
      intro x
      by_cases hxu : x = u
      · exact ⟨0, by simp [f, hxu]⟩
      by_cases hxp : x = p
      · exact ⟨1, by simp [f, hxp, hpu]⟩
      by_cases hxq : x = q
      · exact ⟨2, by simp [f, hxq, hqu, hpq]⟩
      by_cases hux : G.Adj u x
      · rcases onlyTwoNeighbors x hxu hux with h | h <;> contradiction
      · have hxw := uniqueNonneighbor x hxu hux
        exact ⟨3, by simp [f, hxw, hwu, hpw, hqw]⟩
    let e : Fin 4 ≃ V := Equiv.ofBijective f ⟨hfInjective, hfSurjective⟩
    have hpqAdj : G.Adj p q := hclique p q hpu hqu hpq
    have hpwAdj : G.Adj p w := hclique p w hpu hwu hpw
    have hqwAdj : G.Adj q w := hclique q w hqu hwu hqw
    have hnwu : ¬G.Adj w u := fun h => hnuw h.symm
    have hiso : Nonempty (G ≃g Knt 4 2) := by
      have e' : Knt 4 2 ≃g G :=
        { toEquiv := e
          map_rel_iff' := by
            intro i j
            fin_cases i <;> fin_cases j <;>
              simp [e, f, Knt, hup, hup.symm, huq, huq.symm, hnuw, hnwu,
                hpqAdj, hpqAdj.symm, hpwAdj, hpwAdj.symm,
                hqwAdj, hqwAdj.symm] }
      exact ⟨e'.symm⟩
    exact False.elim (h_not_K42 hiso)
  · exact bklpsLemma9_of_delete_noncomplete G h_two_connected u v h_distinct
      h_neighborhood h_deletions hdeleteComplete

end

end BKLPS.External
