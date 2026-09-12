import Proof.ExternalResults.BKLPSLemma9Proof1
import Proof.ExternalResults.BKLPSLemma9Proof2

namespace BKLPS.External

open SimpleGraph

noncomputable section

universe u

/-- The second conclusion of BKLPS Lemma 9: every block of the relevant
deletion is unexceptional. -/
theorem bklpsLemma9Proof3
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
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, h_distinct.symm⟩) :
    ∀ C : Set {x : V // x ≠ u}, IsBlock (deleteVertex G u) C →
      letI : Fintype C := Fintype.ofFinite C
      IsUnexceptional ((deleteVertex G u).induce C) := by
  classical
  have huvAdj : G.Adj u v := by
    have hu : u ∈ closedNeighborhood G u := by
      simp [closedNeighborhood]
    have huv' := h_neighborhood hu
    have huv'' : u = v ∨ G.Adj v u := by
      simpa [closedNeighborhood, openNeighborhood] using huv'
    rcases huv'' with h | h
    · exact False.elim (h_distinct h)
    · exact h.symm
  intro C hC
  letI : Fintype C := Fintype.ofFinite C
  unfold IsUnexceptional
  intro hExceptional
  let H := deleteVertex G u
  let vc : {x : V // x ≠ u} := ⟨v, h_distinct.symm⟩
  have hvC : vc ∈ C := uniqueCut_mem_isBlock H vc hunique C hC
  obtain ⟨x, hxC, hxv, hux⟩ :=
    exists_u_neighbor_in_block G h_two_connected u v h_distinct hunique C hC
  let xC : C := ⟨x, hxC⟩
  let vC : C := ⟨vc, hvC⟩
  have hxCvC : xC ≠ vC := by
    intro h
    exact hxv (congrArg (fun q : C => q.1.1) h)
  have completeFalse (hcomplete :
      IsomorphicToKn ((deleteVertex G u).induce C)) : False := by
    by_cases hcard : 3 ≤ Fintype.card C
    · have hremain : ((Finset.univ.erase xC).erase vC).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        have hc0 : ((Finset.univ.erase xC).erase vC).card = 0 := by
          simp [hempty]
        have hxmem : xC ∈ (Finset.univ : Finset C) := Finset.mem_univ _
        have hvmem : vC ∈ (Finset.univ.erase xC : Finset C) := by
          simp [hxCvC.symm]
        rw [Finset.card_erase_of_mem hvmem,
          Finset.card_erase_of_mem hxmem, Finset.card_univ] at hc0
        omega
      obtain ⟨zC, hzC⟩ := hremain
      have hzx : zC ≠ xC := by
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hzC).2).1
      have hzvC : zC ≠ vC := by simpa using (Finset.mem_erase.mp hzC).1
      let z := zC.1
      have hzMem : z ∈ C := zC.2
      have hzv : z.1 ≠ v := by
        intro h
        exact hzvC (by
          apply Subtype.ext
          apply Subtype.ext
          exact h)
      have hzxH : z ≠ x := by
        intro h
        exact hzx (Subtype.ext h)
      have hzvc : z ≠ vc := by
        intro h
        exact hzvC (Subtype.ext h)
      have hxdom : ∀ t : C, xC ≠ t →
          ((deleteVertex G u).induce C).Adj xC t := by
        intro t hxt
        exact adj_of_isomorphicToKn ((deleteVertex G u).induce C) hcomplete hxt
      have hvdom : ∀ t : C, vC ≠ t →
          ((deleteVertex G u).induce C).Adj vC t := by
        intro t hvt
        exact adj_of_isomorphicToKn ((deleteVertex G u).induce C) hcomplete hvt
      have hN : closedNeighborhood G z.1 ⊆ closedNeighborhood G x.1 :=
        closedNeighborhood_subset_of_block_dominates G u v h_distinct
          hunique C hC z x hzMem hxC hzv hzxH hxdom (fun _ => hux)
      exact no_global_and_local_dominator_in_block G h_two_connected u v
        h_distinct huvAdj h_deletions hunique C hC z x vc hzMem hxC hvC
        hzv hxv hzxH hzvc (by
          intro h
          exact hxv (congrArg Subtype.val h)) hN hvdom
    · /- A complete two-vertex block is the single-edge subcase treated at
         the start of Case 1 in the paper. -/
      have hcardTwo : Fintype.card C ≤ 2 := by omega
      have hall (t : C) : t = xC ∨ t = vC := by
        by_contra ht
        push_neg at ht
        have hsub : ({xC, vC, t} : Finset C) ⊆ Finset.univ :=
          Finset.subset_univ _
        have hc := Finset.card_le_card hsub
        have hthree : ({xC, vC, t} : Finset C).card = 3 := by
          simp [hxCvC, ht.1.symm, ht.2.symm]
        rw [hthree, Finset.card_univ] at hc
        omega
      have hvdom : ∀ t : C, vC ≠ t →
          ((deleteVertex G u).induce C).Adj vC t := by
        intro t hvt
        exact adj_of_isomorphicToKn ((deleteVertex G u).induce C) hcomplete hvt
      have hNxv : closedNeighborhood G x.1 ⊆ closedNeighborhood G v :=
        closedNeighborhood_subset_of_block_dominates G u v h_distinct
          hunique C hC x vc hxC hvC hxv
          (by intro h; exact hxv (congrArg Subtype.val h)) hvdom
          (fun _ => huvAdj)
      have hNxu : closedNeighborhood G x.1 ⊆ closedNeighborhood G u := by
        intro t ht
        have ht' : t = x.1 ∨ G.Adj x.1 t := by
          simpa [closedNeighborhood, openNeighborhood] using ht
        rcases ht' with rfl | hxt
        · simp [closedNeighborhood, openNeighborhood, hux]
        · by_cases htu : t = u
          · simp [closedNeighborhood, htu]
          · let tH : {q : V // q ≠ u} := ⟨t, htu⟩
            have htC : tH ∈ C :=
              adj_mem_isBlock_of_uniqueCut H vc hunique C hC hxC
                (by intro h; exact hxv (congrArg Subtype.val h)) hxt
            rcases hall ⟨tH, htC⟩ with heq | heq
            · have : t = x.1 := congrArg (fun q : C => q.1.1) heq
              exact False.elim (hxt.ne this.symm)
            · have : t = v := congrArg (fun q : C => q.1.1) heq
              simp [closedNeighborhood, openNeighborhood, this, huvAdj]
      obtain ⟨C₁, C₂, hC₁, hC₂, hC₁C₂, _, _⟩ :=
        exists_two_blocks_of_cutVertex H vc hunique.1
      obtain ⟨D, hD, hCD⟩ : ∃ D : Set {q : V // q ≠ u},
          IsBlock H D ∧ C ≠ D := by
        by_cases hCC₁ : C = C₁
        · exact ⟨C₂, hC₂, fun h => hC₁C₂ (hCC₁.symm.trans h)⟩
        · exact ⟨C₁, hC₁, hCC₁⟩
      obtain ⟨y, hyD, hyv, _⟩ :=
        exists_u_neighbor_in_block G h_two_connected u v h_distinct
          hunique D hD
      have hyx : y.1 ≠ x.1 := by
        intro h
        have hyEqx : y = x := Subtype.ext h
        have hxD : x ∈ D := by simpa [hyEqx] using hyD
        exact hCD (isBlock_eq_of_two_common H C D hC hD vc x hvC
          (uniqueCut_mem_isBlock H vc hunique D hD) hxC hxD
          (by intro heq; exact hxv (congrArg Subtype.val heq).symm))
      have hdeleteTwo : IsTwoConnected (deleteVertex G x.1) :=
        delete_two_dominated_twoConnected G h_two_connected x.1 u v y.1
          x.2 hxv h_distinct hyx y.2 hyv hNxu hNxv
      have hnotTwo := (bklpsLemma9Proof1 G h_two_connected h_noncomplete
        h_not_K42 h_deletions h_exists x.1 v hxv hNxv).1
      exact hnotTwo hdeleteTwo
  have ktwoFalse (hKtwo :
      Nonempty (((deleteVertex G u).induce C) ≃g Knt (Fintype.card C) 2)) :
      False := by
    /- The `K_t^2` block is Case 2 of the BKLPS block analysis. -/
    by_cases hlarge : 6 ≤ Fintype.card C
    · obtain ⟨e⟩ := hKtwo
      let a₀ : Fin (Fintype.card C) := ⟨3, by omega⟩
      let b₀ : Fin (Fintype.card C) := ⟨4, by omega⟩
      let c₀ : Fin (Fintype.card C) := ⟨5, by omega⟩
      let a : C := e.symm a₀
      let b : C := e.symm b₀
      let c : C := e.symm c₀
      have hab : a ≠ b := by
        intro h
        have := congrArg e h
        simp [a, b, a₀, b₀] at this
      have hac : a ≠ c := by
        intro h
        have := congrArg e h
        simp [a, c, a₀, c₀] at this
      have hbc : b ≠ c := by
        intro h
        have := congrArg e h
        simp [b, c, b₀, c₀] at this
      let P : C → Prop := fun t => G.Adj u t.1.1
      let Q : C → Prop := fun t => 3 ≤ (e t).val
      have hQa : Q a := by simp [Q, a, a₀]
      have hQb : Q b := by simp [Q, b, b₀]
      have hQc : Q c := by simp [Q, c, c₀]
      obtain ⟨zC, wC, _rC, hzw, _hzr, _hwr, hzvC, hwvC,
          hQz, hQw, _hQr, hattach⟩ :=
        orient_three_candidates P Q a b c vC hab hac hbc hQa hQb hQc
      let r₀ : Fin (Fintype.card C) := ⟨1, by omega⟩
      let rC : C := e.symm r₀
      let z := zC.1
      let w := wC.1
      let r := rC.1
      have hzv : z.1 ≠ v := by
        intro h
        exact hzvC (by
          apply Subtype.ext
          apply Subtype.ext
          exact h)
      have hwv : w.1 ≠ v := by
        intro h
        exact hwvC (by
          apply Subtype.ext
          apply Subtype.ext
          exact h)
      have hzwH : z ≠ w := by intro h; exact hzw (Subtype.ext h)
      have hzr : z ≠ r := by
        intro h
        have heqC : zC = rC := Subtype.ext h
        have heq := congrArg (fun q : C => (e q).val) heqC
        have hzval : 3 ≤ (e zC).val := hQz
        simp [rC, r₀] at heq
        omega
      have hwr : w ≠ r := by
        intro h
        have heqC : wC = rC := Subtype.ext h
        have heq := congrArg (fun q : C => (e q).val) heqC
        have hwval : 3 ≤ (e wC).val := hQw
        simp [rC, r₀] at heq
        omega
      have hrdom : ∀ t : C, rC ≠ t →
          ((deleteVertex G u).induce C).Adj rC t := by
        intro t hrt
        apply e.map_rel_iff.mp
        rw [show e rC = r₀ by simp [rC]]
        refine ⟨?_, ?_⟩
        · intro heq
          apply hrt
          apply e.injective
          simpa [rC] using heq
        · by_cases ht0 : (e t).val = 0
          · exact Or.inr (Or.inr ⟨ht0, by simp [r₀]⟩)
          · exact Or.inl ⟨by simp [r₀], ht0⟩
      have hlocal : ∀ t : C, t = zC ∨
          ((deleteVertex G u).induce C).Adj zC t →
        t = wC ∨ ((deleteVertex G u).induce C).Adj wC t := by
        intro t ht
        by_cases htw : t = wC
        · exact Or.inl htw
        · right
          apply e.map_rel_iff.mp
          have hew0 : (e wC).val ≠ 0 := by
            have := hQw
            omega
          have het0 : (e t).val ≠ 0 := by
            rcases ht with rfl | hzt
            · have := hQz
              omega
            · have hcan := e.map_rel_iff.mpr hzt
              rcases hcan.2 with hold | hzeroLeft | hzeroRight
              · exact hold.2
              · have := hQz
                omega
              · have := hQz
                omega
          exact ⟨fun heq => htw (e.injective heq.symm),
            Or.inl ⟨hew0, het0⟩⟩
      have hN : closedNeighborhood G z.1 ⊆ closedNeighborhood G w.1 :=
        closedNeighborhood_subset_of_block_subset G u v h_distinct hunique
          C hC z w zC.2 wC.2 hzv hzwH hlocal (by
            intro huz
            exact hattach huz)
      exact no_global_and_local_dominator_in_block G h_two_connected u v
        h_distinct huvAdj h_deletions hunique C hC z w r zC.2 wC.2 rC.2
        hzv hwv hzwH hzr hwr hN hrdom
    · /- The remaining `K_t^2` blocks have orders at most five and are the
         finite attachment patterns isolated in Case 2 of the paper. -/
      obtain ⟨e⟩ := hKtwo
      by_cases hn4 : 4 ≤ Fintype.card C
      · let z₀ : Fin (Fintype.card C) := ⟨0, by omega⟩
        let d₁₀ : Fin (Fintype.card C) := ⟨1, by omega⟩
        let d₂₀ : Fin (Fintype.card C) := ⟨2, by omega⟩
        let z₀C : C := e.symm z₀
        let d₁C : C := e.symm d₁₀
        let d₂C : C := e.symm d₂₀
        let z₀H := z₀C.1
        let d₁ := d₁C.1
        let d₂ := d₂C.1
        have hd₁d₂C : d₁C ≠ d₂C := by
          intro h
          have := congrArg e h
          simp [d₁C, d₂C, d₁₀, d₂₀] at this
        have hz₀d₁C : z₀C ≠ d₁C := by
          intro h
          have := congrArg e h
          simp [z₀C, d₁C, z₀, d₁₀] at this
        have hz₀d₂C : z₀C ≠ d₂C := by
          intro h
          have := congrArg e h
          simp [z₀C, d₂C, z₀, d₂₀] at this
        have hd₁dom : ∀ t : C, d₁C ≠ t →
            ((deleteVertex G u).induce C).Adj d₁C t := by
          intro t hne
          apply e.map_rel_iff.mp
          rw [show e d₁C = d₁₀ by simp [d₁C]]
          refine ⟨?_, ?_⟩
          · intro h
            exact hne (e.injective (by simpa [d₁C] using h))
          · by_cases ht0 : (e t).val = 0
            · exact Or.inr (Or.inr ⟨ht0, by simp [d₁₀]⟩)
            · exact Or.inl ⟨by simp [d₁₀], ht0⟩
        have hd₂dom : ∀ t : C, d₂C ≠ t →
            ((deleteVertex G u).induce C).Adj d₂C t := by
          intro t hne
          apply e.map_rel_iff.mp
          rw [show e d₂C = d₂₀ by simp [d₂C]]
          refine ⟨?_, ?_⟩
          · intro h
            exact hne (e.injective (by simpa [d₂C] using h))
          · by_cases ht0 : (e t).val = 0
            · exact Or.inr (Or.inr ⟨ht0, by simp [d₂₀]⟩)
            · exact Or.inl ⟨by simp [d₂₀], ht0⟩
        have freshThree (p q r : C) : ∃ z : C, z ≠ p ∧ z ≠ q ∧ z ≠ r := by
          by_contra hnone
          push_neg at hnone
          have hsub : (Finset.univ : Finset C) ⊆ {p, q, r} := by
            intro t ht
            by_cases htp : t = p
            · simp [htp]
            · by_cases htq : t = q
              · simp [htq]
              · simp [htp, htq, hnone t htp htq]
          have hc := Finset.card_le_card hsub
          simp only [Finset.card_univ] at hc
          have hthree : ({p, q, r} : Finset C).card ≤ 3 := by
            have h₁ := Finset.card_insert_le p ({q, r} : Finset C)
            have h₂ := Finset.card_insert_le q ({r} : Finset C)
            simp only [Finset.card_singleton] at h₂
            omega
          omega
        by_cases hvd₁ : vC = d₁C
        · obtain ⟨zC, hzxC, hzvC, hzd₂C⟩ := freshThree xC vC d₂C
          let z := zC.1
          have hzv : z.1 ≠ v := by
            intro h
            exact hzvC (by apply Subtype.ext; apply Subtype.ext; exact h)
          have hd₂v : d₂.1 ≠ v := by
            intro h
            apply hd₁d₂C
            exact hvd₁.symm.trans (by
              apply Subtype.ext
              apply Subtype.ext
              exact h.symm)
          have hd₁vEq : d₁.1 = v := by
            exact (congrArg (fun q : C => q.1.1) hvd₁).symm
          have hN₁ : closedNeighborhood G z.1 ⊆ closedNeighborhood G d₁.1 :=
            closedNeighborhood_subset_of_block_dominates G u v h_distinct
              hunique C hC z d₁ zC.2 d₁C.2 hzv
              (by
                intro h
                apply hzvC
                exact (Subtype.ext h).trans hvd₁.symm)
              hd₁dom (fun _ => by simpa [hd₁vEq] using huvAdj)
          have hN : closedNeighborhood G z.1 ⊆ closedNeighborhood G v := by
            simpa [hd₁vEq] using hN₁
          exact no_cut_and_local_dominator_in_block G h_two_connected u v
            h_distinct huvAdj h_deletions hunique C hC z x d₂ zC.2 hxC
            d₂C.2 hzv hxv hd₂v (by intro h; exact hzxC (Subtype.ext h))
            (by intro h; exact hzd₂C (Subtype.ext h)) hN hux hd₂dom
        · by_cases hvd₂ : vC = d₂C
          · obtain ⟨zC, hzxC, hzvC, hzd₁C⟩ := freshThree xC vC d₁C
            let z := zC.1
            have hzv : z.1 ≠ v := by
              intro h
              exact hzvC (by apply Subtype.ext; apply Subtype.ext; exact h)
            have hd₁v : d₁.1 ≠ v := by
              intro h
              apply hd₁d₂C
              have hd₁vC : d₁C = vC := by
                apply Subtype.ext
                apply Subtype.ext
                exact h
              exact hd₁vC.trans hvd₂
            have hd₂vEq : d₂.1 = v := by
              exact (congrArg (fun q : C => q.1.1) hvd₂).symm
            have hN₂ : closedNeighborhood G z.1 ⊆ closedNeighborhood G d₂.1 :=
              closedNeighborhood_subset_of_block_dominates G u v h_distinct
                hunique C hC z d₂ zC.2 d₂C.2 hzv
                (by
                  intro h
                  apply hzvC
                  exact (Subtype.ext h).trans hvd₂.symm)
                hd₂dom (fun _ => by simpa [hd₂vEq] using huvAdj)
            have hN : closedNeighborhood G z.1 ⊆ closedNeighborhood G v := by
              simpa [hd₂vEq] using hN₂
            exact no_cut_and_local_dominator_in_block G h_two_connected u v
              h_distinct huvAdj h_deletions hunique C hC z x d₁ zC.2 hxC
              d₁C.2 hzv hxv hd₁v (by intro h; exact hzxC (Subtype.ext h))
              (by intro h; exact hzd₁C (Subtype.ext h)) hN hux hd₁dom
          · have hd₁v : d₁.1 ≠ v := by
              intro h
              exact hvd₁ (by apply Subtype.ext; apply Subtype.ext; exact h.symm)
            have hd₂v : d₂.1 ≠ v := by
              intro h
              exact hvd₂ (by apply Subtype.ext; apply Subtype.ext; exact h.symm)
            by_cases hud₁ : G.Adj u d₁.1
            · obtain ⟨zC, hzvC, hzd₁C, hzd₂C⟩ := freshThree vC d₁C d₂C
              let z := zC.1
              have hzv : z.1 ≠ v := by
                intro h
                exact hzvC (by apply Subtype.ext; apply Subtype.ext; exact h)
              have hN : closedNeighborhood G z.1 ⊆ closedNeighborhood G d₁.1 :=
                closedNeighborhood_subset_of_block_dominates G u v h_distinct
                  hunique C hC z d₁ zC.2 d₁C.2 hzv
                  (by intro h; exact hzd₁C (Subtype.ext h)) hd₁dom
                  (fun _ => hud₁)
              exact no_global_and_local_dominator_in_block G h_two_connected u v
                h_distinct huvAdj h_deletions hunique C hC z d₁ d₂ zC.2
                d₁C.2 d₂C.2 hzv hd₁v
                (by intro h; exact hzd₁C (Subtype.ext h))
                (by intro h; exact hzd₂C (Subtype.ext h))
                (by intro h; exact hd₁d₂C (Subtype.ext h)) hN hd₂dom
            · by_cases hud₂ : G.Adj u d₂.1
              · obtain ⟨zC, hzvC, hzd₂C, hzd₁C⟩ := freshThree vC d₂C d₁C
                let z := zC.1
                have hzv : z.1 ≠ v := by
                  intro h
                  exact hzvC (by apply Subtype.ext; apply Subtype.ext; exact h)
                have hN : closedNeighborhood G z.1 ⊆ closedNeighborhood G d₂.1 :=
                  closedNeighborhood_subset_of_block_dominates G u v h_distinct
                    hunique C hC z d₂ zC.2 d₂C.2 hzv
                    (by intro h; exact hzd₂C (Subtype.ext h)) hd₂dom
                    (fun _ => hud₂)
                exact no_global_and_local_dominator_in_block G h_two_connected u v
                  h_distinct huvAdj h_deletions hunique C hC z d₂ d₁ zC.2
                  d₂C.2 d₁C.2 hzv hd₂v
                  (by intro h; exact hzd₂C (Subtype.ext h))
                  (by intro h; exact hzd₁C (Subtype.ext h))
                  (by intro h; exact hd₁d₂C (Subtype.ext h).symm) hN hd₁dom
              · have hz₀v : z₀H.1 ≠ v := by
                  intro hzvEq
                  have hvz₀C : vC = z₀C := by
                    apply Subtype.ext
                    apply Subtype.ext
                    exact hzvEq.symm
                  have hxIn : x.1 ∈ closedNeighborhood G u := by
                    simp [closedNeighborhood, openNeighborhood, hux]
                  have hxInV := h_neighborhood hxIn
                  have hvx : G.Adj v x.1 := by
                    have hxCases : x.1 = v ∨ G.Adj v x.1 := by
                      simpa [closedNeighborhood, openNeighborhood] using hxInV
                    exact hxCases.resolve_left hxv
                  have hvxC : ((deleteVertex G u).induce C).Adj vC xC := hvx
                  have hcan := e.map_rel_iff.mpr hvxC
                  have hevz : e vC = z₀ := by simp [hvz₀C, z₀C]
                  rw [hevz] at hcan
                  have hx12 : (e xC).val = 1 ∨ (e xC).val = 2 := by
                    simp only [Knt] at hcan
                    rcases hcan.2 with hboth | hleft | hright
                    · exact False.elim (hboth.1 (by simp [z₀]))
                    · have := hleft.2
                      have hx0 : (e xC).val ≠ 0 := by
                        intro hzero
                        apply hcan.1
                        apply Fin.ext
                        simpa [z₀] using hzero.symm
                      omega
                    · exact False.elim (by
                        apply hcan.1
                        apply Fin.ext
                        simpa [z₀] using hright.1.symm)
                  rcases hx12 with hx1 | hx2
                  · apply hud₁
                    have hxd : xC = d₁C := by
                      apply e.injective
                      apply Fin.ext
                      simpa [d₁C, d₁₀] using hx1
                    have hval : x.1 = d₁.1 :=
                      congrArg (fun q : C => q.1.1) hxd
                    rw [hval] at hux
                    exact hux
                  · apply hud₂
                    have hxd : xC = d₂C := by
                      apply e.injective
                      apply Fin.ext
                      simpa [d₂C, d₂₀] using hx2
                    have hval : x.1 = d₂.1 :=
                      congrArg (fun q : C => q.1.1) hxd
                    rw [hval] at hux
                    exact hux
                have huz₀ : ¬G.Adj u z₀H.1 := by
                  intro huz
                  have hzIn : z₀H.1 ∈ closedNeighborhood G u := by
                    simp [closedNeighborhood, openNeighborhood, huz]
                  have hzInV := h_neighborhood hzIn
                  have hvz : G.Adj v z₀H.1 := by
                    have hzCases : z₀H.1 = v ∨ G.Adj v z₀H.1 := by
                      simpa [closedNeighborhood, openNeighborhood] using hzInV
                    exact hzCases.resolve_left hz₀v
                  have hvzC : ((deleteVertex G u).induce C).Adj vC z₀C := hvz
                  have hcan := e.map_rel_iff.mpr hvzC
                  have hzmap : e z₀C = z₀ := by simp [z₀C]
                  rw [hzmap] at hcan
                  have hv12 : (e vC).val = 1 ∨ (e vC).val = 2 := by
                    simp only [Knt] at hcan
                    rcases hcan.2 with hboth | hleft | hright
                    · exact False.elim (hboth.2 (by simp [z₀]))
                    · exact False.elim (by
                        have hevz : e vC = z₀ := by
                          apply Fin.ext
                          simpa [z₀] using hleft.1
                        apply hz₀v
                        have hvc : vC = z₀C := e.injective (by simpa [z₀C] using hevz)
                        exact (congrArg (fun q : C => q.1.1) hvc).symm)
                    · have hv0 : (e vC).val ≠ 0 := by
                        intro hzero
                        apply hcan.1
                        apply Fin.ext
                        simpa [z₀] using hzero
                      omega
                  rcases hv12 with hv1 | hv2
                  · apply hvd₁
                    apply e.injective
                    apply Fin.ext
                    simpa [d₁C, d₁₀] using hv1
                  · apply hvd₂
                    apply e.injective
                    apply Fin.ext
                    simpa [d₂C, d₂₀] using hv2
                have hN : closedNeighborhood G z₀H.1 ⊆
                    closedNeighborhood G d₁.1 :=
                  closedNeighborhood_subset_of_block_dominates G u v h_distinct
                    hunique C hC z₀H d₁ z₀C.2 d₁C.2 hz₀v
                    (by intro h; exact hz₀d₁C (Subtype.ext h)) hd₁dom
                    (fun h => False.elim (huz₀ h))
                exact no_global_and_local_dominator_in_block G h_two_connected u v
                  h_distinct huvAdj h_deletions hunique C hC z₀H d₁ d₂
                  z₀C.2 d₁C.2 d₂C.2 hz₀v hd₁v
                  (by intro h; exact hz₀d₁C (Subtype.ext h))
                  (by intro h; exact hz₀d₂C (Subtype.ext h))
                  (by intro h; exact hd₁d₂C (Subtype.ext h)) hN hd₂dom
      · have hcanon : Knt (Fintype.card C) 2 =
            completeGraph (Fin (Fintype.card C)) := by
          ext p q
          simp only [Knt, completeGraph]
          constructor
          · exact fun h => h.1
          · intro hpq
            refine ⟨hpq, ?_⟩
            by_cases hp0 : p.val = 0
            · exact Or.inr (Or.inl ⟨hp0, by omega⟩)
            · by_cases hq0 : q.val = 0
              · exact Or.inr (Or.inr ⟨hq0, by omega⟩)
              · exact Or.inl ⟨hp0, hq0⟩
        rw [hcanon] at e
        exact completeFalse ⟨e⟩
  rcases hExceptional with hcomplete | hKtwo | hKhigh
  · exact completeFalse hcomplete
  · exact ktwoFalse hKtwo
  · /- The `K_t^(t-2)` block has at least three dominating vertices unless
         it coincides with the preceding `K_4^2` case. -/
    by_cases hlarge : 5 ≤ Fintype.card C
    · obtain ⟨e⟩ := hKhigh
      let a₀ : Fin (Fintype.card C) := ⟨1, by omega⟩
      let b₀ : Fin (Fintype.card C) := ⟨2, by omega⟩
      let c₀ : Fin (Fintype.card C) := ⟨3, by omega⟩
      let a : C := e.symm a₀
      let b : C := e.symm b₀
      let c : C := e.symm c₀
      have hab : a ≠ b := by
        intro h
        have := congrArg e h
        simp [a, b, a₀, b₀] at this
      have hac : a ≠ c := by
        intro h
        have := congrArg e h
        simp [a, c, a₀, c₀] at this
      have hbc : b ≠ c := by
        intro h
        have := congrArg e h
        simp [b, c, b₀, c₀] at this
      have canonicalDominates (d : Fin (Fintype.card C))
          (hd0 : d.val ≠ 0) (hdtop : d.val ≤ Fintype.card C - 2) :
          ∀ t : Fin (Fintype.card C), d ≠ t →
            (Knt (Fintype.card C) (Fintype.card C - 2)).Adj d t := by
        intro t hdt
        refine ⟨hdt, ?_⟩
        by_cases ht0 : t.val = 0
        · exact Or.inr (Or.inr ⟨ht0, hdtop⟩)
        · exact Or.inl ⟨hd0, ht0⟩
      have hQa : ∀ t : C, a ≠ t →
          ((deleteVertex G u).induce C).Adj a t := by
        intro t hat
        apply e.map_rel_iff.mp
        rw [show e a = a₀ by simp [a]]
        apply canonicalDominates a₀ (by simp [a₀]) (by simp [a₀]; omega)
        intro h
        apply hat
        apply e.injective
        simpa [a] using h
      have hQb : ∀ t : C, b ≠ t →
          ((deleteVertex G u).induce C).Adj b t := by
        intro t hbt
        apply e.map_rel_iff.mp
        rw [show e b = b₀ by simp [b]]
        apply canonicalDominates b₀ (by simp [b₀]) (by simp [b₀]; omega)
        intro h
        apply hbt
        apply e.injective
        simpa [b] using h
      have hQc : ∀ t : C, c ≠ t →
          ((deleteVertex G u).induce C).Adj c t := by
        intro t hct
        apply e.map_rel_iff.mp
        rw [show e c = c₀ by simp [c]]
        apply canonicalDominates c₀ (by simp [c₀]) (by simp [c₀]; omega)
        intro h
        apply hct
        apply e.injective
        simpa [c] using h
      let P : C → Prop := fun t => G.Adj u t.1.1
      let Q : C → Prop := fun d => ∀ t : C, d ≠ t →
        ((deleteVertex G u).induce C).Adj d t
      obtain ⟨zC, wC, rC, hzw, hzr, hwr, hzvC, hwvC,
          hQz, hQw, hQr, hattach⟩ :=
        orient_three_candidates P Q a b c vC hab hac hbc hQa hQb hQc
      let z := zC.1
      let w := wC.1
      let r := rC.1
      have hzv : z.1 ≠ v := by
        intro h
        exact hzvC (by
          apply Subtype.ext
          apply Subtype.ext
          exact h)
      have hwv : w.1 ≠ v := by
        intro h
        exact hwvC (by
          apply Subtype.ext
          apply Subtype.ext
          exact h)
      have hzwH : z ≠ w := by intro h; exact hzw (Subtype.ext h)
      have hzrH : z ≠ r := by intro h; exact hzr (Subtype.ext h)
      have hwrH : w ≠ r := by intro h; exact hwr (Subtype.ext h)
      have hN : closedNeighborhood G z.1 ⊆ closedNeighborhood G w.1 :=
        closedNeighborhood_subset_of_block_dominates G u v h_distinct
          hunique C hC z w zC.2 wC.2 hzv hzwH hQw (by
            intro huz
            exact hattach huz)
      exact no_global_and_local_dominator_in_block G h_two_connected u v
        h_distinct huvAdj h_deletions hunique C hC z w r zC.2 wC.2 rC.2
        hzv hwv hzwH hzrH hwrH hN hQr
    · /- Orders at most four reduce to the edge or `K_4^2` cases. -/
      obtain ⟨e⟩ := hKhigh
      have hcardTwo : 2 ≤ Fintype.card C := by
        have hsub : ({xC, vC} : Finset C) ⊆ Finset.univ := Finset.subset_univ _
        have hc := Finset.card_le_card hsub
        simpa [hxCvC] using hc
      have htargetConn :
          (Knt (Fintype.card C) (Fintype.card C - 2)).Connected :=
        e.connected_iff.mp hC.1.1
      have htargetNoCut :
          HasNoCutVertex (Knt (Fintype.card C) (Fintype.card C - 2)) := by
        intro w hwcut
        apply hC.1.2 (e.symm w)
        refine ⟨?_, e.connected_iff.mpr hwcut.2.1, ?_⟩
        · simpa using hwcut.1
        · intro hdelete
          apply hwcut.2.2
          have hc := (deleteVertexIso e (e.symm w)).connected_iff.mp hdelete
          rw [show e (e.symm w) = w by simp] at hc
          exact hc
      by_cases hcardThree : 3 ≤ Fintype.card C
      · by_cases hcardFour : 4 ≤ Fintype.card C
        · have ht : Fintype.card C - 2 = 2 := by omega
          apply ktwoFalse
          exact ⟨by simpa [ht] using e⟩
        · have hn : Fintype.card C = 3 := by omega
          let m : Fin (Fintype.card C) := ⟨1, by omega⟩
          have hdelete :
              ¬(deleteVertex (Knt (Fintype.card C) (Fintype.card C - 2)) m).Connected := by
            let z : {q : Fin (Fintype.card C) // q ≠ m} :=
              ⟨⟨0, by omega⟩, by
                intro h
                have hv := congrArg Fin.val h
                simp [m] at hv⟩
            let t : {q : Fin (Fintype.card C) // q ≠ m} :=
              ⟨⟨2, by omega⟩, by
                intro h
                have hv := congrArg Fin.val h
                simp [m] at hv⟩
            apply not_connected_of_no_edges _ z t
            · intro h
              have hv := congrArg (fun q : {q : Fin (Fintype.card C) // q ≠ m} => q.1.val) h
              simp [z, t] at hv
            · intro p q hpq
              change (Knt (Fintype.card C) (Fintype.card C - 2)).Adj p.1 q.1 at hpq
              simp only [Knt] at hpq
              have hp1 : p.1.val ≠ 1 := by
                intro hp
                exact p.2 (Fin.ext (by simpa [m] using hp))
              have hq1 : q.1.val ≠ 1 := by
                intro hq
                exact q.2 (Fin.ext (by simpa [m] using hq))
              omega
          exact htargetNoCut m ⟨by simp [hn], htargetConn, hdelete⟩
      · have hn : Fintype.card C = 2 := by omega
        have hno : ∀ p q : Fin (Fintype.card C),
            ¬(Knt (Fintype.card C) (Fintype.card C - 2)).Adj p q := by
          intro p q hpq
          simp only [Knt] at hpq
          omega
        let z : Fin (Fintype.card C) := ⟨0, by omega⟩
        let t : Fin (Fintype.card C) := ⟨1, by omega⟩
        have hne : z ≠ t := by
          intro h
          have hv := congrArg Fin.val h
          simp [z, t] at hv
        exact (not_connected_of_no_edges _ z t hne hno) htargetConn

end

end BKLPS.External
