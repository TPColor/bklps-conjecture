import Proof.ExternalResults.BKLPSLemma7GoodsLowerBounds

/-! The proof content of BKLPS Lemma 7. -/

namespace BKLPS.External

open SimpleGraph

noncomputable section

universe u

/-- Along a geodesic whose first step does not decrease an integer-valued
level but whose endpoint has lower level, the first eventual descent is
preceded either by a rise or by a horizontal edge.  The three vertices at
that turn form an induced two-edge path. -/
private theorem geodesic_turn
    {W : Type u} [DecidableEq W] (H : SimpleGraph W)
    (level : W → ℕ) {r s : W} (p : H.Walk r s)
    (hp : p.length = H.dist r s)
    (hend : level s < level r)
    (hfirst : ∀ (y : W) (q : H.Walk y s) (h : H.Adj r y),
      p = Walk.cons h q → level r ≤ level y) :
    ∃ x y z : W, H.Adj x y ∧ H.Adj y z ∧
      ¬H.Adj x z ∧ x ≠ z ∧ level x ≤ level y ∧
        level z < level y := by
  induction p with
  | nil => exact False.elim (by simpa using hend)
  | @cons r y s hry q ih =>
      cases q with
      | nil =>
          have hle := hfirst y Walk.nil hry rfl
          exact False.elim (by simpa using (not_lt_of_ge hle hend))
      | @cons y z s hyz t =>
          have hryLevel : level r ≤ level y :=
            hfirst y (Walk.cons hyz t) hry rfl
          by_cases hdrop : level z < level y
          · have hne : r ≠ z := by
              intro h
              subst z
              have hshort := H.dist_le t
              simp only [Walk.length_cons] at hp
              omega
            have hnotAdj : ¬H.Adj r z := by
              intro hrz
              have hshort := H.dist_le (Walk.cons hrz t)
              simp only [Walk.length_cons] at hp hshort
              omega
            exact ⟨r, y, z, hry, hyz, hnotAdj, hne, hryLevel, hdrop⟩
          · have hqgeo : (Walk.cons hyz t).length = H.dist y s := by
              apply length_eq_dist_of_subwalk hp
              exact Walk.isSubwalk_cons (Walk.cons hyz t) hry
            have hend' : level s < level y := lt_of_lt_of_le hend hryLevel
            have hfirst' : ∀ (w : W) (q' : H.Walk w s) (h : H.Adj y w),
                Walk.cons hyz t = Walk.cons h q' → level y ≤ level w := by
              intro w q' h heq
              cases heq
              exact le_of_not_gt hdrop
            exact ih hqgeo hend' hfirst'

/-- Every non-root vertex of a connected graph has a neighbor in the
preceding BFS layer. -/
private theorem exists_lower_neighbor
    {V : Type u} [DecidableEq V] (G : SimpleGraph V) (hconn : G.Connected)
    (u x : V) (hxu : x ≠ u) :
    ∃ y : V, G.Adj x y ∧ G.dist u y < G.dist u x := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x u
  cases p with
  | nil => exact False.elim (hxu rfl)
  | @cons _ y _ hxy q =>
      refine ⟨y, hxy, ?_⟩
      have hle := G.dist_le q
      have hcommx : G.dist x u = G.dist u x := dist_comm
      have hcommy : G.dist y u = G.dist u y := dist_comm
      rw [hcommx] at hp
      rw [hcommy] at hle
      simp only [Walk.length_cons] at hp
      omega

/-- BKLPS condition (C1) for a specified nonedge in `N(u)`. -/
theorem bklpsLemma7_neighbor_nonedge
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (u v : V)
    (h_two_connected : IsTwoConnected G)
    (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (a b : {x : V // x ≠ u}) (hab : a ≠ b)
    (hua : G.Adj u a.1) (hub : G.Adj u b.1)
    (hnab : ¬(deleteVertex G u).Adj a b) :
    szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥ (2 : ℤ) := by
  have hgain := pairGain_two_of_neighbor_nonedge G h_two_connected.2.1 u v
    h_distinct h_neighborhood a b hab hua hub hnab
  have hglobal := gap_sub_deleteVertex_ge_vertexContribution_add_pairGain
    G h_two_connected.2.1 u v h_distinct h_neighborhood a b
  have hcu : 0 ≤ vertexContribution G u := by
    unfold vertexContribution
    exact Finset.sum_nonneg fun x _ =>
      pairGap_nonneg G h_two_connected.2.1 u x
  omega

/-- The dominating-vertex branch of BKLPS Lemma 7.  A nonedge `ab` of
`G-u` gains the two good edges `ua` and `ub`, which is precisely (C1). -/
theorem bklpsLemma7_dominating
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (u v : V)
    (h_two_connected : IsTwoConnected G)
    (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete_noncomplete : ¬IsomorphicToKn (deleteVertex G u))
    (hdom : ∀ x : V, x ≠ u → G.Adj u x) :
    szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥ (2 : ℤ) := by
  obtain ⟨a, b, hab, hnab⟩ :=
    exists_nonedge_of_not_isomorphicToKn (deleteVertex G u) h_delete_noncomplete
  exact bklpsLemma7_neighbor_nonedge G u v h_two_connected h_distinct
    h_neighborhood a b hab (hdom a.1 a.2) (hdom b.1 b.2) hnab

/-- BKLPS condition (C2): a vertex with at least two neighbors in the
preceding BFS layer contributes at least two by itself. -/
theorem bklpsLemma7_C2
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (u v a : V)
    (h_two_connected : IsTwoConnected G)
    (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (hparents : (lowerNeighbors G u a).card ≥ 2) :
    szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥ (2 : ℤ) := by
  have hpair := pairGap_ge_two_mul_lowerNeighbors_sub_two
    G h_two_connected.2.1 u a
  have hglobal := gap_sub_deleteVertex_ge_vertexContribution G
    h_two_connected.2.1 u v h_distinct h_neighborhood
  have hterm : pairGap G u a ≤ vertexContribution G u := by
    unfold vertexContribution
    have ha_mem : a ∈ (Finset.univ : Finset V) := by simp
    rw [← Finset.sum_erase_add _ _ ha_mem]
    have hrest : 0 ≤ ∑ x ∈ (Finset.univ.erase a), pairGap G u x := by
      exact Finset.sum_nonneg fun x hx =>
        pairGap_nonneg G h_two_connected.2.1 u x
    omega
  omega

/-- BKLPS condition (C3) in the two-sided horizontal-edge configuration
produced by the avoiding path: each endpoint receives one extra good edge. -/
private theorem bklpsLemma7_C3_vertexContribution
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u b₁ b₂ z₁ z₂ : V)
    (hb : G.Adj b₁ b₂) (hhoriz : G.dist u b₁ = G.dist u b₂)
    (hz₁ : G.Adj b₁ z₁) (hlower₁ : G.dist u z₁ < G.dist u b₁)
    (hcross₁ : ¬G.Adj z₁ b₂)
    (hz₂ : G.Adj b₂ z₂) (hlower₂ : G.dist u z₂ < G.dist u b₂)
    (hcross₂ : ¬G.Adj z₂ b₁) :
    vertexContribution G u ≥ (2 : ℤ) := by
  classical
  have hgap₂ : pairGap G u b₂ ≥ 1 :=
    pairGap_ge_one_of_horizontalEdge G hconn u b₁ b₂ z₁ hb hhoriz
      hz₁ hlower₁ hcross₁
  have hgap₁ : pairGap G u b₁ ≥ 1 :=
    pairGap_ge_one_of_horizontalEdge G hconn u b₂ b₁ z₂ hb.symm hhoriz.symm
      hz₂ hlower₂ hcross₂
  have hne : b₁ ≠ b₂ := hb.ne
  unfold vertexContribution
  have hb₁mem : b₁ ∈ (Finset.univ : Finset V) := Finset.mem_univ _
  rw [← Finset.sum_erase_add _ _ hb₁mem]
  have hb₂mem : b₂ ∈ (Finset.univ.erase b₁ : Finset V) := by
    simp [hne.symm]
  rw [← Finset.sum_erase_add _ _ hb₂mem]
  have hrest :
      0 ≤ ∑ x ∈ (Finset.univ.erase b₁).erase b₂, pairGap G u x := by
    exact Finset.sum_nonneg fun x _ => pairGap_nonneg G hconn u x
  omega

/-- The C3 configuration already suffices for the deletion estimate. -/
private theorem bklpsLemma7_C3
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (u v b₁ b₂ z₁ z₂ : V)
    (h_two_connected : IsTwoConnected G)
    (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (hb : G.Adj b₁ b₂) (hhoriz : G.dist u b₁ = G.dist u b₂)
    (hz₁ : G.Adj b₁ z₁) (hlower₁ : G.dist u z₁ < G.dist u b₁)
    (hcross₁ : ¬G.Adj z₁ b₂)
    (hz₂ : G.Adj b₂ z₂) (hlower₂ : G.dist u z₂ < G.dist u b₂)
    (hcross₂ : ¬G.Adj z₂ b₁) :
    szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥ (2 : ℤ) := by
  have hc := bklpsLemma7_C3_vertexContribution G h_two_connected.2.1
    u b₁ b₂ z₁ z₂ hb hhoriz hz₁ hlower₁ hcross₁ hz₂ hlower₂ hcross₂
  have hglobal := gap_sub_deleteVertex_ge_vertexContribution G
    h_two_connected.2.1 u v h_distinct h_neighborhood
  omega

/-- BKLPS Lemma 7, isolated as the external deletion estimate used by the
informal proof. -/
theorem bklpsLemma7Proof1
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (u v : V)
    (h_two_connected : IsTwoConnected G)
    (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete_two_connected : IsTwoConnected (deleteVertex G u))
    (h_delete_noncomplete : ¬IsomorphicToKn (deleteVertex G u))
    (h_not_dominating : ¬∀ x : V, x ≠ u → G.Adj u x)
    (h_no_neighbor_nonedge : ¬∃ a b : {x : V // x ≠ u},
      a ≠ b ∧ G.Adj u a.1 ∧ G.Adj u b.1 ∧
        ¬(deleteVertex G u).Adj a b)
    (h_at_most_one_lower_neighbor : ¬∃ a : V,
      (lowerNeighbors G u a).card ≥ 2) :
    szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥ (2 : ℤ) := by
  classical
  push_neg at h_not_dominating
  obtain ⟨w, hwu, hnuw⟩ := h_not_dominating
  have hdistw : 1 < G.dist u w :=
    h_two_connected.2.1.one_lt_dist_of_ne_of_not_adj hwu.symm hnuw
  obtain ⟨p, hp⟩ :=
    h_two_connected.2.1.exists_walk_length_eq_dist u w
  cases p with
  | nil => simp at hp hdistw
  | @cons _ x _ hux q =>
    cases q with
    | nil => simp only [Walk.length_cons, Walk.length_nil] at hp; omega
    | @cons _ a _ hxa r =>
      have hau : u ≠ a := by
        intro hua
        subst a
        have hshort := G.dist_le r
        simp only [Walk.length_cons] at hp
        omega
      have hnua : ¬G.Adj u a := by
        intro hua
        have hshort := G.dist_le (Walk.cons hua r)
        simp only [Walk.length_cons] at hp hshort
        omega
      have hdista : G.dist u a = 2 := by
        have hle := G.dist_le
          (Walk.cons hux (Walk.cons hxa Walk.nil))
        have hgt := h_two_connected.2.1.one_lt_dist_of_ne_of_not_adj
          hau hnua
        simp only [Walk.length_cons, Walk.length_nil] at hle
        omega
      have hdistx : G.dist u x = 1 :=
        dist_eq_one_iff_adj.mpr hux
      have hxparent : x ∈ lowerNeighbors G u a := by
        simp [lowerNeighbors, openNeighborhood, hxa.symm, hdistx, hdista]
      have hparentCard : (lowerNeighbors G u a).card ≤ 1 := by
        by_contra h
        exact h_at_most_one_lower_neighbor ⟨a, by omega⟩
      let a' : {z : V // z ≠ x} := ⟨a, hxa.ne.symm⟩
      let u' : {z : V // z ≠ x} := ⟨u, hux.ne⟩
      obtain ⟨q, hq⟩ :=
        (h_two_connected.2.2 x).exists_walk_length_eq_dist a' u'
      have hend : G.dist u u'.1 < G.dist u a'.1 := by
        simp [u', a', hdista]
      have hfirst : ∀ (y : {z : V // z ≠ x})
          (q' : (deleteVertex G x).Walk y u')
          (hay : (deleteVertex G x).Adj a' y),
          q = Walk.cons hay q' →
            G.dist u a'.1 ≤ G.dist u y.1 := by
        intro y q' hay heq
        by_contra hlevel
        have hayG : G.Adj a y.1 := hay
        have hlevel' : G.dist u y.1 < G.dist u a := by
          dsimp [a'] at hlevel
          omega
        have hyparent : y.1 ∈ lowerNeighbors G u a := by
          apply Finset.mem_filter.mpr
          exact ⟨by simpa [openNeighborhood] using hayG, hlevel'⟩
        have hyx : y.1 = x :=
          (Finset.card_le_one.mp hparentCard) y.1 hyparent x hxparent
        exact y.2 hyx
      obtain ⟨b₁', b₂', z₂', hb', hz₂', hcross', hbne',
          hlevel₁, hlower₂⟩ :=
        geodesic_turn (deleteVertex G x) (fun y => G.dist u y.1)
          q hq hend hfirst
      have hb : G.Adj b₁'.1 b₂'.1 := hb'
      have hz₂ : G.Adj b₂'.1 z₂'.1 := hz₂'
      have hcross : ¬G.Adj b₁'.1 z₂'.1 := hcross'
      by_cases hrise : G.dist u b₁'.1 < G.dist u b₂'.1
      · have hb₁mem : b₁'.1 ∈ lowerNeighbors G u b₂'.1 := by
          simp [lowerNeighbors, openNeighborhood, hb.symm, hrise]
        have hz₂mem : z₂'.1 ∈ lowerNeighbors G u b₂'.1 := by
          simp [lowerNeighbors, openNeighborhood, hz₂, hlower₂]
        have htwoParents : 1 < (lowerNeighbors G u b₂'.1).card :=
          Finset.one_lt_card.mpr
            ⟨b₁'.1, hb₁mem, z₂'.1, hz₂mem,
              fun h => hbne' (Subtype.ext h)⟩
        exact False.elim (h_at_most_one_lower_neighbor ⟨b₂'.1, by omega⟩)
      · have hhoriz : G.dist u b₁'.1 = G.dist u b₂'.1 := by omega
        have hb₁u : b₁'.1 ≠ u := by
          intro h
          have hzero₁ : G.dist u b₁'.1 = 0 := by simp [h]
          have hzero₂ : G.dist u b₂'.1 = 0 := by omega
          have heq : u = b₂'.1 :=
            h_two_connected.2.1.dist_eq_zero_iff.mp hzero₂
          exact hb.ne (h.trans heq)
        obtain ⟨z₁, hz₁, hlower₁⟩ :=
          exists_lower_neighbor G h_two_connected.2.1 u b₁'.1 hb₁u
        have hcross₁ : ¬G.Adj z₁ b₂'.1 := by
          intro hz₁b₂
          have hz₁mem : z₁ ∈ lowerNeighbors G u b₂'.1 := by
            simp [lowerNeighbors, openNeighborhood, hz₁b₂.symm, hhoriz.symm,
              hlower₁]
          have hz₂mem : z₂'.1 ∈ lowerNeighbors G u b₂'.1 := by
            simp [lowerNeighbors, openNeighborhood, hz₂, hlower₂]
          have hcard : (lowerNeighbors G u b₂'.1).card ≤ 1 := by
            by_contra h
            exact h_at_most_one_lower_neighbor ⟨b₂'.1, by omega⟩
          have heq : z₁ = z₂'.1 :=
            (Finset.card_le_one.mp hcard) z₁ hz₁mem z₂'.1 hz₂mem
          exact hcross (by simpa [heq] using hz₁)
        exact bklpsLemma7_C3 G u v b₁'.1 b₂'.1 z₁ z₂'.1
          h_two_connected h_distinct h_neighborhood hb hhoriz hz₁
          hlower₁ hcross₁ hz₂ hlower₂ (fun h => hcross h.symm)

end

end BKLPS.External


/-!
Main route of BKLPS Lemma 7 as used here.

Equation (3) expresses deletion of `u` as the sum of the contributions
`η_G(u,x)` plus gains from good edges incident with `u`.  The proof finds two
units by four exhaustive configurations.  If `u` dominates the graph, the
noncompleteness of `G-u` supplies them.  If two neighbors of `u` are
nonadjacent in `G-u`, that pair supplies them.  If a vertex has two lower
neighbors in the distance layering from `u`, estimate (C2) supplies them.
Otherwise a geodesic from `u` to a nonneighbor must turn horizontally or
rise in a way that creates the required C3 configuration.  Each branch
proves `η(G)-η(G-u)≥2`.
-/

namespace BKLPS.External

open SimpleGraph

noncomputable section

universe u

/-- Bonamy--Knor--Lužar--Pinlou--Škrekovski, Lemma 7. -/
theorem bklpsLemma7
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (u v : V)
    (h_two_connected : IsTwoConnected G)
    (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete_two_connected : IsTwoConnected (deleteVertex G u))
    (h_delete_noncomplete : ¬IsomorphicToKn (deleteVertex G u)) :
    szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥ (2 : ℤ) := by
  /- This is BKLPS's case finish: `u` is dominating; two neighbors of `u`
  are nonadjacent after deletion; some distance layer has two predecessors;
  or none of these occurs, in which case a geodesic-turn argument supplies
  the required two units. -/
  classical
  by_cases hdom : ∀ x : V, x ≠ u → G.Adj u x
  · exact bklpsLemma7_dominating G u v h_two_connected h_distinct
      h_neighborhood h_delete_noncomplete hdom
  · by_cases hC1 : ∃ a b : {x : V // x ≠ u},
        a ≠ b ∧ G.Adj u a.1 ∧ G.Adj u b.1 ∧
          ¬(deleteVertex G u).Adj a b
    · obtain ⟨a, b, hab, hua, hub, hnab⟩ := hC1
      exact bklpsLemma7_neighbor_nonedge G u v h_two_connected h_distinct
        h_neighborhood a b hab hua hub hnab
    · by_cases hC2 : ∃ a : V, (lowerNeighbors G u a).card ≥ 2
      · obtain ⟨a, hparents⟩ := hC2
        exact bklpsLemma7_C2 G u v a h_two_connected h_distinct
          h_neighborhood hparents
      · exact bklpsLemma7Proof1 G u v h_two_connected h_distinct
          h_neighborhood h_delete_two_connected h_delete_noncomplete hdom hC1 hC2

end

end BKLPS.External
