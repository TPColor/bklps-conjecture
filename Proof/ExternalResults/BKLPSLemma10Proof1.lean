import Proof.ExternalResults.BKLPSLemma7GoodsLowerBounds
import Proof.ExternalResults.BlockStructure

/-! The proof content of BKLPS Lemma 10. -/

namespace BKLPS.External

open SimpleGraph

noncomputable section

universe u

/-- A single pair contribution is one of the nonnegative summands in the
contribution of its first endpoint. -/
private theorem pairGap_le_vertexContribution
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (a x : V) :
    pairGap G a x ≤ vertexContribution G a := by
  classical
  unfold vertexContribution
  have hx : x ∈ (Finset.univ : Finset V) := Finset.mem_univ _
  rw [← Finset.sum_erase_add _ _ hx]
  have hrest : 0 ≤ ∑ y ∈ (Finset.univ.erase x), pairGap G a y :=
    Finset.sum_nonneg fun y _ => pairGap_nonneg G hconn a y
  omega

/-- Two distinct pair contributions can be extracted simultaneously from
the vertex contribution. -/
private theorem pairGap_add_pairGap_le_vertexContribution
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (a x y : V) (hxy : x ≠ y) :
    pairGap G a x + pairGap G a y ≤ vertexContribution G a := by
  classical
  unfold vertexContribution
  have hx : x ∈ (Finset.univ : Finset V) := Finset.mem_univ _
  rw [← Finset.sum_erase_add _ _ hx]
  have hy : y ∈ (Finset.univ.erase x : Finset V) := by simp [hxy.symm]
  rw [← Finset.sum_erase_add _ _ hy]
  have hrest : 0 ≤ ∑ z ∈ (Finset.univ.erase x).erase y,
      pairGap G a z :=
    Finset.sum_nonneg fun z _ => pairGap_nonneg G hconn a z
  omega

/-- Three distinct summands can likewise be extracted from a vertex
contribution. -/
private theorem three_pairGaps_le_vertexContribution
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (a x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    pairGap G a x + pairGap G a y + pairGap G a z ≤
      vertexContribution G a := by
  classical
  unfold vertexContribution
  have hx : x ∈ (Finset.univ : Finset V) := Finset.mem_univ _
  rw [← Finset.sum_erase_add _ _ hx]
  have hy : y ∈ (Finset.univ.erase x : Finset V) := by simp [hxy.symm]
  rw [← Finset.sum_erase_add _ _ hy]
  have hz : z ∈ ((Finset.univ.erase x).erase y : Finset V) := by
    simp [hxz.symm, hyz.symm]
  rw [← Finset.sum_erase_add _ _ hz]
  have hrest : 0 ≤ ∑ q ∈ ((Finset.univ.erase x).erase y).erase z,
      pairGap G a q :=
    Finset.sum_nonneg fun q _ => pairGap_nonneg G hconn a q
  omega

/-- Four distinct summands can be extracted simultaneously. -/
private theorem four_pairGaps_le_vertexContribution
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (a x y z w : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    pairGap G a x + pairGap G a y + pairGap G a z + pairGap G a w ≤
      vertexContribution G a := by
  classical
  unfold vertexContribution
  have hx : x ∈ (Finset.univ : Finset V) := Finset.mem_univ _
  rw [← Finset.sum_erase_add _ _ hx]
  have hy : y ∈ (Finset.univ.erase x : Finset V) := by simp [hxy.symm]
  rw [← Finset.sum_erase_add _ _ hy]
  have hz : z ∈ ((Finset.univ.erase x).erase y : Finset V) := by
    simp [hxz.symm, hyz.symm]
  rw [← Finset.sum_erase_add _ _ hz]
  have hw : w ∈ (((Finset.univ.erase x).erase y).erase z : Finset V) := by
    simp [hxw.symm, hyw.symm, hzw.symm]
  rw [← Finset.sum_erase_add _ _ hw]
  have hrest : 0 ≤ ∑ q ∈ (((Finset.univ.erase x).erase y).erase z).erase w,
      pairGap G a q :=
    Finset.sum_nonneg fun q _ => pairGap_nonneg G hconn a q
  omega

/-- Claim P1 of BKLPS Lemma 10.  Under the contradictory assumption
`c(a) ≤ 3`, at most one vertex has two neighbors in its preceding BFS
layer, and that vertex has exactly two such neighbors. -/
private theorem bklpsLemma10_P1
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (a : V)
    (hsmall : vertexContribution G a ≤ (3 : ℤ)) :
    (∀ x : V, 2 ≤ (lowerNeighbors G a x).card →
      (lowerNeighbors G a x).card = 2) ∧
    ∀ x y : V, 2 ≤ (lowerNeighbors G a x).card →
      2 ≤ (lowerNeighbors G a y).card → x = y := by
  constructor
  · intro x hx
    have hpair := pairGap_ge_two_mul_lowerNeighbors_sub_two G hconn a x
    have hterm := pairGap_le_vertexContribution G hconn a x
    omega
  · intro x y hx hy
    by_contra hxy
    have hpairx := pairGap_ge_two_mul_lowerNeighbors_sub_two G hconn a x
    have hpairy := pairGap_ge_two_mul_lowerNeighbors_sub_two G hconn a y
    have hsum := pairGap_add_pairGap_le_vertexContribution G hconn a x y hxy
    omega

/-- The local estimate behind property P2.  Adjacent vertices in one BFS
layer with distinct predecessors each contribute at least one: a missing
cross edge is BKLPS condition C3, while a present cross edge gives two
predecessors and hence the stronger C2 estimate. -/
private theorem bklpsLemma10_P2_pair
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (a x y px py : V)
    (hxy : G.Adj x y) (hlevel : G.dist a x = G.dist a y)
    (hpx : px ∈ lowerNeighbors G a x)
    (hpy : py ∈ lowerNeighbors G a y) (hparents : px ≠ py) :
    pairGap G a x ≥ 1 ∧ pairGap G a y ≥ 1 := by
  have hpxFacts : G.Adj x px ∧ G.dist a px < G.dist a x := by
    simpa [lowerNeighbors, openNeighborhood] using hpx
  have hpyFacts : G.Adj y py ∧ G.dist a py < G.dist a y := by
    simpa [lowerNeighbors, openNeighborhood] using hpy
  constructor
  · by_cases hcross : G.Adj py x
    · have hpyx : py ∈ lowerNeighbors G a x := by
        simp [lowerNeighbors, openNeighborhood, hcross.symm, hlevel, hpyFacts.2]
      have htwo : 2 ≤ (lowerNeighbors G a x).card := by
        have hone : 1 < (lowerNeighbors G a x).card :=
          Finset.one_lt_card.mpr ⟨px, hpx, py, hpyx, hparents⟩
        omega
      have hbound := pairGap_ge_two_mul_lowerNeighbors_sub_two G hconn a x
      omega
    · exact pairGap_ge_one_of_horizontalEdge G hconn a y x py hxy.symm
        hlevel.symm hpyFacts.1 hpyFacts.2 hcross
  · by_cases hcross : G.Adj px y
    · have hpxy : px ∈ lowerNeighbors G a y := by
        simp [lowerNeighbors, openNeighborhood, hcross.symm, ← hlevel, hpxFacts.2]
      have htwo : 2 ≤ (lowerNeighbors G a y).card := by
        have hone : 1 < (lowerNeighbors G a y).card :=
          Finset.one_lt_card.mpr ⟨px, hpxy, py, hpy, hparents⟩
        omega
      have hbound := pairGap_ge_two_mul_lowerNeighbors_sub_two G hconn a y
      omega
    · exact pairGap_ge_one_of_horizontalEdge G hconn a x y px hxy
        hlevel hpxFacts.1 hpxFacts.2 hcross

/-- Two different horizontal neighbors, each with a predecessor not joined
to the common vertex, give two different good edges outside every geodesic
to that common vertex. -/
private theorem pairGap_ge_two_of_two_horizontalEdges
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (a x y z py pz : V)
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : y ≠ z)
    (hlevelY : G.dist a x = G.dist a y)
    (hlevelZ : G.dist a x = G.dist a z)
    (hypy : G.Adj y py) (hpyLower : G.dist a py < G.dist a y)
    (hzpz : G.Adj z pz) (hpzLower : G.dist a pz < G.dist a z)
    (hnpyx : ¬G.Adj py x) (hnpzx : ¬G.Adj pz x) :
    pairGap G a x ≥ 2 := by
  classical
  have hgoodY : IsGoodEdgeFor G a x s(y, py) := by
    change G.Adj y py ∧
      ((G.dist a y < G.dist a py ∧ G.dist x py < G.dist x y) ∨
       (G.dist a py < G.dist a y ∧ G.dist x y < G.dist x py))
    refine ⟨hypy, Or.inr ⟨hpyLower, ?_⟩⟩
    rw [dist_eq_one_iff_adj.mpr hxy]
    exact hconn.one_lt_dist_of_ne_of_not_adj
      (by intro h; subst py; omega) (fun h => hnpyx h.symm)
  have hgoodZ : IsGoodEdgeFor G a x s(z, pz) := by
    change G.Adj z pz ∧
      ((G.dist a z < G.dist a pz ∧ G.dist x pz < G.dist x z) ∨
       (G.dist a pz < G.dist a z ∧ G.dist x z < G.dist x pz))
    refine ⟨hzpz, Or.inr ⟨hpzLower, ?_⟩⟩
    rw [dist_eq_one_iff_adj.mpr hxz]
    exact hconn.one_lt_dist_of_ne_of_not_adj
      (by intro h; subst pz; omega) (fun h => hnpzx h.symm)
  have hedgeNe : s(y, py) ≠ s(z, pz) := by
    intro h
    rcases Sym2.eq_iff.mp h with hsame | hswap
    · exact hyz hsame.1
    · have hlevels : G.dist a y = G.dist a z := by omega
      rw [hswap.2] at hpyLower
      omega
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist a x
  have extra (q r : V) (hxq : G.Adj x q)
      (hlevel : G.dist a x = G.dist a q)
      (hqr : G.Adj q r) (hrLower : G.dist a r < G.dist a q) :
      s(q, r) ∉ p.edges := by
    intro he
    have hqSupp : q ∈ p.support := p.fst_mem_support_of_mem_edges he
    have hadd := geodesic_dist_add_of_mem_support p hp hqSupp
    rw [dist_eq_one_iff_adj.mpr hxq.symm] at hadd
    omega
  exact pairGap_ge_two_of_two_extra_goodEdges G hconn a x p hp
    s(y, py) s(z, pz) hedgeNe hgoodY hgoodZ
      (extra y py hxy hlevelY hypy hpyLower)
      (extra z pz hxz hlevelZ hzpz hpzLower)

/-- BKLPS' observation immediately after P2: a P1 vertex and a P2 edge
cannot coexist when `c(a) ≤ 3`.  P1 contributes at least two and the two
ends of P2 contribute at least one each. -/
private theorem bklpsLemma10_no_P1_and_P2
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (a : V)
    (hsmall : vertexContribution G a ≤ (3 : ℤ))
    (p x y px py : V)
    (hp : 2 ≤ (lowerNeighbors G a p).card)
    (hxy : G.Adj x y) (hlevel : G.dist a x = G.dist a y)
    (hxone : (lowerNeighbors G a x).card = 1)
    (hyone : (lowerNeighbors G a y).card = 1)
    (hpx : px ∈ lowerNeighbors G a x)
    (hpy : py ∈ lowerNeighbors G a y) (hparents : px ≠ py) : False := by
  have hpxy : x ≠ y := hxy.ne
  have hpnx : p ≠ x := by
    intro h
    subst p
    omega
  have hpny : p ≠ y := by
    intro h
    subst p
    omega
  have hpGap := pairGap_ge_two_mul_lowerNeighbors_sub_two G hconn a p
  have hP2 := bklpsLemma10_P2_pair G hconn a x y px py hxy hlevel
    hpx hpy hparents
  have hsum := three_pairGaps_le_vertexContribution G hconn a p x y
    hpnx hpny hpxy
  omega

/-- Two distinct P2 edges cannot share an endpoint.  Their two horizontal
detours give contribution two at the shared endpoint, while the other two
endpoints contribute one each. -/
private theorem bklpsLemma10_no_overlapping_P2
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (a : V)
    (hsmall : vertexContribution G a ≤ (3 : ℤ))
    (x y z px py pz : V) (hyz : y ≠ z)
    (hxy : G.Adj x y) (hxz : G.Adj x z)
    (hlevelY : G.dist a x = G.dist a y)
    (hlevelZ : G.dist a x = G.dist a z)
    (hxone : (lowerNeighbors G a x).card = 1)
    (hyone : (lowerNeighbors G a y).card = 1)
    (hzone : (lowerNeighbors G a z).card = 1)
    (hpx : px ∈ lowerNeighbors G a x)
    (hpy : py ∈ lowerNeighbors G a y) (hpxpy : px ≠ py)
    (hpz : pz ∈ lowerNeighbors G a z) (hpxpz : px ≠ pz) : False := by
  have hpxFacts : G.Adj x px ∧ G.dist a px < G.dist a x := by
    simpa [lowerNeighbors, openNeighborhood] using hpx
  have hpyFacts : G.Adj y py ∧ G.dist a py < G.dist a y := by
    simpa [lowerNeighbors, openNeighborhood] using hpy
  have hpzFacts : G.Adj z pz ∧ G.dist a pz < G.dist a z := by
    simpa [lowerNeighbors, openNeighborhood] using hpz
  have hnpyx : ¬G.Adj py x := by
    intro h
    have hpyLower : py ∈ lowerNeighbors G a x := by
      simp [lowerNeighbors, openNeighborhood, h.symm, hlevelY, hpyFacts.2]
    have htwo : 2 ≤ (lowerNeighbors G a x).card := by
      have hone : 1 < (lowerNeighbors G a x).card :=
        Finset.one_lt_card.mpr ⟨px, hpx, py, hpyLower, hpxpy⟩
      omega
    omega
  have hnpzx : ¬G.Adj pz x := by
    intro h
    have hpzLower' : pz ∈ lowerNeighbors G a x := by
      simp [lowerNeighbors, openNeighborhood, h.symm, hlevelZ, hpzFacts.2]
    have htwo : 2 ≤ (lowerNeighbors G a x).card := by
      have hone : 1 < (lowerNeighbors G a x).card :=
        Finset.one_lt_card.mpr ⟨px, hpx, pz, hpzLower', hpxpz⟩
      omega
    omega
  have hnpxy : ¬G.Adj px y := by
    intro h
    have hpxLower : px ∈ lowerNeighbors G a y := by
      simp [lowerNeighbors, openNeighborhood, h.symm, ← hlevelY, hpxFacts.2]
    have hone : 1 < (lowerNeighbors G a y).card :=
      Finset.one_lt_card.mpr ⟨px, hpxLower, py, hpy, hpxpy⟩
    omega
  have hnpxz : ¬G.Adj px z := by
    intro h
    have hpxLower : px ∈ lowerNeighbors G a z := by
      simp [lowerNeighbors, openNeighborhood, h.symm, ← hlevelZ, hpxFacts.2]
    have hone : 1 < (lowerNeighbors G a z).card :=
      Finset.one_lt_card.mpr ⟨px, hpxLower, pz, hpz, hpxpz⟩
    omega
  have hxGap := pairGap_ge_two_of_two_horizontalEdges G hconn a x y z py pz
    hxy hxz hyz hlevelY hlevelZ hpyFacts.1 hpyFacts.2 hpzFacts.1
      hpzFacts.2 hnpyx hnpzx
  have hyGap := pairGap_ge_one_of_horizontalEdge G hconn a x y px hxy
    hlevelY hpxFacts.1 hpxFacts.2 hnpxy
  have hzGap := pairGap_ge_one_of_horizontalEdge G hconn a x z px hxz
    hlevelZ hpxFacts.1 hpxFacts.2 hnpxz
  have hxyNe : x ≠ y := hxy.ne
  have hxzNe : x ≠ z := hxz.ne
  have hsum := three_pairGaps_le_vertexContribution G hconn a x y z
    hxyNe hxzNe hyz
  omega

/-- Two vertex-disjoint P2 edges are also impossible: their four endpoints
each contribute at least one. -/
private theorem bklpsLemma10_no_disjoint_P2
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (a : V)
    (hsmall : vertexContribution G a ≤ (3 : ℤ))
    (x y z w px py pz pw : V)
    (hxy : G.Adj x y) (hzw : G.Adj z w)
    (hlevelXY : G.dist a x = G.dist a y)
    (hlevelZW : G.dist a z = G.dist a w)
    (hpx : px ∈ lowerNeighbors G a x)
    (hpy : py ∈ lowerNeighbors G a y) (hpxpy : px ≠ py)
    (hpz : pz ∈ lowerNeighbors G a z)
    (hpw : pw ∈ lowerNeighbors G a w) (hpzpw : pz ≠ pw)
    (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) : False := by
  have hfirst := bklpsLemma10_P2_pair G hconn a x y px py hxy hlevelXY
    hpx hpy hpxpy
  have hsecond := bklpsLemma10_P2_pair G hconn a z w pz pw hzw hlevelZW
    hpz hpw hpzpw
  have hsum := four_pairGaps_le_vertexContribution G hconn a x y z w
    hxy.ne hxz hxw hyz hyw hzw.ne
  omega

/-- Claim P2 of BKLPS Lemma 10: under `c(a) ≤ 3`, two P2 edges must be
the same unordered pair.  The proof separates the four possible shared
endpoints from the vertex-disjoint case. -/
private theorem bklpsLemma10_P2_unique
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (a : V)
    (hsmall : vertexContribution G a ≤ (3 : ℤ))
    (x y z w px py pz pw : V)
    (hxy : G.Adj x y) (hzw : G.Adj z w)
    (hlevelXY : G.dist a x = G.dist a y)
    (hlevelZW : G.dist a z = G.dist a w)
    (hxone : (lowerNeighbors G a x).card = 1)
    (hyone : (lowerNeighbors G a y).card = 1)
    (hzone : (lowerNeighbors G a z).card = 1)
    (hwone : (lowerNeighbors G a w).card = 1)
    (hpx : px ∈ lowerNeighbors G a x)
    (hpy : py ∈ lowerNeighbors G a y) (hpxpy : px ≠ py)
    (hpz : pz ∈ lowerNeighbors G a z)
    (hpw : pw ∈ lowerNeighbors G a w) (hpzpw : pz ≠ pw) :
    s(x, y) = s(z, w) := by
  by_contra hpairs
  by_cases hxz : x = z
  · subst z
    have hyw : y ≠ w := by
      intro h; subst w; exact hpairs rfl
    have hparent : px = pz :=
      (Finset.card_le_one.mp (by omega : (lowerNeighbors G a x).card ≤ 1))
        px hpx pz hpz
    subst pz
    exact bklpsLemma10_no_overlapping_P2 G hconn a hsmall
      x y w px py pw hyw hxy hzw hlevelXY hlevelZW hxone hyone hwone
        hpx hpy hpxpy hpw hpzpw
  · by_cases hxw : x = w
    · subst w
      have hyz : y ≠ z := by
        intro h; subst z; exact hpairs Sym2.eq_swap
      have hparent : px = pw :=
        (Finset.card_le_one.mp (by omega : (lowerNeighbors G a x).card ≤ 1))
          px hpx pw hpw
      subst pw
      exact bklpsLemma10_no_overlapping_P2 G hconn a hsmall
        x y z px py pz hyz hxy hzw.symm hlevelXY hlevelZW.symm
          hxone hyone hzone hpx hpy hpxpy hpz hpzpw.symm
    · by_cases hyz : y = z
      · subst z
        have hxw' : x ≠ w := by
          intro h; subst w; exact hpairs Sym2.eq_swap
        have hparent : py = pz :=
          (Finset.card_le_one.mp (by omega : (lowerNeighbors G a y).card ≤ 1))
            py hpy pz hpz
        subst pz
        exact bklpsLemma10_no_overlapping_P2 G hconn a hsmall
          y x w py px pw hxw' hxy.symm hzw hlevelXY.symm hlevelZW
            hyone hxone hwone hpy hpx hpxpy.symm hpw hpzpw
      · by_cases hyw : y = w
        · subst w
          have hxz' : x ≠ z := by
            intro h; subst z; exact hpairs rfl
          have hparent : py = pw :=
            (Finset.card_le_one.mp (by omega : (lowerNeighbors G a y).card ≤ 1))
              py hpy pw hpw
          subst pw
          exact bklpsLemma10_no_overlapping_P2 G hconn a hsmall
            y x z py px pz hxz' hxy.symm hzw.symm hlevelXY.symm
              hlevelZW.symm hyone hxone hzone hpy hpx hpxpy.symm hpz
                hpzpw.symm
        · exact False.elim (bklpsLemma10_no_disjoint_P2 G hconn a hsmall
            x y z w px py pz pw hxy hzw hlevelXY hlevelZW hpx hpy hpxpy
              hpz hpw hpzpw hxz hxw hyz hyw)

/-- Every non-root vertex has a predecessor in the preceding BFS layer. -/
private theorem exists_lower_neighbor_bfs
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (a x : V) (hxa : x ≠ a) :
    ∃ y : V, y ∈ lowerNeighbors G a x := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x a
  cases p with
  | nil => exact False.elim (hxa rfl)
  | @cons _ y _ hxy q =>
      refine ⟨y, ?_⟩
      have hle := G.dist_le q
      have hcommx : G.dist x a = G.dist a x := dist_comm
      have hcommy : G.dist y a = G.dist a y := dist_comm
      rw [hcommx] at hp
      rw [hcommy] at hle
      simp only [Walk.length_cons] at hp
      apply Finset.mem_filter.mpr
      refine ⟨by simpa [openNeighborhood] using hxy, ?_⟩
      have hlt : G.dist y a < G.dist x a := by omega
      simpa [dist_comm] using hlt

/-- The P2 configuration used in the paper, with the two predecessors
included as witnesses. -/
private def IsP2Configuration
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a x y px py : V) : Prop :=
  G.Adj x y ∧ G.dist a x = G.dist a y ∧
  (lowerNeighbors G a x).card = 1 ∧
  (lowerNeighbors G a y).card = 1 ∧
  px ∈ lowerNeighbors G a x ∧ py ∈ lowerNeighbors G a y ∧ px ≠ py

/-- BKLPS Claim `noPs`, in the local form needed below.  If `x` has no
P1, no incident P2, and no same-level neighbor with P1, then failure to
have a neighbor in the next layer forces `N[x] ⊆ N[parent(x)]`. -/
private theorem bklpsLemma10_noPs
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G)
    (a x : V) (hxa : x ≠ a)
    (hnoP1x : ¬2 ≤ (lowerNeighbors G a x).card)
    (hnoP1same : ∀ y : V, G.Adj x y → G.dist a x = G.dist a y →
      ¬2 ≤ (lowerNeighbors G a y).card)
    (hnoP2 : ∀ y px py : V, ¬IsP2Configuration G a x y px py)
    (h_no_containment : ∀ u v : V, u ≠ v →
      ¬(closedNeighborhood G u ⊆ closedNeighborhood G v)) :
    ∃ y : V, G.Adj x y ∧ G.dist a y = G.dist a x + 1 := by
  classical
  by_contra hupper
  push_neg at hupper
  have hxpos : 0 < G.dist a x := by
    by_contra hzero
    have hz : G.dist a x = 0 := by omega
    exact hxa ((htwo.2.1.dist_eq_zero_iff (u := a) (v := x)).mp hz).symm
  obtain ⟨v, hv⟩ := exists_lower_neighbor_bfs G htwo.2.1 a x hxa
  have hvFacts : G.Adj x v ∧ G.dist a v < G.dist a x := by
    simpa [lowerNeighbors, openNeighborhood] using hv
  have hlowerOne : (lowerNeighbors G a x).card = 1 := by
    have hpos : 0 < (lowerNeighbors G a x).card := Finset.card_pos.mpr ⟨v, hv⟩
    omega
  obtain ⟨r, s, hrs, hxr, hxs⟩ := exists_two_neighbors_of_twoConnected G htwo x
  let w := if r = v then s else r
  have hxw : G.Adj x w := by
    by_cases hrv : r = v
    · simpa [w, hrv] using hxs
    · simpa [w, hrv] using hxr
  have hwv : w ≠ v := by
    by_cases hrv : r = v
    · simpa [w, hrv] using hrs.symm
    · simpa [w, hrv]
  have hwNotLower : ¬G.dist a w < G.dist a x := by
    intro hw
    have hwmem : w ∈ lowerNeighbors G a x := by
      simp [lowerNeighbors, openNeighborhood, hxw, hw]
    exact hwv ((Finset.card_le_one.mp (by omega :
      (lowerNeighbors G a x).card ≤ 1)) w hwmem v hv)
  have hlevelw : G.dist a x = G.dist a w := by
    rcases hxw.diff_dist_adj (u := a) with hsame | hup | hdown
    · exact hsame.symm
    · exact False.elim (hupper w hxw hup)
    · omega
  have hN : closedNeighborhood G x ⊆ closedNeighborhood G v := by
    intro t ht
    have ht' : t = x ∨ G.Adj x t := by
      simpa [closedNeighborhood, openNeighborhood] using ht
    rcases ht' with rfl | hxt
    · simp [closedNeighborhood, openNeighborhood, hvFacts.1.symm]
    · rcases hxt.diff_dist_adj (u := a) with hsame | hup | hdown
      · have htneA : t ≠ a := by
          intro h; subst t
          simp only [dist_self] at hsame
          exact hxa
            ((htwo.2.1.dist_eq_zero_iff (u := a) (v := x)).mp hsame.symm).symm
        obtain ⟨q, hq⟩ := exists_lower_neighbor_bfs G htwo.2.1 a t htneA
        have hqFacts : G.Adj t q ∧ G.dist a q < G.dist a t := by
          simpa [lowerNeighbors, openNeighborhood] using hq
        by_cases hvt : G.Adj v t
        · simp [closedNeighborhood, openNeighborhood, hvt]
        · have htNoP1 := hnoP1same t hxt hsame.symm
          have htOne : (lowerNeighbors G a t).card = 1 := by
            have : 0 < (lowerNeighbors G a t).card := Finset.card_pos.mpr ⟨q, hq⟩
            omega
          have hqv : q ≠ v := by
            intro h; subst q; exact hvt hqFacts.1.symm
          exact False.elim (hnoP2 t v q ⟨hxt, hsame.symm, hlowerOne,
            htOne, hv, hq, hqv.symm⟩)
      · exact False.elim (hupper t hxt hup)
      · have htmem : t ∈ lowerNeighbors G a x := by
          simp [lowerNeighbors, openNeighborhood, hxt]
          omega
        have htv : t = v :=
          (Finset.card_le_one.mp (by omega :
            (lowerNeighbors G a x).card ≤ 1)) t htmem v hv
        simp [closedNeighborhood, htv]
  exact h_no_containment x v hvFacts.1.ne hN

/-- The vertical fork at a maximal P1 vertex supplies an extra good edge
for the pair formed with the other predecessor. -/
private theorem pairGap_ge_one_of_parent_fork
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (a x y z : V) (hxy : G.Adj x y) (hxz : G.Adj x z)
    (hyz : y ≠ z)
    (hlevels : G.dist a y = G.dist a z)
    (hup : G.dist a x = G.dist a y + 1) (hnyz : ¬G.Adj y z) :
    pairGap G a z ≥ 1 := by
  classical
  have hfar : 1 < G.dist z y :=
    hconn.one_lt_dist_of_ne_of_not_adj hyz.symm (fun h => hnyz h.symm)
  have hgood : IsGoodEdgeFor G a z s(y, x) := by
    change G.Adj y x ∧
      ((G.dist a y < G.dist a x ∧ G.dist z x < G.dist z y) ∨
       (G.dist a x < G.dist a y ∧ G.dist z y < G.dist z x))
    refine ⟨hxy.symm, Or.inl ⟨by omega, ?_⟩⟩
    rw [dist_eq_one_iff_adj.mpr hxz.symm]
    exact hfar
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist a z
  have hextra : s(y, x) ∉ p.edges := by
    intro he
    have hySupp : y ∈ p.support := p.fst_mem_support_of_mem_edges he
    have hadd := geodesic_dist_add_of_mem_support p hp hySupp
    have hzero : G.dist y z = 0 := by omega
    exact hyz ((hconn.dist_eq_zero_iff).mp hzero)
  exact pairGap_ge_one_of_extra_goodEdge G hconn a z p hp s(y, x) hgood hextra

/-- Two distinct parents of a maximal-layer vertex, both missed by a
same-layer vertex, give two extra good edges for that vertex. -/
private theorem pairGap_ge_two_of_double_parent_fork
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (a x t y z : V) (hxt : G.Adj x t)
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : y ≠ z)
    (hlevel : G.dist a x = G.dist a t)
    (hyLower : G.dist a y < G.dist a x)
    (hzLower : G.dist a z < G.dist a x)
    (hnyt : ¬G.Adj y t) (hnzt : ¬G.Adj z t) :
    pairGap G a t ≥ 2 := by
  classical
  have good (q : V) (hxq : G.Adj x q) (hqLower : G.dist a q < G.dist a x)
      (hnqt : ¬G.Adj q t) : IsGoodEdgeFor G a t s(q, x) := by
    change G.Adj q x ∧
      ((G.dist a q < G.dist a x ∧ G.dist t x < G.dist t q) ∨
       (G.dist a x < G.dist a q ∧ G.dist t q < G.dist t x))
    refine ⟨hxq.symm, Or.inl ⟨hqLower, ?_⟩⟩
    rw [dist_eq_one_iff_adj.mpr hxt.symm]
    exact hconn.one_lt_dist_of_ne_of_not_adj
      (by intro h; subst q; omega) (fun h => hnqt h.symm)
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist a t
  have extra (q : V) (hxq : G.Adj x q) (hqLower : G.dist a q < G.dist a x) :
      s(q, x) ∉ p.edges := by
    intro he
    have hxSupp : x ∈ p.support := p.snd_mem_support_of_mem_edges he
    have hadd := geodesic_dist_add_of_mem_support p hp hxSupp
    rw [dist_eq_one_iff_adj.mpr hxt] at hadd
    omega
  have hedge : s(y, x) ≠ s(z, x) := by
    intro h
    rcases Sym2.eq_iff.mp h with hsame | hswap
    · exact hyz hsame.1
    · exact hxy.ne hswap.1.symm
  exact pairGap_ge_two_of_two_extra_goodEdges G hconn a t p hp
    s(y, x) s(z, x) hedge (good y hxy hyLower hnyt)
      (good z hxz hzLower hnzt) (extra y hxy hyLower) (extra z hxz hzLower)

/-- In the terminal P2 configuration, two different predecessors in the
next lower layer provide two extra good edges for the opposite endpoint. -/
private theorem pairGap_ge_two_terminal_P2
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (a x t y w z r : V)
    (hxt : G.Adj x t) (hlevel : G.dist a x = G.dist a t)
    (hxone : (lowerNeighbors G a x).card = 1)
    (htone : (lowerNeighbors G a t).card = 1)
    (hy : y ∈ lowerNeighbors G a x) (hw : w ∈ lowerNeighbors G a t)
    (hyw : y ≠ w)
    (hyone : (lowerNeighbors G a y).card = 1)
    (hwone : (lowerNeighbors G a w).card = 1)
    (hz : z ∈ lowerNeighbors G a y) (hr : r ∈ lowerNeighbors G a w)
    (hzr : z ≠ r) : pairGap G a t ≥ 2 := by
  classical
  have hyF : G.Adj x y ∧ G.dist a y < G.dist a x := by
    simpa [lowerNeighbors, openNeighborhood] using hy
  have hwF : G.Adj t w ∧ G.dist a w < G.dist a t := by
    simpa [lowerNeighbors, openNeighborhood] using hw
  have hzF : G.Adj y z ∧ G.dist a z < G.dist a y := by
    simpa [lowerNeighbors, openNeighborhood] using hz
  have hrF : G.Adj w r ∧ G.dist a r < G.dist a w := by
    simpa [lowerNeighbors, openNeighborhood] using hr
  have hupY : G.dist a x = G.dist a y + 1 := by
    have hd := hyF.1.diff_dist_adj (u := a)
    omega
  have hupW : G.dist a t = G.dist a w + 1 := by
    have hd := hwF.1.diff_dist_adj (u := a)
    omega
  have hupZ : G.dist a y = G.dist a z + 1 := by
    have hd := hzF.1.diff_dist_adj (u := a)
    omega
  have hupR : G.dist a w = G.dist a r + 1 := by
    have hd := hrF.1.diff_dist_adj (u := a)
    omega
  have hyt : ¬G.Adj y t := by
    intro h
    have hymem : y ∈ lowerNeighbors G a t := by
      simp [lowerNeighbors, openNeighborhood, h.symm]
      omega
    exact hyw ((Finset.card_le_one.mp (by omega :
      (lowerNeighbors G a t).card ≤ 1)) y hymem w hw)
  have hty : G.dist t y = 2 := by
    have hgt := hconn.one_lt_dist_of_ne_of_not_adj
      (by intro h; subst y; omega) (fun h => hyt h.symm)
    have hle := hconn.dist_triangle (u := t) (v := x) (w := y)
    rw [dist_eq_one_iff_adj.mpr hxt.symm,
      dist_eq_one_iff_adj.mpr hyF.1] at hle
    omega
  have htz : 2 < G.dist t z := by
    by_contra hn
    have hlower : 2 ≤ G.dist t z := by
      have htri := hconn.dist_triangle (u := a) (v := z) (w := t)
      have hcomm : G.dist z t = G.dist t z := dist_comm
      omega
    have heq : G.dist t z = 2 := by omega
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist t z
    have hpTwo : p.length = 2 := by omega
    cases p with
    | nil => simp at hpTwo
    | @cons _ m _ htm q =>
        have hqOne : q.length = 1 := by simpa [Walk.length_cons] using hpTwo
        have hmz : G.Adj m z := Walk.adj_of_length_eq_one hqOne
        have hmLevel : G.dist a m = G.dist a w := by
          have hd₁ := htm.diff_dist_adj (u := a)
          have hd₂ := hmz.diff_dist_adj (u := a)
          omega
        have hmmem : m ∈ lowerNeighbors G a t := by
          apply Finset.mem_filter.mpr
          refine ⟨by simpa [openNeighborhood] using htm, ?_⟩
          omega
        have hmw : m = w :=
          (Finset.card_le_one.mp (by omega :
            (lowerNeighbors G a t).card ≤ 1)) m hmmem w hw
        have hzmem : z ∈ lowerNeighbors G a w := by
          subst m
          apply Finset.mem_filter.mpr
          refine ⟨by simpa [openNeighborhood] using hmz, ?_⟩
          omega
        have hzr' : z = r :=
          (Finset.card_le_one.mp (by omega :
            (lowerNeighbors G a w).card ≤ 1)) z hzmem r hr
        exact hzr hzr'
  have hgood₁ : IsGoodEdgeFor G a t s(y, x) := by
    change G.Adj y x ∧
      ((G.dist a y < G.dist a x ∧ G.dist t x < G.dist t y) ∨
       (G.dist a x < G.dist a y ∧ G.dist t y < G.dist t x))
    refine ⟨hyF.1.symm, Or.inl ⟨hyF.2, ?_⟩⟩
    rw [dist_eq_one_iff_adj.mpr hxt.symm, hty]
    omega
  have hgood₂ : IsGoodEdgeFor G a t s(z, y) := by
    change G.Adj z y ∧
      ((G.dist a z < G.dist a y ∧ G.dist t y < G.dist t z) ∨
       (G.dist a y < G.dist a z ∧ G.dist t z < G.dist t y))
    exact ⟨hzF.1.symm, Or.inl ⟨hzF.2, by omega⟩⟩
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist a t
  have hextra₁ : s(y, x) ∉ p.edges := by
    intro he
    have hxSupp : x ∈ p.support := p.snd_mem_support_of_mem_edges he
    have hadd := geodesic_dist_add_of_mem_support p hp hxSupp
    rw [dist_eq_one_iff_adj.mpr hxt] at hadd
    omega
  have hextra₂ : s(z, y) ∉ p.edges := by
    intro he
    have hySupp : y ∈ p.support := p.snd_mem_support_of_mem_edges he
    have hadd := geodesic_dist_add_of_mem_support p hp hySupp
    have hcomm : G.dist y t = G.dist t y := dist_comm
    omega
  have hedge : s(y, x) ≠ s(z, y) := by
    intro he
    rcases Sym2.eq_iff.mp he with hs | hs
    · exact hzF.1.ne hs.1
    · have hxz : x ≠ z := by
        intro hxz
        have hd := congrArg (G.dist a) hxz
        omega
      exact hxz hs.2
  exact pairGap_ge_two_of_two_extra_goodEdges G hconn a t p hp
    s(y, x) s(z, y) hedge hgood₁ hgood₂ hextra₁ hextra₂

/-- The terminal P1 configuration.  If `x` is the only vertex in its
maximal layer, its two predecessors are either adjacent (giving forbidden
closed-neighborhood containment) or nonadjacent (giving contributions
`2+1+1`). -/
private theorem bklpsLemma10_terminal_P1
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G) (a x : V)
    (hsmall : vertexContribution G a ≤ (3 : ℤ))
    (hxmax : ∀ t : V, G.dist a t ≤ G.dist a x)
    (hmaxOnly : ∀ t : V, G.dist a t = G.dist a x → t = x)
    (hxP1 : 2 ≤ (lowerNeighbors G a x).card)
    (hxExact : (lowerNeighbors G a x).card = 2)
    (h_no_containment : ∀ u v : V, u ≠ v →
      ¬(closedNeighborhood G u ⊆ closedNeighborhood G v)) : False := by
  classical
  obtain ⟨y, z, hyz, hparents⟩ := Finset.card_eq_two.mp hxExact
  have hy : y ∈ lowerNeighbors G a x := by simp [hparents]
  have hz : z ∈ lowerNeighbors G a x := by simp [hparents]
  have hyFacts : G.Adj x y ∧ G.dist a y < G.dist a x := by
    simpa [lowerNeighbors, openNeighborhood] using hy
  have hzFacts : G.Adj x z ∧ G.dist a z < G.dist a x := by
    simpa [lowerNeighbors, openNeighborhood] using hz
  have hlevels : G.dist a y = G.dist a z := by
    have hyDiff := hyFacts.1.diff_dist_adj (u := a)
    have hzDiff := hzFacts.1.diff_dist_adj (u := a)
    omega
  have hupY : G.dist a x = G.dist a y + 1 := by
    have := hyFacts.1.diff_dist_adj (u := a)
    omega
  by_cases hyzAdj : G.Adj y z
  · have hN : closedNeighborhood G x ⊆ closedNeighborhood G y := by
      intro t ht
      have ht' : t = x ∨ G.Adj x t := by
        simpa [closedNeighborhood, openNeighborhood] using ht
      rcases ht' with rfl | hxt
      · simp [closedNeighborhood, openNeighborhood, hyFacts.1.symm]
      · rcases hxt.diff_dist_adj (u := a) with hsame | hup | hdown
        · have htx : t = x := hmaxOnly t hsame
          subst t
          simp [closedNeighborhood, openNeighborhood, hyFacts.1.symm]
        · exact False.elim (by have := hxmax t; omega)
        · have htLower : t ∈ lowerNeighbors G a x := by
            simp [lowerNeighbors, openNeighborhood, hxt]
            have hxpos : 0 < G.dist a x := by omega
            omega
          have htCases : t = y ∨ t = z := by
            simpa [hparents] using htLower
          rcases htCases with rfl | rfl
          · simp [closedNeighborhood]
          · simp [closedNeighborhood, openNeighborhood, hyzAdj]
    exact h_no_containment x y hyFacts.1.ne hN
  · have hxGap := pairGap_ge_two_mul_lowerNeighbors_sub_two G htwo.2.1 a x
    have hyGap := pairGap_ge_one_of_parent_fork G htwo.2.1 a x z y
      hzFacts.1 hyFacts.1 hyz.symm hlevels.symm (by omega)
        (fun h => hyzAdj h.symm)
    have hzGap := pairGap_ge_one_of_parent_fork G htwo.2.1 a x y z
      hyFacts.1 hzFacts.1 hyz hlevels hupY hyzAdj
    have hxy : x ≠ y := hyFacts.1.ne
    have hxz : x ≠ z := hzFacts.1.ne
    have hsum := three_pairGaps_le_vertexContribution G htwo.2.1 a x y z
      hxy hxz hyz
    omega
/-- The combinatorial heart of BKLPS Lemma 10: its breadth-first-search
argument proves that every vertex contributes at least four.  The public
statement derives the global gap bound by BKLPS equation (3). -/
theorem bklpsLemma10Proof1
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_two_connected : IsTwoConnected G)
    (h_noncomplete : ¬IsomorphicToKn G)
    (h_not_C5 : ¬IsomorphicToCn G 5)
    (h_no_containment : ∀ u v : V, u ≠ v →
      ¬(closedNeighborhood G u ⊆ closedNeighborhood G v)) :
    ∀ u : V, vertexContribution G u ≥ (4 : ℤ) := by
  intro a
  by_contra h
  have hsmall : vertexContribution G a ≤ (3 : ℤ) := by omega
  have hP1 := bklpsLemma10_P1 G h_two_connected.2.1 a hsmall
  classical
  have hcardV := h_two_connected.1
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, _, hxmax⟩ := Finset.exists_max_image (Finset.univ : Finset V)
    (G.dist a) Finset.univ_nonempty
  have hxmax' (t : V) : G.dist a t ≤ G.dist a x := hxmax t (Finset.mem_univ _)
  obtain ⟨b, hba⟩ := exists_ne a
  have hxpos : 0 < G.dist a x := by
    have hbpos : 0 < G.dist a b := by
      have hb0 := h_two_connected.2.1.dist_eq_zero_iff (u := a) (v := b)
      have hnzero : G.dist a b ≠ 0 := by
        intro hz
        exact hba ((hb0.mp hz).symm)
      omega
    exact lt_of_lt_of_le hbpos (hxmax' b)
  have maxMarked (t : V) (htmax : G.dist a t = G.dist a x) :
      2 ≤ (lowerNeighbors G a t).card ∨
      (∃ y px py, IsP2Configuration G a t y px py) ∨
      (∃ p, 2 ≤ (lowerNeighbors G a p).card ∧ G.Adj t p ∧
        G.dist a t = G.dist a p) := by
    by_cases htP1 : 2 ≤ (lowerNeighbors G a t).card
    · exact Or.inl htP1
    · by_cases htP2 : ∃ y px py, IsP2Configuration G a t y px py
      · exact Or.inr (Or.inl htP2)
      · by_cases hsame : ∃ p, 2 ≤ (lowerNeighbors G a p).card ∧
          G.Adj t p ∧ G.dist a t = G.dist a p
        · exact Or.inr (Or.inr hsame)
        · have hta : t ≠ a := by
            intro hta
            subst t
            simp only [dist_self] at htmax
            omega
          have hu := bklpsLemma10_noPs G h_two_connected a t hta htP1
            (by
              intro y hty hlev hyP1
              exact hsame ⟨y, hyP1, hty, hlev⟩)
            (by
              intro y px py hcfg
              exact htP2 ⟨y, px, py, hcfg⟩)
            h_no_containment
          obtain ⟨y, _, hyLevel⟩ := hu
          have := hxmax' y
          omega
  by_cases hexP1 : ∃ p : V, 2 ≤ (lowerNeighbors G a p).card
  · obtain ⟨p, hpP1⟩ := hexP1
    have hpExact := hP1.1 p hpP1
    have noP2 : ∀ q y pq py, ¬IsP2Configuration G a q y pq py := by
      intro q y pq py hcfg
      rcases hcfg with ⟨hqy, hlev, hqone, hyone, hpq, hpy, hpqpy⟩
      exact bklpsLemma10_no_P1_and_P2 G h_two_connected.2.1 a hsmall
        p q y pq py hpP1 hqy hlev hqone hyone hpq hpy hpqpy
    have hpMax : G.dist a p = G.dist a x := by
      rcases maxMarked x rfl with hxP1 | hxP2 | ⟨q, hqP1, _, hxq⟩
      · exact (congrArg (G.dist a) (hP1.2 x p hxP1 hpP1)).symm
      · obtain ⟨y, px, py, hcfg⟩ := hxP2
        exact False.elim (noP2 x y px py hcfg)
      · have hqp : q = p := hP1.2 q p hqP1 hpP1
        simpa [hqp] using hxq.symm
    have hpMaxBound (t : V) : G.dist a t ≤ G.dist a p := by
      simpa [hpMax] using hxmax' t
    obtain ⟨y, z, hyz, hparents⟩ := Finset.card_eq_two.mp hpExact
    have hy : y ∈ lowerNeighbors G a p := by simp [hparents]
    have hz : z ∈ lowerNeighbors G a p := by simp [hparents]
    have hyF : G.Adj p y ∧ G.dist a y < G.dist a p := by
      simpa [lowerNeighbors, openNeighborhood] using hy
    have hzF : G.Adj p z ∧ G.dist a z < G.dist a p := by
      simpa [lowerNeighbors, openNeighborhood] using hz
    have hyzLevel : G.dist a y = G.dist a z := by
      have h₁ := hyF.1.diff_dist_adj (u := a)
      have h₂ := hzF.1.diff_dist_adj (u := a)
      omega
    have hupY : G.dist a p = G.dist a y + 1 := by
      have hdiff := hyF.1.diff_dist_adj (u := a)
      omega
    have hupZ : G.dist a p = G.dist a z + 1 := by
      have hdiff := hzF.1.diff_dist_adj (u := a)
      omega
    have hyzAdj : G.Adj y z := by
      by_contra hn
      have hpGap := pairGap_ge_two_mul_lowerNeighbors_sub_two G
        h_two_connected.2.1 a p
      have hyGap := pairGap_ge_one_of_parent_fork G h_two_connected.2.1
        a p z y hzF.1 hyF.1 hyz.symm hyzLevel.symm hupZ
          (fun h => hn h.symm)
      have hzGap := pairGap_ge_one_of_parent_fork G h_two_connected.2.1
        a p y z hyF.1 hzF.1 hyz hyzLevel hupY hn
      have hsum := three_pairGaps_le_vertexContribution G h_two_connected.2.1
        a p y z hyF.1.ne hzF.1.ne hyz
      omega
    have sameLevelWitness (q : V) (hpq : G.Adj p q) (hnYq : ¬G.Adj y q)
        (hqY : q ≠ y) : G.dist a q = G.dist a p := by
      rcases hpq.diff_dist_adj (u := a) with hsame | hup | hdown
      · exact hsame
      · have := hpMaxBound q; omega
      · have hqLower : q ∈ lowerNeighbors G a p := by
          simp [lowerNeighbors, openNeighborhood, hpq]
          omega
        have hcases : q = y ∨ q = z := by simpa [hparents] using hqLower
        rcases hcases with hqy | hqz
        · exact False.elim (hqY hqy)
        · subst q
          exact False.elim (hnYq hyzAdj)
    have hpOnly (t : V) (ht : G.dist a t = G.dist a p) : t = p := by
      rcases maxMarked t (ht.trans hpMax) with htP1 | htP2 |
          ⟨q, hqP1, htq, hlevel⟩
      · exact hP1.2 t p htP1 hpP1
      · obtain ⟨w, pt, pw, hcfg⟩ := htP2
        exact False.elim (noP2 t w pt pw hcfg)
      · have hqp : q = p := hP1.2 q p hqP1 hpP1
        subst q
        by_contra htp
        have hnotY := h_no_containment p y hyF.1.ne
        obtain ⟨s, hsP, hsNY⟩ := Finset.not_subset.mp hnotY
        have hsCases : s = p ∨ G.Adj p s := by
          simpa [closedNeighborhood, openNeighborhood] using hsP
        have hsp : G.Adj p s := hsCases.resolve_left (by
          intro hsp
          subst s
          apply hsNY
          simp [closedNeighborhood, openNeighborhood, hyF.1.symm])
        have hsny : ¬G.Adj y s := by
          intro hys
          apply hsNY
          simp [closedNeighborhood, openNeighborhood, hys]
        have hsneY : s ≠ y := by
          intro hsy
          subst s
          exact hsNY (by simp [closedNeighborhood])
        have hsLevel := sameLevelWitness s hsp hsny hsneY
        have hsGap := pairGap_ge_one_of_horizontalEdge G h_two_connected.2.1
          a p s y hsp hsLevel.symm hyF.1 hyF.2 hsny
        have hnotZ := h_no_containment p z hzF.1.ne
        obtain ⟨r, hrP, hrNZ⟩ := Finset.not_subset.mp hnotZ
        have hrCases : r = p ∨ G.Adj p r := by
          simpa [closedNeighborhood, openNeighborhood] using hrP
        have hrp : G.Adj p r := hrCases.resolve_left (by
          intro hrp
          subst r
          apply hrNZ
          simp [closedNeighborhood, openNeighborhood, hzF.1.symm])
        have hrnz : ¬G.Adj z r := by
          intro hzr
          apply hrNZ
          simp [closedNeighborhood, openNeighborhood, hzr]
        have hrneZ : r ≠ z := by
          intro h
          subst r
          exact hrNZ (by simp [closedNeighborhood])
        have hrLevel : G.dist a r = G.dist a p := by
          rcases hrp.diff_dist_adj (u := a) with hsame | hup | hdown
          · exact hsame
          · have := hpMaxBound r; omega
          · have hrLower : r ∈ lowerNeighbors G a p := by
              simp [lowerNeighbors, openNeighborhood, hrp]
              omega
            have hcases : r = y ∨ r = z := by simpa [hparents] using hrLower
            rcases hcases with hry | hrz
            · subst r
              exact False.elim (hrnz hyzAdj.symm)
            · exact False.elim (hrneZ hrz)
        have hrGap := pairGap_ge_one_of_horizontalEdge G h_two_connected.2.1
          a p r z hrp hrLevel.symm hzF.1 hzF.2 hrnz
        have hpGap := pairGap_ge_two_mul_lowerNeighbors_sub_two G
          h_two_connected.2.1 a p
        by_cases hsr : s = r
        · subst r
          have hs2 := pairGap_ge_two_of_double_parent_fork G
            h_two_connected.2.1 a p s y z hsp hyF.1 hzF.1 hyz
              hsLevel.symm hyF.2 hzF.2 hsny hrnz
          have hsum := pairGap_add_pairGap_le_vertexContribution G
            h_two_connected.2.1 a p s hsp.ne
          omega
        · have hsum := three_pairGaps_le_vertexContribution G
            h_two_connected.2.1 a p s r hsp.ne hrp.ne hsr
          omega
    exact False.elim (bklpsLemma10_terminal_P1 G h_two_connected a p hsmall
      hpMaxBound hpOnly hpP1 hpExact h_no_containment)
  · have noP1 (q : V) : ¬2 ≤ (lowerNeighbors G a q).card := by
      intro hq
      exact hexP1 ⟨q, hq⟩
    rcases maxMarked x rfl with hxP1 | hxP2 | hxNearP1
    · exact False.elim (noP1 x hxP1)
    · obtain ⟨x₂, y₁, y₂, hcfg⟩ := hxP2
      rcases hcfg with ⟨hxx₂, hlevelX, hxone, hx₂one, hy₁, hy₂, hy₁y₂⟩
      have hy₁F : G.Adj x y₁ ∧ G.dist a y₁ < G.dist a x := by
        simpa [lowerNeighbors, openNeighborhood] using hy₁
      have hy₂F : G.Adj x₂ y₂ ∧ G.dist a y₂ < G.dist a x₂ := by
        simpa [lowerNeighbors, openNeighborhood] using hy₂
      have hup₁ : G.dist a x = G.dist a y₁ + 1 := by
        have hd := hy₁F.1.diff_dist_adj (u := a)
        omega
      have hup₂ : G.dist a x₂ = G.dist a y₂ + 1 := by
        have hd := hy₂F.1.diff_dist_adj (u := a)
        omega
      have hyLevel : G.dist a y₁ = G.dist a y₂ := by omega
      have maxOnly (t : V) (ht : G.dist a t = G.dist a x) : t = x ∨ t = x₂ := by
        rcases maxMarked t ht with htP1 | htP2 | htNear
        · exact False.elim (noP1 t htP1)
        · obtain ⟨w, pt, pw, hcfgT⟩ := htP2
          rcases hcfgT with ⟨htw, hlev, htone, hwone, hpt, hpw, hptw⟩
          have heq := bklpsLemma10_P2_unique G h_two_connected.2.1 a hsmall
            x x₂ t w y₁ y₂ pt pw hxx₂ htw hlevelX hlev hxone
              hx₂one htone hwone hy₁ hy₂ hy₁y₂ hpt hpw hptw
          rcases Sym2.eq_iff.mp heq with hs | hs
          · exact Or.inl hs.1.symm
          · exact Or.inr hs.2.symm
        · obtain ⟨q, hq, _, _⟩ := htNear
          exact False.elim (noP1 q hq)
      have hypos : 0 < G.dist a y₁ := by
        by_contra hz
        have hz₁ : G.dist a y₁ = 0 := by omega
        have hz₂ : G.dist a y₂ = 0 := by omega
        have hya := (h_two_connected.2.1.dist_eq_zero_iff).mp hz₁
        have hyb := (h_two_connected.2.1.dist_eq_zero_iff).mp hz₂
        exact hy₁y₂ (hya.symm.trans hyb)
      have noOtherP2 (t : V) (htLevel : G.dist a t = G.dist a y₁) :
          ∀ w pt pw, ¬IsP2Configuration G a t w pt pw := by
        intro w pt pw hT
        rcases hT with ⟨htw, hlev, htone, hwone, hpt, hpw, hptw⟩
        have heq := bklpsLemma10_P2_unique G h_two_connected.2.1 a hsmall
          x x₂ t w y₁ y₂ pt pw hxx₂ htw hlevelX hlev hxone
            hx₂one htone hwone hy₁ hy₂ hy₁y₂ hpt hpw hptw
        rcases Sym2.eq_iff.mp heq with hs | hs
        · have := congrArg (G.dist a) hs.1
          omega
        · have := congrArg (G.dist a) hs.2
          omega
      have previousOnly (t : V) (ht : G.dist a t = G.dist a y₁) :
          t = y₁ ∨ t = y₂ := by
        have hta : t ≠ a := by
          intro hta
          subst t
          simp only [dist_self] at ht
          omega
        have hu := bklpsLemma10_noPs G h_two_connected a t hta (noP1 t)
          (by intro q _ _ hq; exact noP1 q hq)
          (noOtherP2 t ht) h_no_containment
        obtain ⟨q, htq, hqLevel⟩ := hu
        have hqMax : G.dist a q = G.dist a x := by omega
        rcases maxOnly q hqMax with hqx | hqx₂
        · have htmem : t ∈ lowerNeighbors G a x := by
            simp [lowerNeighbors, openNeighborhood]
            refine ⟨?_, ?_⟩
            · simpa [hqx] using htq.symm
            · omega
          have := (Finset.card_le_one.mp (by omega :
            (lowerNeighbors G a x).card ≤ 1)) t htmem y₁ hy₁
          exact Or.inl this
        · have htmem : t ∈ lowerNeighbors G a x₂ := by
            simp [lowerNeighbors, openNeighborhood]
            refine ⟨?_, ?_⟩
            · simpa [hqx₂] using htq.symm
            · omega
          have := (Finset.card_le_one.mp (by omega :
            (lowerNeighbors G a x₂).card ≤ 1)) t htmem y₂ hy₂
          exact Or.inr this
      obtain ⟨z₁, hz₁⟩ := exists_lower_neighbor_bfs G h_two_connected.2.1
        a y₁ (by intro h; subst y₁; simp at hypos)
      obtain ⟨z₂, hz₂⟩ := exists_lower_neighbor_bfs G h_two_connected.2.1
        a y₂ (by
          intro h
          subst y₂
          have : G.dist a y₁ = 0 := by simpa using hyLevel
          omega)
      have hy₁one : (lowerNeighbors G a y₁).card = 1 := by
        have hp := Finset.card_pos.mpr ⟨z₁, hz₁⟩
        have hn := noP1 y₁
        omega
      have hy₂one : (lowerNeighbors G a y₂).card = 1 := by
        have hp := Finset.card_pos.mpr ⟨z₂, hz₂⟩
        have hn := noP1 y₂
        omega
      /- The rest is the paper's terminal P2 split: distinct `z₁,z₂`
      supply two extra good edges at each endpoint; a common predecessor is
      a cut vertex unless it is `a`, and the resulting five-vertex graph is
      `C₅` (the chorded alternative has forbidden neighborhood containment). -/
      by_cases hzEq : z₁ = z₂
      · subst z₂
        have hz₁F : G.Adj y₁ z₁ ∧ G.dist a z₁ < G.dist a y₁ := by
          simpa [lowerNeighbors, openNeighborhood] using hz₁
        have hz₂F : G.Adj y₂ z₁ ∧ G.dist a z₁ < G.dist a y₂ := by
          simpa [lowerNeighbors, openNeighborhood] using hz₂
        by_cases hza : z₁ = a
        · subst z₁
          have hy₁dist : G.dist a y₁ = 1 :=
            dist_eq_one_iff_adj.mpr hz₁F.1.symm
          have hy₂dist : G.dist a y₂ = 1 :=
            dist_eq_one_iff_adj.mpr hz₂F.1.symm
          have hxdist : G.dist a x = 2 := by omega
          have hx₂dist : G.dist a x₂ = 2 := by omega
          have hall (t : V) :
              t = a ∨ t = y₁ ∨ t = y₂ ∨ t = x ∨ t = x₂ := by
            have htBound := hxmax' t
            have htLevels : G.dist a t = 0 ∨ G.dist a t = 1 ∨
                G.dist a t = 2 := by omega
            rcases htLevels with ht0 | ht1 | ht2
            · have hat := (h_two_connected.2.1.dist_eq_zero_iff).mp ht0
              exact Or.inl hat.symm
            · rcases previousOnly t (by simpa [hy₁dist] using ht1) with
                hty₁ | hty₂
              · exact Or.inr (Or.inl hty₁)
              · exact Or.inr (Or.inr (Or.inl hty₂))
            · rcases maxOnly t (by omega) with htx | htx₂
              · exact Or.inr (Or.inr (Or.inr (Or.inl htx)))
              · exact Or.inr (Or.inr (Or.inr (Or.inr htx₂)))
          have hnaX : ¬G.Adj a x := by
            intro hax
            have hd : G.dist a x = 1 := dist_eq_one_iff_adj.mpr hax
            omega
          have hnaX₂ : ¬G.Adj a x₂ := by
            intro hax₂
            have hd : G.dist a x₂ = 1 := dist_eq_one_iff_adj.mpr hax₂
            omega
          have hny₁x₂ : ¬G.Adj y₁ x₂ := by
            intro hy₁x₂
            have hy₁mem : y₁ ∈ lowerNeighbors G a x₂ := by
              simp [lowerNeighbors, openNeighborhood, hy₁x₂.symm]
              omega
            have heq := (Finset.card_le_one.mp (by omega :
              (lowerNeighbors G a x₂).card ≤ 1)) y₁ hy₁mem y₂ hy₂
            exact hy₁y₂ heq
          have hny₂x : ¬G.Adj y₂ x := by
            intro hy₂x
            have hy₂mem : y₂ ∈ lowerNeighbors G a x := by
              simp [lowerNeighbors, openNeighborhood, hy₂x.symm]
              omega
            have heq := (Finset.card_le_one.mp (by omega :
              (lowerNeighbors G a x).card ≤ 1)) y₂ hy₂mem y₁ hy₁
            exact hy₁y₂ heq.symm
          by_cases hy₁y₂Adj : G.Adj y₁ y₂
          · have hN : closedNeighborhood G a ⊆ closedNeighborhood G y₁ := by
              intro t ht
              have htCases : t = a ∨ G.Adj a t := by
                simpa [closedNeighborhood, openNeighborhood] using ht
              rcases htCases with rfl | hat
              · simp [closedNeighborhood, openNeighborhood, hz₁F.1]
              · have htdist : G.dist a t = 1 :=
                  dist_eq_one_iff_adj.mpr hat
                rcases previousOnly t (by simpa [hy₁dist] using htdist) with
                    rfl | rfl
                · simp [closedNeighborhood]
                · simp [closedNeighborhood, openNeighborhood, hy₁y₂Adj]
            exact False.elim
              (h_no_containment a y₁ hz₁F.1.ne.symm hN)
          · have hay₁ : a ≠ y₁ := hz₁F.1.ne.symm
            have hay₂ : a ≠ y₂ := hz₂F.1.ne.symm
            have hax : a ≠ x := by
              intro hax
              subst x
              simp only [dist_self] at hxdist
              omega
            have hax₂ : a ≠ x₂ := by
              intro hax₂
              subst x₂
              simp only [dist_self] at hx₂dist
              omega
            have hy₁x : y₁ ≠ x := hy₁F.1.ne.symm
            have hy₁x₂ : y₁ ≠ x₂ := by
              intro h
              subst x₂
              omega
            have hy₂x : y₂ ≠ x := by
              intro h
              subst x
              omega
            have hy₂x₂ : y₂ ≠ x₂ := hy₂F.1.ne.symm
            have hxx₂ne : x ≠ x₂ := hxx₂.ne
            let f : Fin 5 → V := fun i =>
              if i = 0 then a else if i = 1 then y₁ else
                if i = 2 then x else if i = 3 then x₂ else y₂
            have hfInjective : Function.Injective f := by
              intro i j hij
              fin_cases i <;> fin_cases j <;>
                simp [f, hay₁, hay₁.symm, hay₂, hay₂.symm, hax, hax.symm,
                  hax₂, hax₂.symm, hy₁y₂, hy₁y₂.symm, hy₁x, hy₁x.symm,
                  hy₁x₂, hy₁x₂.symm, hy₂x, hy₂x.symm, hy₂x₂, hy₂x₂.symm,
                  hxx₂ne, hxx₂ne.symm] at hij ⊢
            have hfSurjective : Function.Surjective f := by
              intro t
              rcases hall t with rfl | rfl | rfl | rfl | rfl
              · exact ⟨0, by simp [f]⟩
              · exact ⟨1, by simp [f, hay₁]⟩
              · exact ⟨4, by simp [f, hay₂, hy₁y₂.symm]⟩
              · exact ⟨2, by simp [f, hax, hy₁x]⟩
              · exact ⟨3, by simp [f, hax₂, hy₁x₂]⟩
            let e : Fin 5 ≃ V := Equiv.ofBijective f
              ⟨hfInjective, hfSurjective⟩
            have hnxA : ¬G.Adj x a := fun h => hnaX h.symm
            have hnx₂A : ¬G.Adj x₂ a := fun h => hnaX₂ h.symm
            have hnx₂y₁ : ¬G.Adj x₂ y₁ := fun h => hny₁x₂ h.symm
            have hnxY₂ : ¬G.Adj x y₂ := fun h => hny₂x h.symm
            have hny₂y₁ : ¬G.Adj y₂ y₁ := fun h => hy₁y₂Adj h.symm
            have hc01 : (Cn 5).Adj (0 : Fin 5) (1 : Fin 5) := by
              change (cycleGraph 5).Adj 0 1
              native_decide
            have hc12 : (Cn 5).Adj (1 : Fin 5) (2 : Fin 5) := by
              change (cycleGraph 5).Adj 1 2
              native_decide
            have hc23 : (Cn 5).Adj (2 : Fin 5) (3 : Fin 5) := by
              change (cycleGraph 5).Adj 2 3
              native_decide
            have hc34 : (Cn 5).Adj (3 : Fin 5) (4 : Fin 5) := by
              change (cycleGraph 5).Adj 3 4
              native_decide
            have hc40 : (Cn 5).Adj (4 : Fin 5) (0 : Fin 5) := by
              change (cycleGraph 5).Adj 4 0
              native_decide
            have hnc02 : ¬(Cn 5).Adj (0 : Fin 5) (2 : Fin 5) := by
              change ¬(cycleGraph 5).Adj 0 2
              native_decide
            have hnc03 : ¬(Cn 5).Adj (0 : Fin 5) (3 : Fin 5) := by
              change ¬(cycleGraph 5).Adj 0 3
              native_decide
            have hnc13 : ¬(Cn 5).Adj (1 : Fin 5) (3 : Fin 5) := by
              change ¬(cycleGraph 5).Adj 1 3
              native_decide
            have hnc14 : ¬(Cn 5).Adj (1 : Fin 5) (4 : Fin 5) := by
              change ¬(cycleGraph 5).Adj 1 4
              native_decide
            have hnc24 : ¬(Cn 5).Adj (2 : Fin 5) (4 : Fin 5) := by
              change ¬(cycleGraph 5).Adj 2 4
              native_decide
            have hnc20 : ¬(Cn 5).Adj (2 : Fin 5) (0 : Fin 5) :=
              fun h => hnc02 h.symm
            have hnc30 : ¬(Cn 5).Adj (3 : Fin 5) (0 : Fin 5) :=
              fun h => hnc03 h.symm
            have hnc31 : ¬(Cn 5).Adj (3 : Fin 5) (1 : Fin 5) :=
              fun h => hnc13 h.symm
            have hnc41 : ¬(Cn 5).Adj (4 : Fin 5) (1 : Fin 5) :=
              fun h => hnc14 h.symm
            have hnc42 : ¬(Cn 5).Adj (4 : Fin 5) (2 : Fin 5) :=
              fun h => hnc24 h.symm
            have he : Nonempty (G ≃g Cn 5) := by
              have e' : Cn 5 ≃g G :=
                { toEquiv := e
                  map_rel_iff' := by
                    intro i j
                    fin_cases i <;> fin_cases j <;>
                      simp [e, f, hz₁F.1, hz₁F.1.symm, hz₂F.1,
                        hz₂F.1.symm, hy₁F.1, hy₁F.1.symm, hy₂F.1,
                        hy₂F.1.symm, hxx₂, hxx₂.symm, hnaX, hnxA,
                        hnaX₂, hnx₂A, hny₁x₂, hnx₂y₁, hny₂x,
                        hnxY₂, hy₁y₂Adj, hny₂y₁, hc01, hc01.symm,
                        hc12, hc12.symm, hc23, hc23.symm, hc34,
                        hc34.symm, hc40, hc40.symm, hnc02, hnc03,
                        hnc13, hnc14, hnc24, hnc20, hnc30, hnc31,
                        hnc41, hnc42] }
              exact ⟨e'.symm⟩
            exact False.elim (h_not_C5 he)
        · have hy₁z : y₁ ≠ z₁ := hz₁F.1.ne
          have haz : a ≠ z₁ := Ne.symm hza
          let yD : {q : V // q ≠ z₁} := ⟨y₁, hy₁z⟩
          let aD : {q : V // q ≠ z₁} := ⟨a, haz⟩
          have step (q r : {s : V // s ≠ z₁})
              (hq : G.dist a y₁ ≤ G.dist a q.1)
              (hqr : (deleteVertex G z₁).Adj q r) :
              G.dist a y₁ ≤ G.dist a r.1 := by
            by_contra hr
            have hqrG : G.Adj q.1 r.1 := hqr
            have hd := hqrG.diff_dist_adj (u := a)
            have hqLevel : G.dist a q.1 = G.dist a y₁ := by omega
            have hrLevel : G.dist a r.1 < G.dist a y₁ := by omega
            rcases previousOnly q.1 hqLevel with hqy₁ | hqy₂
            · have hrmem : r.1 ∈ lowerNeighbors G a y₁ := by
                apply Finset.mem_filter.mpr
                refine ⟨?_, hrLevel⟩
                simpa [openNeighborhood, hqy₁] using hqrG
              have hrz : r.1 = z₁ :=
                (Finset.card_le_one.mp (by omega :
                  (lowerNeighbors G a y₁).card ≤ 1)) r.1 hrmem z₁ hz₁
              exact r.2 hrz
            · have hrmem : r.1 ∈ lowerNeighbors G a y₂ := by
                apply Finset.mem_filter.mpr
                refine ⟨?_, ?_⟩
                · simpa [openNeighborhood, hqy₂] using hqrG
                · omega
              have hrz : r.1 = z₁ :=
                (Finset.card_le_one.mp (by omega :
                  (lowerNeighbors G a y₂).card ≤ 1)) r.1 hrmem z₁ hz₂
              exact r.2 hrz
          have walkStays {q r : {s : V // s ≠ z₁}}
              (p : (deleteVertex G z₁).Walk q r)
              (hq : G.dist a y₁ ≤ G.dist a q.1) :
              G.dist a y₁ ≤ G.dist a r.1 := by
            induction p with
            | nil => exact hq
            | @cons q r s hqr p ih => exact ih (step q r hq hqr)
          obtain ⟨p⟩ := (h_two_connected.2.2 z₁) yD aD
          have hstay := walkStays p (by simp [yD])
          have hzero : G.dist a a = 0 := dist_self
          have hstay' : G.dist a y₁ ≤ G.dist a a := by simpa [aD] using hstay
          omega
      · have hx₂Gap := pairGap_ge_two_terminal_P2 G h_two_connected.2.1
          a x x₂ y₁ y₂ z₁ z₂ hxx₂ hlevelX hxone hx₂one hy₁ hy₂
            hy₁y₂ hy₁one hy₂one hz₁ hz₂ hzEq
        have hxGap := pairGap_ge_two_terminal_P2 G h_two_connected.2.1
          a x₂ x y₂ y₁ z₂ z₁ hxx₂.symm hlevelX.symm hx₂one hxone
            hy₂ hy₁ hy₁y₂.symm hy₂one hy₁one hz₂ hz₁ (Ne.symm hzEq)
        have hsum := pairGap_add_pairGap_le_vertexContribution G
          h_two_connected.2.1 a x x₂ hxx₂.ne
        omega
    · obtain ⟨q, hq, _, _⟩ := hxNearP1
      exact False.elim (noP1 q hq)

end

end BKLPS.External
