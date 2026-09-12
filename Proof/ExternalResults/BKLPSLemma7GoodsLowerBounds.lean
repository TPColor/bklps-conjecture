import Proof.ExternalResults.BKLPSGoodEdgesDeletion

namespace BKLPS.External

open SimpleGraph

universe u

/-- A graph in which every distinct pair is adjacent is isomorphic to the
canonical complete graph of the same order. -/
theorem isomorphicToKn_of_forall_adj
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h : ∀ a b : V, a ≠ b → G.Adj a b) :
    IsomorphicToKn G := by
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  refine ⟨{
    toEquiv := e
    map_rel_iff' := ?_ }⟩
  intro a b
  constructor
  · intro hab
    exact h a b (fun hab' => hab (congrArg e hab'))
  · intro hab
    simpa using hab.ne

/-- A noncomplete finite graph has a pair of distinct nonadjacent vertices. -/
theorem exists_nonedge_of_not_isomorphicToKn
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h : ¬IsomorphicToKn G) :
    ∃ a b : V, a ≠ b ∧ ¬G.Adj a b := by
  by_contra hn
  push_neg at hn
  exact h (isomorphicToKn_of_forall_adj G hn)

/-- If the restored vertex is dominating, every nonedge of the deletion gains
the two good edges incident with the restored vertex.  This is BKLPS (C1) for
one nonedge. -/
theorem pairGain_two_of_neighbor_nonedge
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (a b : {x : V // x ≠ u}) (hab : a ≠ b)
    (ha_adj : G.Adj u a.1) (hb_adj : G.Adj u b.1)
    (hnab : ¬(deleteVertex G u).Adj a b) :
    pairGap G a.1 b.1 - pairGap (deleteVertex G u) a b ≥ 2 := by
  classical
  let f : Sym2 {x : V // x ≠ u} → Sym2 V := Sym2.map Subtype.val
  let A : Finset (Sym2 V) :=
    (goodEdgeFinset (deleteVertex G u) a b).image f
  let e₁ : Sym2 V := s(u, a.1)
  let e₂ : Sym2 V := s(u, b.1)
  have hf : Function.Injective f := by
    dsimp [f]
    exact Sym2.map.injective Subtype.val_injective
  have hnabG : ¬G.Adj a.1 b.1 := hnab
  have habv : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
  have habdist : 1 < G.dist a.1 b.1 :=
    hconn.one_lt_dist_of_ne_of_not_adj habv hnabG
  have hbaDist : 1 < G.dist b.1 a.1 := by simpa [dist_comm] using habdist
  have he₁good : IsGoodEdgeFor G a.1 b.1 e₁ := by
    change G.Adj u a.1 ∧
      ((G.dist a.1 u < G.dist a.1 a.1 ∧
          G.dist b.1 a.1 < G.dist b.1 u) ∨
       (G.dist a.1 a.1 < G.dist a.1 u ∧
          G.dist b.1 u < G.dist b.1 a.1))
    refine ⟨ha_adj, Or.inr ?_⟩
    rw [SimpleGraph.dist_self,
      dist_eq_one_iff_adj.mpr ha_adj.symm,
      dist_eq_one_iff_adj.mpr hb_adj.symm]
    omega
  have he₂good : IsGoodEdgeFor G a.1 b.1 e₂ := by
    change G.Adj u b.1 ∧
      ((G.dist a.1 u < G.dist a.1 b.1 ∧
          G.dist b.1 b.1 < G.dist b.1 u) ∨
       (G.dist a.1 b.1 < G.dist a.1 u ∧
          G.dist b.1 u < G.dist b.1 b.1))
    refine ⟨hb_adj, Or.inl ?_⟩
    rw [SimpleGraph.dist_self,
      dist_eq_one_iff_adj.mpr ha_adj.symm,
      dist_eq_one_iff_adj.mpr hb_adj.symm]
    omega
  have he₁_ne_e₂ : e₁ ≠ e₂ := by
    intro h
    exact hab (Subtype.ext ((Sym2.mkEmbedding u).injective h))
  have image_avoids_u (e : Sym2 {x : V // x ≠ u}) : u ∉ f e := by
    intro hm
    dsimp [f] at hm
    rw [Sym2.mem_map] at hm
    obtain ⟨x, _, hxu⟩ := hm
    exact x.2 hxu
  have he₁_not_A : e₁ ∉ A := by
    intro he
    obtain ⟨e, _, heq⟩ := Finset.mem_image.mp he
    have hm : u ∈ e₁ := by simp [e₁]
    rw [← heq] at hm
    exact image_avoids_u e hm
  have he₂_not_A : e₂ ∉ A := by
    intro he
    obtain ⟨e, _, heq⟩ := Finset.mem_image.mp he
    have hm : u ∈ e₂ := by simp [e₂]
    rw [← heq] at hm
    exact image_avoids_u e hm
  let T : Finset (Sym2 V) := insert e₁ (insert e₂ A)
  have hTcard : T.card = goodEdgeCount (deleteVertex G u) a b + 2 := by
    unfold T
    rw [Finset.card_insert_of_notMem (by simp [he₁_ne_e₂, he₁_not_A]),
      Finset.card_insert_of_notMem he₂_not_A]
    unfold A goodEdgeCount
    rw [Finset.card_image_iff.mpr hf.injOn]
  have hTsub : T ⊆ goodEdgeFinset G a.1 b.1 := by
    intro e he
    simp only [T, Finset.mem_insert] at he
    rcases he with rfl | rfl | he
    · exact Finset.mem_filter.mpr ⟨by simpa [e₁] using ha_adj, he₁good⟩
    · exact Finset.mem_filter.mpr ⟨by simpa [e₂] using hb_adj, he₂good⟩
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
      simp only [goodEdgeFinset, Finset.mem_filter,
        SimpleGraph.mem_edgeFinset] at he' ⊢
      exact ⟨by
        induction e' using Sym2.inductionOn with
        | _ x y => exact he'.1,
        deleteVertex_goodEdge_maps_to_goodEdge G hconn u v huv hN a b e' he'.2⟩
  have hcount : goodEdgeCount (deleteVertex G u) a b + 2 ≤
      goodEdgeCount G a.1 b.1 := by
    rw [← hTcard]
    exact Finset.card_le_card hTsub
  have hdist := deleteVertex_dist_eq_of_closedNeighborhood_subset
    G hconn u v huv hN a b
  unfold pairGap
  omega

/-- Neighbors in the preceding breadth-first-search layer. -/
noncomputable def lowerNeighbors
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u x : V) : Finset V :=
  (openNeighborhood G x).filter fun y => G.dist u y < G.dist u x

/-- BKLPS condition (C2) in its general BFS-layer form.  If `x` has `p`
neighbors in the preceding layer, all but the one used by a geodesic supply
two additional good edges. -/
theorem pairGap_ge_two_mul_lowerNeighbors_sub_two
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (u x : V) :
    pairGap G u x ≥ (2 * (lowerNeighbors G u x).card - 2 : ℤ) := by
  classical
  let P := lowerNeighbors G u x
  by_cases hsmall : P.card ≤ 1
  · have hnonneg := pairGap_nonneg G hconn u x
    dsimp [P] at hsmall ⊢
    omega
  · have hPtwo : 2 ≤ P.card := by omega
    have parent_facts (y : V) (hy : y ∈ P) :
        G.Adj x y ∧ G.dist u y < G.dist u x ∧
          G.dist u x = G.dist u y + 1 := by
      have hy' : G.Adj x y ∧ G.dist u y < G.dist u x := by
        simpa [P, lowerNeighbors, openNeighborhood] using hy
      have htri := hconn.dist_triangle (u := u) (v := y) (w := x)
      rw [dist_eq_one_iff_adj.mpr hy'.1.symm] at htri
      exact ⟨hy'.1, hy'.2, by omega⟩
    have hdistx : 2 ≤ G.dist u x := by
      obtain ⟨y₁, hy₁, y₂, hy₂, hyne⟩ :=
        Finset.one_lt_card.mp (by omega : 1 < P.card)
      have h₁ := parent_facts y₁ hy₁
      have h₂ := parent_facts y₂ hy₂
      by_contra h
      have hy₁u : y₁ = u := ((hconn.dist_eq_zero_iff (u := u) (v := y₁)).mp
        (by omega)).symm
      have hy₂u : y₂ = u := ((hconn.dist_eq_zero_iff (u := u) (v := y₂)).mp
        (by omega)).symm
      exact hyne (hy₁u.trans hy₂u.symm)
    have predecessor_exists (y : V) (hy : y ∈ P) :
        ∃ z : V, G.Adj y z ∧ G.dist u z < G.dist u y := by
      have hyfacts := parent_facts y hy
      have hyu : y ≠ u := by
        intro h
        subst y
        have hdistone : G.dist u x = 1 :=
          dist_eq_one_iff_adj.mpr hyfacts.1.symm
        omega
      obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist y u
      cases q with
      | nil => exact False.elim (hyu rfl)
      | @cons _ z _ hyz q =>
          refine ⟨z, hyz, ?_⟩
          have hle := G.dist_le q
          rw [dist_comm (u := z) (v := u)] at hle
          have hcomm : G.dist y u = G.dist u y := dist_comm
          rw [hcomm] at hq
          simp only [Walk.length_cons] at hq
          omega
    let pred : V → V := fun y =>
      if hy : y ∈ P then Classical.choose (predecessor_exists y hy) else u
    have pred_facts (y : V) (hy : y ∈ P) :
        G.Adj y (pred y) ∧ G.dist u (pred y) < G.dist u y := by
      dsimp [pred]
      rw [dif_pos hy]
      exact Classical.choose_spec (predecessor_exists y hy)
    let U : Finset (Sym2 V) := P.image fun y => s(x, y)
    let Z : Finset (Sym2 V) := P.image fun y => s(y, pred y)
    have hUcard : U.card = P.card := by
      unfold U
      exact Finset.card_image_iff.mpr (Sym2.mkEmbedding x).injective.injOn
    have hZinj : Set.InjOn (fun y => s(y, pred y)) P := by
      intro y₁ hy₁ y₂ hy₂ heq
      rcases Sym2.eq_iff.mp heq with hsame | hswap
      · exact hsame.1
      · have hlevel₁ := (parent_facts y₁ hy₁).2.2
        have hlevel₂ := (parent_facts y₂ hy₂).2.2
        have hp₂ := (pred_facts y₂ hy₂).2
        rw [hswap.1] at hlevel₁
        exact False.elim (by omega)
    have hZcard : Z.card = P.card := by
      unfold Z
      exact Finset.card_image_iff.mpr hZinj
    have hUZdisj : Disjoint U Z := by
      rw [Finset.disjoint_left]
      intro edge hedgeU hedgeZ
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hedgeU
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hedgeZ
      rcases Sym2.eq_iff.mp heq with hsame | hswap
      · have hxlevel := (parent_facts y hy).2.2
        have hwlevel := (parent_facts w hw).2.2
        have hpw := (pred_facts w hw).2
        exact (parent_facts w hw).1.ne hsame.1.symm
      · have hxlevel := (parent_facts y hy).2.2
        have hpw := (pred_facts w hw).2
        rw [hswap.2, hswap.1] at hpw
        exact (by omega : False)
    have hUgood : U ⊆ goodEdgeFinset G u x := by
      intro edge hedge
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hedge
      have hyf := parent_facts y hy
      apply Finset.mem_filter.mpr
      refine ⟨by simpa using hyf.1, ?_⟩
      change G.Adj x y ∧
        ((G.dist u x < G.dist u y ∧ G.dist x y < G.dist x x) ∨
         (G.dist u y < G.dist u x ∧ G.dist x x < G.dist x y))
      refine ⟨hyf.1, Or.inr ⟨hyf.2.1, ?_⟩⟩
      rw [SimpleGraph.dist_self, dist_eq_one_iff_adj.mpr hyf.1]
      omega
    have hZgood : Z ⊆ goodEdgeFinset G u x := by
      intro edge hedge
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hedge
      have hyf := parent_facts y hy
      have hpf := pred_facts y hy
      have hxpred : ¬G.Adj x (pred y) := by
        intro h
        have htri := hconn.dist_triangle (u := u) (v := pred y) (w := x)
        rw [dist_eq_one_iff_adj.mpr h.symm] at htri
        omega
      have hne : x ≠ pred y := by
        intro h
        have heqdist := congrArg (G.dist u) h
        omega
      have hfar : 1 < G.dist x (pred y) :=
        hconn.one_lt_dist_of_ne_of_not_adj hne hxpred
      apply Finset.mem_filter.mpr
      refine ⟨by simpa using hpf.1, ?_⟩
      change G.Adj y (pred y) ∧
        ((G.dist u y < G.dist u (pred y) ∧
            G.dist x (pred y) < G.dist x y) ∨
         (G.dist u (pred y) < G.dist u y ∧
            G.dist x y < G.dist x (pred y)))
      refine ⟨hpf.1, Or.inr ⟨hpf.2, ?_⟩⟩
      rw [dist_eq_one_iff_adj.mpr hyf.1]
      exact hfar
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u x
    let E : Finset (Sym2 V) := p.edges.toFinset
    let Q : Finset V := P.filter fun y => y ∈ p.support
    have hQcard : Q.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro y₁ hy₁ y₂ hy₂
      have hy₁P := (Finset.mem_filter.mp hy₁).1
      have hy₂P := (Finset.mem_filter.mp hy₂).1
      have hy₁supp := (Finset.mem_filter.mp hy₁).2
      have hy₂supp := (Finset.mem_filter.mp hy₂).2
      have hlen₁ : (p.takeUntil y₁ hy₁supp).length = G.dist u y₁ :=
        length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hy₁supp)
      have hlen₂ : (p.takeUntil y₂ hy₂supp).length = G.dist u y₂ :=
        length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hy₂supp)
      have hlevels : G.dist u y₁ = G.dist u y₂ := by
        have h₁ := (parent_facts y₁ hy₁P).2.2
        have h₂ := (parent_facts y₂ hy₂P).2.2
        omega
      calc
        y₁ = p.getVert (p.takeUntil y₁ hy₁supp).length :=
          (p.getVert_length_takeUntil hy₁supp).symm
        _ = p.getVert (p.takeUntil y₂ hy₂supp).length := by
          rw [hlen₁, hlen₂, hlevels]
        _ = y₂ := p.getVert_length_takeUntil hy₂supp
    have hinterSub : (E ∩ (U ∪ Z)) ⊆
        (Q.image (fun y => s(x, y))) ∪ (Q.image fun y => s(y, pred y)) := by
      intro edge hedge
      have hedgeE := (Finset.mem_inter.mp hedge).1
      have hedgeUZ := (Finset.mem_inter.mp hedge).2
      have hedgeList : edge ∈ p.edges := by simpa [E] using hedgeE
      rcases Finset.mem_union.mp hedgeUZ with hedgeU | hedgeZ
      · obtain ⟨y, hyP, rfl⟩ := Finset.mem_image.mp hedgeU
        apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨y, Finset.mem_filter.mpr ⟨hyP, ?_⟩, rfl⟩
        exact p.snd_mem_support_of_mem_edges hedgeList
      · obtain ⟨y, hyP, rfl⟩ := Finset.mem_image.mp hedgeZ
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨y, Finset.mem_filter.mpr ⟨hyP, ?_⟩, rfl⟩
        exact p.fst_mem_support_of_mem_edges hedgeList
    have hinterCard : (E ∩ (U ∪ Z)).card ≤ 2 := by
      have h₁ := Finset.card_le_card hinterSub
      have h₂ := Finset.card_union_le
        (Q.image (fun y => s(x, y))) (Q.image fun y => s(y, pred y))
      have h₃ : (Q.image (fun y => s(x, y))).card ≤ Q.card :=
        Finset.card_image_le
      have h₄ : (Q.image (fun y => s(y, pred y))).card ≤ Q.card :=
        Finset.card_image_le
      omega
    have hEcard : E.card = G.dist u x := by
      unfold E
      rw [List.toFinset_card_of_nodup
        (Walk.isPath_of_length_eq_dist p hp).isTrail.edges_nodup,
        p.length_edges, hp]
    have hUZcard : (U ∪ Z).card = 2 * P.card := by
      rw [Finset.card_union_of_disjoint hUZdisj, hUcard, hZcard]
      omega
    have hbigCard : (E ∪ (U ∪ Z)).card ≥
        G.dist u x + 2 * P.card - 2 := by
      have hcardEq := Finset.card_union_add_card_inter E (U ∪ Z)
      rw [hEcard, hUZcard] at hcardEq
      omega
    have hEgood : E ⊆ goodEdgeFinset G u x := by
      intro edge hedge
      have hedgeList : edge ∈ p.edges := by simpa [E] using hedge
      exact Finset.mem_filter.mpr
        ⟨by simpa [SimpleGraph.mem_edgeFinset] using p.edges_subset_edgeSet hedgeList,
          geodesicEdgeGood p hp edge hedgeList⟩
    have hbigSub : E ∪ (U ∪ Z) ⊆ goodEdgeFinset G u x :=
      Finset.union_subset hEgood (Finset.union_subset hUgood hZgood)
    have hcount := Finset.card_le_card hbigSub
    unfold pairGap goodEdgeCount
    dsimp [P] at hbigCard ⊢
    omega

/-- The predecessors of a distance-two vertex used in BKLPS condition (C2). -/
noncomputable def distanceTwoParents
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u a : V) : Finset V :=
  by
    classical
    exact (openNeighborhood G a).filter fun w => G.Adj u w

/-- BKLPS (C2) for the second BFS layer: if `a` has `p` neighbors in
`N(u)`, the `2p` edges from `u` and `a` to those neighbors are all good for
`{u,a}`. -/
theorem pairGap_ge_two_mul_parents_sub_two
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u a : V) (hua : G.dist u a = 2) :
    pairGap G u a ≥ (2 * (distanceTwoParents G u a).card - 2 : ℤ) := by
  classical
  let P := distanceTwoParents G u a
  let U : Finset (Sym2 V) := P.image (fun w => s(u, w))
  let A : Finset (Sym2 V) := P.image (fun w => s(a, w))
  have hne : u ≠ a := by
    intro h
    subst a
    simp at hua
  have parent_facts (w : V) (hw : w ∈ P) : G.Adj a w ∧ G.Adj u w := by
    simpa [P, distanceTwoParents, openNeighborhood] using hw
  have hUcard : U.card = P.card := by
    unfold U
    apply Finset.card_image_iff.mpr
    intro x hx y hy hxy
    exact (Sym2.mkEmbedding u).injective hxy
  have hAcard : A.card = P.card := by
    unfold A
    apply Finset.card_image_iff.mpr
    intro x hx y hy hxy
    exact (Sym2.mkEmbedding a).injective hxy
  have hdisj : Disjoint U A := by
    rw [Finset.disjoint_left]
    intro e heU heA
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp heU
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp heA
    rcases Sym2.eq_iff.mp heq with hsame | hswap
    · exact hne hsame.1.symm
    · exact (parent_facts z hz).2.ne hswap.2.symm
  have hUgood : U ⊆ goodEdgeFinset G u a := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
    have hwf := parent_facts w hw
    apply Finset.mem_filter.mpr
    refine ⟨by simpa using hwf.2, ?_⟩
    change G.Adj u w ∧
      ((G.dist u u < G.dist u w ∧ G.dist a w < G.dist a u) ∨
       (G.dist u w < G.dist u u ∧ G.dist a u < G.dist a w))
    refine ⟨hwf.2, Or.inl ?_⟩
    rw [SimpleGraph.dist_self, dist_eq_one_iff_adj.mpr hwf.2,
      dist_eq_one_iff_adj.mpr hwf.1, dist_comm, hua]
    omega
  have hAgood : A ⊆ goodEdgeFinset G u a := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
    have hwf := parent_facts w hw
    apply Finset.mem_filter.mpr
    refine ⟨by simpa using hwf.1, ?_⟩
    change G.Adj a w ∧
      ((G.dist u a < G.dist u w ∧ G.dist a w < G.dist a a) ∨
       (G.dist u w < G.dist u a ∧ G.dist a a < G.dist a w))
    refine ⟨hwf.1, Or.inr ?_⟩
    rw [hua, dist_eq_one_iff_adj.mpr hwf.2,
      SimpleGraph.dist_self, dist_eq_one_iff_adj.mpr hwf.1]
    omega
  have hsub : U ∪ A ⊆ goodEdgeFinset G u a :=
    Finset.union_subset hUgood hAgood
  have hcount : 2 * P.card ≤ goodEdgeCount G u a := by
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, hUcard, hAcard] at hc
    unfold goodEdgeCount
    omega
  unfold pairGap
  change (goodEdgeCount G u a : ℤ) - G.dist u a ≥ _
  rw [hua]
  dsimp [P]
  dsimp [P] at hcount
  omega

/-- One good edge outside a chosen geodesic contributes one unit beyond the
distance term.  This is the counting step used in BKLPS (C3). -/
theorem pairGap_ge_one_of_extra_goodEdge
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (a b : V)
    (p : G.Walk a b) (hp : p.length = G.dist a b)
    (e : Sym2 V) (hegood : IsGoodEdgeFor G a b e)
    (heextra : e ∉ p.edges) :
    pairGap G a b ≥ 1 := by
  classical
  let S : Finset (Sym2 V) := insert e p.edges.toFinset
  have hbase : p.edges.toFinset ⊆ goodEdgeFinset G a b := by
    intro q hq
    rw [List.mem_toFinset] at hq
    exact Finset.mem_filter.mpr
      ⟨by simpa [SimpleGraph.mem_edgeFinset] using p.edges_subset_edgeSet hq,
        geodesicEdgeGood p hp q hq⟩
  have heedge : e ∈ G.edgeSet := by
    induction e using Sym2.inductionOn with
    | _ x y => exact hegood.1
  have hsub : S ⊆ goodEdgeFinset G a b := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_filter.mpr
        ⟨by simpa [SimpleGraph.mem_edgeFinset] using heedge, hegood⟩
    · exact hbase hq
  have hcard : S.card = G.dist a b + 1 := by
    unfold S
    rw [Finset.card_insert_of_notMem (by simpa using heextra)]
    have hc : p.edges.toFinset.card = p.edges.length :=
      (List.toFinset_card_of_nodup
        (Walk.isPath_of_length_eq_dist p hp).isTrail.edges_nodup)
    rw [hc, p.length_edges, hp]
  have hcount := Finset.card_le_card hsub
  unfold pairGap goodEdgeCount
  rw [hcard] at hcount
  omega

/-- Two distinct good edges outside a geodesic contribute two units beyond
the distance term. -/
theorem pairGap_ge_two_of_two_extra_goodEdges
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (a b : V)
    (p : G.Walk a b) (hp : p.length = G.dist a b)
    (e₁ e₂ : Sym2 V) (hne : e₁ ≠ e₂)
    (hgood₁ : IsGoodEdgeFor G a b e₁)
    (hgood₂ : IsGoodEdgeFor G a b e₂)
    (hextra₁ : e₁ ∉ p.edges) (hextra₂ : e₂ ∉ p.edges) :
    pairGap G a b ≥ 2 := by
  classical
  let S : Finset (Sym2 V) := insert e₁ (insert e₂ p.edges.toFinset)
  have hbase : p.edges.toFinset ⊆ goodEdgeFinset G a b := by
    intro q hq
    rw [List.mem_toFinset] at hq
    exact Finset.mem_filter.mpr
      ⟨by simpa [SimpleGraph.mem_edgeFinset] using p.edges_subset_edgeSet hq,
        geodesicEdgeGood p hp q hq⟩
  have hedge₁ : e₁ ∈ G.edgeSet := by
    induction e₁ using Sym2.inductionOn with
    | _ x y => exact hgood₁.1
  have hedge₂ : e₂ ∈ G.edgeSet := by
    induction e₂ using Sym2.inductionOn with
    | _ x y => exact hgood₂.1
  have hsub : S ⊆ goodEdgeFinset G a b := by
    intro q hq
    simp only [S, Finset.mem_insert] at hq
    rcases hq with rfl | rfl | hq
    · exact Finset.mem_filter.mpr
        ⟨by simpa [SimpleGraph.mem_edgeFinset] using hedge₁, hgood₁⟩
    · exact Finset.mem_filter.mpr
        ⟨by simpa [SimpleGraph.mem_edgeFinset] using hedge₂, hgood₂⟩
    · exact hbase hq
  have hcard : S.card = G.dist a b + 2 := by
    unfold S
    rw [Finset.card_insert_of_notMem (by simp [hne, hextra₁]),
      Finset.card_insert_of_notMem (by simpa using hextra₂)]
    have hc : p.edges.toFinset.card = p.edges.length :=
      (List.toFinset_card_of_nodup
        (Walk.isPath_of_length_eq_dist p hp).isTrail.edges_nodup)
    rw [hc, p.length_edges, hp]
  have hcount := Finset.card_le_card hsub
  unfold pairGap goodEdgeCount
  rw [hcard] at hcount
  omega

/-- A vertex on a shortest walk splits its length into the two corresponding
distances.  This is the metric fact used to show that the extra edge in
BKLPS condition (C3) cannot already lie on the chosen geodesic. -/
theorem geodesic_dist_add_of_mem_support
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {a b z : V}
    (p : G.Walk a b) (hp : p.length = G.dist a b)
    (hz : z ∈ p.support) :
    G.dist a z + G.dist z b = G.dist a b := by
  have ht : (p.takeUntil z hz).length = G.dist a z :=
    length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hz)
  have hd : (p.dropUntil z hz).length = G.dist z b :=
    length_eq_dist_of_subwalk hp (p.isSubwalk_dropUntil hz)
  have hall := congrArg Walk.length (p.take_spec hz)
  simp only [Walk.length_append] at hall
  omega

/-- BKLPS condition (C3), in the exact local form used in their proof.  A
horizontal edge `ab` and a lower neighbor `x` of `a` not adjacent to `b`
provide the extra good edge `ax` for the pair `{u,b}`. -/
theorem pairGap_ge_one_of_horizontalEdge
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u a b x : V) (hab : G.Adj a b)
    (horiz : G.dist u a = G.dist u b)
    (hax : G.Adj a x) (hlower : G.dist u x < G.dist u a)
    (hnxb : ¬G.Adj x b) :
    pairGap G u b ≥ 1 := by
  classical
  have hxb : x ≠ b := by
    intro h
    subst x
    omega
  have hba : G.dist b a = 1 := dist_eq_one_iff_adj.mpr hab.symm
  have hbx : 1 < G.dist b x := by
    rw [dist_comm]
    exact hconn.one_lt_dist_of_ne_of_not_adj hxb hnxb
  have hgood : IsGoodEdgeFor G u b s(a, x) := by
    change G.Adj a x ∧
      ((G.dist u a < G.dist u x ∧ G.dist b x < G.dist b a) ∨
       (G.dist u x < G.dist u a ∧ G.dist b a < G.dist b x))
    exact ⟨hax, Or.inr ⟨hlower, by omega⟩⟩
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u b
  have hextra : s(a, x) ∉ p.edges := by
    intro he
    have ha_support : a ∈ p.support := p.fst_mem_support_of_mem_edges he
    have hadd := geodesic_dist_add_of_mem_support p hp ha_support
    have habdist : G.dist a b = 1 := dist_eq_one_iff_adj.mpr hab
    omega
  exact pairGap_ge_one_of_extra_goodEdge G hconn u b p hp s(a, x) hgood hextra

end BKLPS.External
