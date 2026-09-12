import Proof.ExternalResults.BKLPSGoodEdges
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Walks under a vertex contraction

The domination arguments repeatedly replace the deleted vertex `u` by the
dominating vertex `v`.  An edge can then either remain an edge or collapse to
a point.  The construction below records this elementary walk operation and
the resulting length inequality.
-/

namespace BKLPS.External

open SimpleGraph

universe u v

/-- Map a walk by a function which takes adjacent vertices either to adjacent
vertices or to the same vertex.  Collapsed edges are omitted. -/
def Walk.mapAdjOrEq
    {V : Type u} {W : Type v} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W)
    (hf : ∀ {a b : V}, G.Adj a b → f a = f b ∨ H.Adj (f a) (f b))
    {a b : V} : G.Walk a b → H.Walk (f a) (f b)
  | .nil => .nil
  | @SimpleGraph.Walk.cons _ _ _ x _ h p =>
      if heq : f _ = f x then
        (mapAdjOrEq f hf p).copy heq.symm rfl
      else
        .cons ((hf h).resolve_left heq) (mapAdjOrEq f hf p)

@[simp]
theorem Walk.length_mapAdjOrEq_le
    {V : Type u} {W : Type v} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W)
    (hf : ∀ {a b : V}, G.Adj a b → f a = f b ∨ H.Adj (f a) (f b))
    {a b : V} (p : G.Walk a b) :
    (mapAdjOrEq f hf p).length ≤ p.length := by
  induction p with
  | nil => simp [Walk.mapAdjOrEq]
  | @cons a x b h p ih =>
      rw [Walk.mapAdjOrEq]
      split
      · simp only [Walk.length_copy, Walk.length_cons]
        omega
      · simp only [Walk.length_cons]
        omega

/-- The retraction which sends `u` to `v` and fixes every other vertex. -/
def dominatedRetraction
    {V : Type u} [DecidableEq V] (u v : V) (huv : u ≠ v) :
    V → {x : V // x ≠ u} :=
  fun x => if hx : x = u then ⟨v, huv.symm⟩ else ⟨x, hx⟩

@[simp] theorem dominatedRetraction_apply_deleted
    {V : Type u} [DecidableEq V] {u v : V} (huv : u ≠ v) :
    dominatedRetraction u v huv u = ⟨v, huv.symm⟩ := by
  simp [dominatedRetraction]

@[simp] theorem dominatedRetraction_apply_of_ne
    {V : Type u} [DecidableEq V] {u v x : V} (huv : u ≠ v) (h : x ≠ u) :
    dominatedRetraction u v huv x = ⟨x, h⟩ := by
  simp [dominatedRetraction, h]

/-- Closed-neighborhood domination makes the retraction adjacency-preserving,
with the sole exception that the edge `uv` collapses. -/
theorem dominatedRetraction_adj_or_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v) :
    ∀ {a b : V}, G.Adj a b →
      dominatedRetraction u v huv a = dominatedRetraction u v huv b ∨
        (deleteVertex G u).Adj (dominatedRetraction u v huv a)
          (dominatedRetraction u v huv b) := by
  intro a b hab
  by_cases ha : a = u
  · subst a
    by_cases hb : b = v
    · left
      simp [dominatedRetraction, hb]
    · right
      have hb_u : b ≠ u := hab.ne'
      simp only [dominatedRetraction_apply_deleted huv,
        dominatedRetraction_apply_of_ne huv hb_u]
      change G.Adj v b
      have hb_mem : b ∈ closedNeighborhood G u := by
        simp [closedNeighborhood, openNeighborhood, hab]
      have := hN hb_mem
      simpa [closedNeighborhood, openNeighborhood, hb] using this
  · by_cases hb : b = u
    · subst b
      by_cases ha_v : a = v
      · left
        simp [dominatedRetraction, ha_v]
      · right
        simp only [dominatedRetraction_apply_of_ne huv ha,
          dominatedRetraction_apply_deleted huv]
        change G.Adj a v
        have ha_mem : a ∈ closedNeighborhood G u := by
          simp [closedNeighborhood, openNeighborhood, hab.symm]
        have := hN ha_mem
        have : G.Adj v a := by
          simpa [closedNeighborhood, openNeighborhood, ha_v] using this
        exact this.symm
    · right
      simp only [dominatedRetraction_apply_of_ne huv ha,
        dominatedRetraction_apply_of_ne huv hb]
      change G.Adj a b
      exact hab

/-- Deleting a vertex whose closed neighborhood is contained in another's
preserves connectedness. -/
theorem deleteVertex_connected_of_closedNeighborhood_subset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v) :
    (deleteVertex G u).Connected := by
  letI : Nonempty {x : V // x ≠ u} := ⟨⟨v, huv.symm⟩⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨p, _hp⟩ := hconn.exists_walk_length_eq_dist x.1 y.1
  exact ⟨(Walk.mapAdjOrEq (dominatedRetraction u v huv)
    (dominatedRetraction_adj_or_eq G u v huv hN) p).copy
      (dominatedRetraction_apply_of_ne huv x.property)
      (dominatedRetraction_apply_of_ne huv y.property)⟩

/-- Deleting a dominated vertex preserves all distances between the surviving
vertices. -/
theorem deleteVertex_dist_eq_of_closedNeighborhood_subset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (a b : {x : V // x ≠ u}) :
    (deleteVertex G u).dist a b = G.dist a.1 b.1 := by
  have hdel_conn := deleteVertex_connected_of_closedNeighborhood_subset
    G hconn u v huv hN
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist a.1 b.1
  have hle_delete : (deleteVertex G u).dist a b ≤ G.dist a.1 b.1 := by
    rw [← hp]
    let q := Walk.mapAdjOrEq (dominatedRetraction u v huv)
      (dominatedRetraction_adj_or_eq G u v huv hN) p
    let q' : (deleteVertex G u).Walk a b :=
      q.copy (dominatedRetraction_apply_of_ne huv a.property)
        (dominatedRetraction_apply_of_ne huv b.property)
    calc
      (deleteVertex G u).dist a b ≤ q'.length := SimpleGraph.dist_le q'
      _ = q.length := by simp [q']
      _ ≤ p.length := by
        dsimp [q]
        exact Walk.length_mapAdjOrEq_le (dominatedRetraction u v huv)
          (dominatedRetraction_adj_or_eq G u v huv hN) p
  obtain ⟨q, hq⟩ := hdel_conn.exists_walk_length_eq_dist a b
  let inclusion : deleteVertex G u →g G := {
    toFun := Subtype.val
    map_rel' := by intro a b h; exact h }
  have hle_G : G.dist a.1 b.1 ≤ (deleteVertex G u).dist a b := by
    rw [← hq, ← q.length_map inclusion]
    change G.dist (inclusion a) (inclusion b) ≤ _
    exact SimpleGraph.dist_le (q.map inclusion)
  omega

/-- A vertex dominating `u` in the closed-neighborhood order is no farther
from any surviving vertex than `u` is. -/
theorem dist_dominator_le
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (x : V) (hxu : x ≠ u) : G.dist v x ≤ G.dist u x := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u x
  let q := Walk.mapAdjOrEq (dominatedRetraction u v huv)
    (dominatedRetraction_adj_or_eq G u v huv hN) p
  let q' : (deleteVertex G u).Walk ⟨v, huv.symm⟩ ⟨x, hxu⟩ :=
    q.copy (dominatedRetraction_apply_deleted huv)
      (dominatedRetraction_apply_of_ne huv hxu)
  have hdel := deleteVertex_dist_eq_of_closedNeighborhood_subset
    G hconn u v huv hN ⟨v, huv.symm⟩ ⟨x, hxu⟩
  rw [← hdel, ← hp]
  calc
    _ ≤ q'.length := SimpleGraph.dist_le q'
    _ = q.length := by simp [q']
    _ ≤ p.length := Walk.length_mapAdjOrEq_le _ _ _

/-- For a proper closed-neighborhood containment, the pair consisting of
the dominated vertex and its dominator has zero Szeged--Wiener pair gap. -/
theorem pairGap_dominated_eq_zero
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v) :
    pairGap G u v = 0 := by
  classical
  have huvAdj : G.Adj u v := by
    have hu : u ∈ closedNeighborhood G u := by
      simp [closedNeighborhood, openNeighborhood]
    have hout := hN hu
    have hvu : G.Adj v u := by
      simpa [closedNeighborhood, openNeighborhood, huv, huv.symm] using hout
    exact hvu.symm
  have hgood_iff (e : Sym2 V) : IsGoodEdgeFor G u v e ↔ e = s(u, v) := by
    induction e using Sym2.inductionOn with
    | _ x y =>
      simp only [IsGoodEdgeFor, Sym2.lift_mk]
      constructor
      · rintro ⟨hxy, h | h⟩
        · by_cases hxu : x = u
          · subst x
            have hvy : G.dist v y = 0 := by
              rw [dist_eq_one_iff_adj.mpr huvAdj.symm] at h
              omega
            have hyv : y = v := hconn.dist_eq_zero_iff.mp (by
              simpa [dist_comm] using hvy)
            subst y
            rfl
          · by_cases hyu : y = u
            · subst y
              simp at h
            · have hvx := dist_dominator_le G hconn u v huv hN x hxu
              have hutriangle : G.dist u y ≤ G.dist u v + G.dist v y :=
                hconn.dist_triangle
              rw [dist_eq_one_iff_adj.mpr huvAdj] at hutriangle
              omega
        · by_cases hyu : y = u
          · subst y
            have hvx0 : G.dist v x = 0 := by
              rw [dist_eq_one_iff_adj.mpr huvAdj.symm] at h
              omega
            have hxv : x = v := hconn.dist_eq_zero_iff.mp (by
              simpa [dist_comm] using hvx0)
            subst x
            exact Sym2.eq_swap
          · by_cases hxu : x = u
            · subst x
              simp at h
            · have hvy := dist_dominator_le G hconn u v huv hN y hyu
              have hutriangle : G.dist u x ≤ G.dist u v + G.dist v x :=
                hconn.dist_triangle
              rw [dist_eq_one_iff_adj.mpr huvAdj] at hutriangle
              omega
      · intro he
        rcases Sym2.eq_iff.mp he with he | he
        · rcases he with ⟨rfl, rfl⟩
          refine ⟨huvAdj, Or.inl ?_⟩
          simp [dist_eq_one_iff_adj.mpr huvAdj,
            dist_eq_one_iff_adj.mpr huvAdj.symm]
        · rcases he with ⟨rfl, rfl⟩
          refine ⟨huvAdj.symm, Or.inr ?_⟩
          simp [dist_eq_one_iff_adj.mpr huvAdj,
            dist_eq_one_iff_adj.mpr huvAdj.symm]
  have hfinset : goodEdgeFinset G u v = {s(u, v)} := by
    ext e
    simp only [goodEdgeFinset, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
      Finset.mem_singleton]
    constructor
    · exact fun h => (hgood_iff e).mp h.2
    · intro he
      subst e
      exact ⟨by simpa using huvAdj, (hgood_iff s(u, v)).mpr rfl⟩
  unfold pairGap goodEdgeCount
  rw [hfinset]
  simp [dist_eq_one_iff_adj.mpr huvAdj]

/-- Diagonal unordered pairs make no contribution. -/
theorem pairGap_self
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a : V) : pairGap G a a = 0 := by
  classical
  have hnone : goodEdgeFinset G a a = ∅ := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp [goodEdgeFinset, IsGoodEdgeFor] <;> omega
  unfold pairGap goodEdgeCount
  rw [hnone]
  simp

/-- Every old good edge remains good after restoring a dominated vertex. -/
theorem deleteVertex_goodEdge_maps_to_goodEdge
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (a b : {x : V // x ≠ u})
    (e : Sym2 {x : V // x ≠ u})
    (he : IsGoodEdgeFor (deleteVertex G u) a b e) :
    IsGoodEdgeFor G a.1 b.1 (Sym2.map Subtype.val e) := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [Sym2.map_pair_eq]
      simp only [IsGoodEdgeFor, Sym2.lift_mk] at he ⊢
      rcases he with ⟨hxy, hgood⟩
      refine ⟨hxy, ?_⟩
      have haa := deleteVertex_dist_eq_of_closedNeighborhood_subset
        G hconn u v huv hN a x
      have hay := deleteVertex_dist_eq_of_closedNeighborhood_subset
        G hconn u v huv hN a y
      have hby := deleteVertex_dist_eq_of_closedNeighborhood_subset
        G hconn u v huv hN b y
      have hbx := deleteVertex_dist_eq_of_closedNeighborhood_subset
        G hconn u v huv hN b x
      rcases hgood with hgood | hgood
      · left
        omega
      · right
        omega

/-- Restoring a dominated vertex cannot decrease the pair contribution of a
pair of surviving vertices.  The injection is the literal inclusion of old
good edges; distance preservation supplies the distance term. -/
theorem pairGap_deleteVertex_le
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (a b : {x : V // x ≠ u}) :
    pairGap (deleteVertex G u) a b ≤ pairGap G a.1 b.1 := by
  classical
  let f : Sym2 {x : V // x ≠ u} → Sym2 V := Sym2.map Subtype.val
  have hf : Function.Injective f := by
    dsimp [f]
    exact Sym2.map.injective Subtype.val_injective
  have hmaps :
      (goodEdgeFinset (deleteVertex G u) a b).image f ⊆
        goodEdgeFinset G a.1 b.1 := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
    simp only [goodEdgeFinset, Finset.mem_filter,
      SimpleGraph.mem_edgeFinset] at he' ⊢
    exact ⟨by
      induction e' using Sym2.inductionOn with
      | _ x y => exact he'.1,
      deleteVertex_goodEdge_maps_to_goodEdge G hconn u v huv hN a b e' he'.2⟩
  have hcount : goodEdgeCount (deleteVertex G u) a b ≤
      goodEdgeCount G a.1 b.1 := by
    unfold goodEdgeCount
    rw [← Finset.card_image_iff.mpr hf.injOn]
    exact Finset.card_le_card hmaps
  have hdist := deleteVertex_dist_eq_of_closedNeighborhood_subset
    G hconn u v huv hN a b
  unfold pairGap
  omega

/-- The unordered pairs containing `u` are the image of `a ↦ {u,a}`. -/
private theorem sym2PairsContaining_eq_image
    {V : Type u} [Fintype V] [DecidableEq V] (u : V) :
    (Finset.univ : Finset (Sym2 V)).filter (fun p => u ∈ p) =
      (Finset.univ : Finset V).image (fun a => s(u, a)) := by
  ext p
  induction p using Sym2.inductionOn with
  | _ a b =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff]
      constructor
      · rintro (ha | hb)
        · apply Finset.mem_image.mpr
          refine ⟨b, by simp, ?_⟩
          exact Sym2.eq_iff.mpr (Or.inl ⟨ha, rfl⟩)
        · apply Finset.mem_image.mpr
          refine ⟨a, by simp, ?_⟩
          exact Sym2.eq_iff.mpr (Or.inr ⟨hb, rfl⟩)
      · intro hp
        obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hp
        have hm : u ∈ s(u, x) := by simp
        rw [hx] at hm
        simpa [Sym2.mem_iff] using hm

/-- The unordered pairs avoiding `u` are exactly the images of unordered
pairs in the deleted vertex type. -/
private theorem sym2PairsAvoiding_eq_image
    {V : Type u} [Fintype V] [DecidableEq V] (u : V) :
    (Finset.univ : Finset (Sym2 V)).filter (fun p => u ∉ p) =
      (Finset.univ : Finset (Sym2 {x : V // x ≠ u})).image
        (Sym2.map Subtype.val) := by
  ext p
  induction p using Sym2.inductionOn with
  | _ a b =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Sym2.mem_iff, not_or]
      constructor
      · rintro ⟨ha, hb⟩
        apply Finset.mem_image.mpr
        refine ⟨s(⟨a, Ne.symm ha⟩, ⟨b, Ne.symm hb⟩), by simp, ?_⟩
        simp
      · intro hp
        obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hp
        have havoid : u ∉ Sym2.map Subtype.val q := by
          intro hm
          rw [Sym2.mem_map] at hm
          obtain ⟨x, hx, hxu⟩ := hm
          exact x.2 hxu
        have : u ∉ s(a, b) := by simpa [hq] using havoid
        simpa [Sym2.mem_iff] using this

/-- Restoring a dominated vertex increases the gap by at least the total
contribution of the restored vertex.  This is equation (4) with the
nonnegative `q` term omitted. -/
theorem gap_sub_deleteVertex_ge_vertexContribution
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v) :
    szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥
      vertexContribution G u := by
  classical
  let old : Finset (Sym2 V) :=
    Finset.univ.filter (fun p => u ∉ p)
  let fresh : Finset (Sym2 V) :=
    Finset.univ.filter (fun p => u ∈ p)
  let f : Sym2 {x : V // x ≠ u} → Sym2 V := Sym2.map Subtype.val
  have hf : Function.Injective f := by
    dsimp [f]
    exact Sym2.map.injective Subtype.val_injective
  have hold : old = (Finset.univ : Finset (Sym2 {x : V // x ≠ u})).image f := by
    simpa [old, f] using sym2PairsAvoiding_eq_image u
  have hfresh : fresh = (Finset.univ : Finset V).image (fun a => s(u, a)) := by
    simpa [fresh] using sym2PairsContaining_eq_image u
  have hpartition : Disjoint old fresh ∧ old ∪ fresh = Finset.univ := by
    constructor
    · rw [Finset.disjoint_left]
      simp [old, fresh]
    · ext p
      by_cases hp : u ∈ p <;> simp [old, fresh, hp]
  have hold_le :
      (∑ p : Sym2 {x : V // x ≠ u}, pairGapOnPair (deleteVertex G u) p) ≤
        ∑ p ∈ old, pairGapOnPair G p := by
    rw [hold, Finset.sum_image]
    · apply Finset.sum_le_sum
      intro p _
      induction p using Sym2.inductionOn with
      | _ a b =>
          exact pairGap_deleteVertex_le G hconn u v huv hN a b
    · exact fun _ _ _ _ h => hf h
  have hfresh_sum :
      (∑ p ∈ fresh, pairGapOnPair G p) = vertexContribution G u := by
    rw [hfresh, Finset.sum_image]
    · unfold vertexContribution
      rfl
    · intro a _ b _ hab
      exact (Sym2.mkEmbedding u).injective hab
  rw [szegedWienerGap_eq_sum_pairGapOnPair,
    szegedWienerGap_eq_sum_pairGapOnPair]
  have hsplit :
      (∑ p : Sym2 V, pairGapOnPair G p) =
        (∑ p ∈ old, pairGapOnPair G p) +
          ∑ p ∈ fresh, pairGapOnPair G p := by
    rw [← Finset.sum_union hpartition.1, hpartition.2]
  rw [hsplit, hfresh_sum]
  omega

/-- Exact dominated-deletion decomposition: the gap gained after restoring
`u` is its vertex contribution plus the sum of the gains of all surviving
unordered pairs.  This is BKLPS equation (4), with their `q` written as the
literal sum of pair gains. -/
theorem gap_sub_deleteVertex_eq_vertexContribution_add_pairGainSum
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v) :
    szegedWienerGap G - szegedWienerGap (deleteVertex G u) =
      vertexContribution G u +
        ∑ p : Sym2 {x : V // x ≠ u}, (
          pairGapOnPair G (Sym2.map Subtype.val p) -
            pairGapOnPair (deleteVertex G u) p) := by
  classical
  let old : Finset (Sym2 V) := Finset.univ.filter (fun p => u ∉ p)
  let fresh : Finset (Sym2 V) := Finset.univ.filter (fun p => u ∈ p)
  let f : Sym2 {x : V // x ≠ u} → Sym2 V := Sym2.map Subtype.val
  have hf : Function.Injective f :=
    Sym2.map.injective Subtype.val_injective
  have hold : old = (Finset.univ : Finset (Sym2 {x : V // x ≠ u})).image f := by
    simpa [old, f] using sym2PairsAvoiding_eq_image u
  have hfresh : fresh = (Finset.univ : Finset V).image (fun x => s(u, x)) := by
    simpa [fresh] using sym2PairsContaining_eq_image u
  have hpartition : Disjoint old fresh ∧ old ∪ fresh = Finset.univ := by
    constructor
    · rw [Finset.disjoint_left]
      simp [old, fresh]
    · ext p
      by_cases hp : u ∈ p <;> simp [old, fresh, hp]
  have holdSum :
      (∑ p ∈ old, pairGapOnPair G p) =
        ∑ p : Sym2 {x : V // x ≠ u}, pairGapOnPair G (f p) := by
    rw [hold, Finset.sum_image]
    exact fun _ _ _ _ h => hf h
  have hfreshSum :
      (∑ p ∈ fresh, pairGapOnPair G p) = vertexContribution G u := by
    rw [hfresh, Finset.sum_image]
    · rfl
    · intro x _ y _ hxy
      exact (Sym2.mkEmbedding u).injective hxy
  have hsplit :
      (∑ p : Sym2 V, pairGapOnPair G p) =
        (∑ p ∈ old, pairGapOnPair G p) +
          ∑ p ∈ fresh, pairGapOnPair G p := by
    rw [← Finset.sum_union hpartition.1, hpartition.2]
  rw [szegedWienerGap_eq_sum_pairGapOnPair,
    szegedWienerGap_eq_sum_pairGapOnPair, hsplit, holdSum, hfreshSum]
  rw [Finset.sum_sub_distrib]
  ring

/-- Any selected collection of surviving-pair gains may be retained in the
dominated-deletion lower bound; all omitted gains are nonnegative. -/
theorem gap_sub_deleteVertex_ge_vertexContribution_add_pairGainFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (S : Finset (Sym2 {x : V // x ≠ u})) :
    szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥
      vertexContribution G u +
        ∑ p ∈ S, (pairGapOnPair G (Sym2.map Subtype.val p) -
          pairGapOnPair (deleteVertex G u) p) := by
  classical
  let delta : Sym2 {x : V // x ≠ u} → ℤ := fun p =>
    pairGapOnPair G (Sym2.map Subtype.val p) -
      pairGapOnPair (deleteVertex G u) p
  have hdelta (p : Sym2 {x : V // x ≠ u}) : 0 ≤ delta p := by
    induction p using Sym2.inductionOn with
    | _ a b =>
      exact sub_nonneg.mpr (pairGap_deleteVertex_le G hconn u v huv hN a b)
  have hsub : (∑ p ∈ S, delta p) ≤ ∑ p, delta p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro p _ _
    exact hdelta p
  rw [gap_sub_deleteVertex_eq_vertexContribution_add_pairGainSum
    G hconn u v huv hN]
  dsimp [delta] at hsub ⊢
  omega

/-- A sharpened form of the preceding inequality which retains the gain of
one specified surviving pair. -/
theorem gap_sub_deleteVertex_ge_vertexContribution_add_pairGain
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (u v : V) (huv : u ≠ v)
    (hN : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (a b : {x : V // x ≠ u}) :
    szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥
      vertexContribution G u +
        (pairGap G a.1 b.1 - pairGap (deleteVertex G u) a b) := by
  classical
  let old : Finset (Sym2 V) := Finset.univ.filter (fun p => u ∉ p)
  let fresh : Finset (Sym2 V) := Finset.univ.filter (fun p => u ∈ p)
  let f : Sym2 {x : V // x ≠ u} → Sym2 V := Sym2.map Subtype.val
  let delta : Sym2 {x : V // x ≠ u} → ℤ := fun p =>
    pairGapOnPair G (f p) - pairGapOnPair (deleteVertex G u) p
  have hf : Function.Injective f := by
    dsimp [f]
    exact Sym2.map.injective Subtype.val_injective
  have hold : old = (Finset.univ : Finset (Sym2 {x : V // x ≠ u})).image f := by
    simpa [old, f] using sym2PairsAvoiding_eq_image u
  have hfresh : fresh = (Finset.univ : Finset V).image (fun x => s(u, x)) := by
    simpa [fresh] using sym2PairsContaining_eq_image u
  have hpartition : Disjoint old fresh ∧ old ∪ fresh = Finset.univ := by
    constructor
    · rw [Finset.disjoint_left]
      simp [old, fresh]
    · ext p
      by_cases hp : u ∈ p <;> simp [old, fresh, hp]
  have hold_sum :
      (∑ p ∈ old, pairGapOnPair G p) =
        ∑ p : Sym2 {x : V // x ≠ u}, pairGapOnPair G (f p) := by
    rw [hold, Finset.sum_image]
    exact fun _ _ _ _ h => hf h
  have hfresh_sum :
      (∑ p ∈ fresh, pairGapOnPair G p) = vertexContribution G u := by
    rw [hfresh, Finset.sum_image]
    · unfold vertexContribution
      rfl
    · intro x _ y _ hxy
      exact (Sym2.mkEmbedding u).injective hxy
  have hdelta_nonneg (p : Sym2 {x : V // x ≠ u}) : 0 ≤ delta p := by
    induction p using Sym2.inductionOn with
    | _ x y =>
        exact sub_nonneg.mpr (pairGap_deleteVertex_le G hconn u v huv hN x y)
  let selected : Sym2 {x : V // x ≠ u} := s(a, b)
  have hselected : selected ∈ (Finset.univ : Finset (Sym2 {x : V // x ≠ u})) := by
    simp
  have hrest : 0 ≤
      ∑ p ∈ (Finset.univ : Finset (Sym2 {x : V // x ≠ u})).erase selected,
        delta p := by
    exact Finset.sum_nonneg fun p hp => hdelta_nonneg p
  have hselected_le : delta selected ≤
      ∑ p : Sym2 {x : V // x ≠ u}, delta p := by
    rw [← Finset.sum_erase_add _ _ hselected]
    omega
  have hdelta_sum :
      (∑ p : Sym2 {x : V // x ≠ u}, pairGapOnPair G (f p)) -
          (∑ p : Sym2 {x : V // x ≠ u},
            pairGapOnPair (deleteVertex G u) p) =
        ∑ p : Sym2 {x : V // x ≠ u}, delta p := by
    rw [Finset.sum_sub_distrib]
  have hsplit :
      (∑ p : Sym2 V, pairGapOnPair G p) =
        (∑ p ∈ old, pairGapOnPair G p) +
          ∑ p ∈ fresh, pairGapOnPair G p := by
    rw [← Finset.sum_union hpartition.1, hpartition.2]
  rw [szegedWienerGap_eq_sum_pairGapOnPair,
    szegedWienerGap_eq_sum_pairGapOnPair, hsplit, hold_sum, hfresh_sum]
  have hsel_value : delta selected =
      pairGap G a.1 b.1 - pairGap (deleteVertex G u) a b := by
    rfl
  rw [← hdelta_sum, hsel_value] at hselected_le
  omega

end BKLPS.External
