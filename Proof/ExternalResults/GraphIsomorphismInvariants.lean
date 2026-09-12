import Proof.Definitions

/-!
Isomorphism invariance of the distances and indices used in the manuscript.
These are general graph-theoretic transport results, not assumptions from BKLPS.
-/

namespace BKLPS.External

open SimpleGraph
open scoped BigOperators

noncomputable section

universe u v

variable {V : Type u} {W : Type v}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- Relabeling commutes with deleting a vertex. -/
def deleteVertexIso (e : G ≃g H) (a : V) :
    deleteVertex G a ≃g deleteVertex H (e a) where
  toEquiv :=
    { toFun := fun x => ⟨e x.1, by
        intro h
        exact x.2 (e.injective h)⟩
      invFun := fun y => ⟨e.symm y.1, by
        intro h
        exact y.2 (by simpa using congrArg e h)⟩
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp }
  map_rel_iff' := by
    intro x y
    exact e.map_rel_iff

/-- Two-connectivity is invariant under graph isomorphism. -/
theorem isoIsTwoConnected (e : G ≃g H) :
    IsTwoConnected G ↔ IsTwoConnected H := by
  constructor
  · rintro ⟨hcard, hconn, hdelete⟩
    refine ⟨by rw [← e.card_eq]; exact hcard, e.connected_iff.mp hconn, ?_⟩
    intro w
    let a : V := e.symm w
    have hc := (deleteVertexIso e a).connected_iff.mp (hdelete a)
    rw [← show e a = w by simp [a]]
    exact hc
  · rintro ⟨hcard, hconn, hdelete⟩
    refine ⟨by rw [e.card_eq]; exact hcard, e.connected_iff.mpr hconn, ?_⟩
    intro a
    exact (deleteVertexIso e a).connected_iff.mpr (hdelete (e a))

/-- Being complete up to isomorphism is invariant under relabeling. -/
theorem isoIsomorphicToKn (e : G ≃g H) :
    IsomorphicToKn G ↔ IsomorphicToKn H := by
  unfold IsomorphicToKn
  rw [← e.card_eq]
  constructor
  · rintro ⟨f⟩
    exact ⟨f.comp e.symm⟩
  · rintro ⟨f⟩
    exact ⟨f.comp e⟩

/-- Being one of the canonical `K_n^t` graphs is invariant under
relabeling. -/
theorem isoIsomorphicToKnt (e : G ≃g H) (t : ℕ) :
    IsomorphicToKnt G t ↔ IsomorphicToKnt H t := by
  unfold IsomorphicToKnt
  rw [← e.card_eq]
  constructor
  · rintro ⟨f⟩
    exact ⟨f.comp e.symm⟩
  · rintro ⟨f⟩
    exact ⟨f.comp e⟩

/-- Being isomorphic to a specified cycle is invariant under relabeling. -/
theorem isoIsomorphicToCn (e : G ≃g H) (n : ℕ) :
    IsomorphicToCn G n ↔ IsomorphicToCn H n := by
  unfold IsomorphicToCn
  constructor
  · rintro ⟨f⟩
    exact ⟨f.comp e.symm⟩
  · rintro ⟨f⟩
    exact ⟨f.comp e⟩

/-- Membership in a closed neighborhood is preserved by a graph
isomorphism. -/
theorem isoMemClosedNeighborhood (e : G ≃g H) (a x : V) :
    e x ∈ closedNeighborhood H (e a) ↔ x ∈ closedNeighborhood G a := by
  simp [closedNeighborhood, openNeighborhood, e.map_adj_iff]

/-- In particular, closed-neighborhood containment is independent of the
chosen vertex labels. -/
theorem isoClosedNeighborhoodSubset (e : G ≃g H) (a b : V) :
    closedNeighborhood G a ⊆ closedNeighborhood G b ↔
      closedNeighborhood H (e a) ⊆ closedNeighborhood H (e b) := by
  constructor
  · intro h y hy
    let x : V := e.symm y
    have hx : x ∈ closedNeighborhood G a :=
      (isoMemClosedNeighborhood e a x).mp (by simpa [x] using hy)
    have hout := (isoMemClosedNeighborhood e b x).mpr (h hx)
    simpa [x] using hout
  · intro h x hx
    exact (isoMemClosedNeighborhood e b x).mp
      (h ((isoMemClosedNeighborhood e a x).mpr hx))

/-- Exceptional and unexceptional status do not depend on vertex labels. -/
theorem isoIsExceptional (e : G ≃g H) :
    IsExceptional G ↔ IsExceptional H := by
  unfold IsExceptional
  rw [← e.card_eq, isoIsomorphicToKn e,
    isoIsomorphicToKnt e 2, isoIsomorphicToKnt e (Fintype.card V - 2)]

theorem isoIsUnexceptional (e : G ≃g H) :
    IsUnexceptional G ↔ IsUnexceptional H := by
  unfold IsUnexceptional
  exact not_congr (isoIsExceptional e)

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
/-- A graph isomorphism preserves graph distance. -/
theorem isoDist (e : G ≃g H) (a b : V) :
    H.dist (e a) (e b) = G.dist a b := by
  by_cases h_reachable : G.Reachable a b
  · have h_image_reachable : H.Reachable (e a) (e b) := e.reachable_iff.mpr h_reachable
    apply Nat.le_antisymm
    · obtain ⟨p, hp⟩ := h_reachable.exists_walk_length_eq_dist
      calc
        H.dist (e a) (e b) ≤ (p.map e.toHom).length := H.dist_le _
        _ = p.length := Walk.length_map e.toHom p
        _ = G.dist a b := hp
    · obtain ⟨p, hp⟩ := h_image_reachable.exists_walk_length_eq_dist
      have h_bound := G.dist_le (p.map e.symm.toHom)
      simpa [hp] using h_bound
  · have h_image_not_reachable : ¬H.Reachable (e a) (e b) := by
      intro h_image
      exact h_reachable (e.reachable_iff.mp h_image)
    rw [G.dist_eq_zero_of_not_reachable h_reachable,
      H.dist_eq_zero_of_not_reachable h_image_not_reachable]

/-- A graph isomorphism preserves the cardinalities `n_ab(a)`. -/
theorem isoCloserCount (e : G ≃g H) (a b : V) :
    closerCount H (e a) (e b) = closerCount G a b := by
  classical
  have h_map :
      (closerVertices G a b).map e.toEquiv.toEmbedding =
        closerVertices H (e a) (e b) := by
    ext y
    constructor
    · simp only [Finset.mem_map]
      rintro ⟨x, hx, rfl⟩
      simpa [closerVertices, isoDist e] using hx
    · intro hy
      simp only [Finset.mem_map]
      refine ⟨e.symm y, ?_, by simp⟩
      have h_left := isoDist e (e.symm y) a
      have h_right := isoDist e (e.symm y) b
      simp only [RelIso.apply_symm_apply] at h_left h_right
      simp only [closerVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rwa [h_left, h_right] at hy
  unfold closerCount
  rw [← h_map, Finset.card_map]

/-- The unordered-pair contribution to the Szeged index is invariant under
an isomorphism. -/
theorem isoSzegedContribution (e : G ≃g H) (p : Sym2 V) :
    szegedContribution H (p.map e) = szegedContribution G p := by
  induction p using Sym2.inductionOn with
  | _ a b =>
      simp [szegedContribution, isoCloserCount e]

/-- The equivalence on unordered vertex pairs induced by a vertex equivalence. -/
def sym2Equiv (e : V ≃ W) : Sym2 V ≃ Sym2 W where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv p := by
    rw [Sym2.map_map]
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using congr_fun Sym2.map_id p
  right_inv p := by
    rw [Sym2.map_map]
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using congr_fun Sym2.map_id p

/-- The Wiener index is invariant under graph isomorphism. -/
theorem isoWienerIndex (e : G ≃g H) : wienerIndex H = wienerIndex G := by
  unfold wienerIndex
  symm
  apply Fintype.sum_equiv (sym2Equiv e.toEquiv)
  intro p
  induction p using Sym2.inductionOn with
  | _ a b => simp [sym2Equiv, isoDist e]

/-- The Szeged index is invariant under graph isomorphism. -/
theorem isoSzegedIndex (e : G ≃g H) : szegedIndex H = szegedIndex G := by
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  letI : Fintype H.edgeSet := Fintype.ofFinite _
  classical
  unfold szegedIndex
  symm
  apply Fintype.sum_equiv e.mapEdgeSet
  intro edge
  exact (isoSzegedContribution e edge.1).symm

/-- The Szeged--Wiener gap is invariant under graph isomorphism. -/
theorem isoSzegedWienerGap (e : G ≃g H) :
    szegedWienerGap H = szegedWienerGap G := by
  simp only [szegedWienerGap, isoSzegedIndex e, isoWienerIndex e]

/-- A finite verification on the canonical vertex type `Fin n` transfers to
every finite type of cardinality `n`. -/
theorem finiteUnexceptionalCheckOfFin
    {n : ℕ} (G : SimpleGraph V) (hcard : Fintype.card V = n)
    (bound : ℤ)
    (hcheck : ∀ K : SimpleGraph (Fin n),
      IsTwoConnected K → IsUnexceptional K → szegedWienerGap K ≥ bound)
    (htwo : IsTwoConnected G) (hunexceptional : IsUnexceptional G) :
    szegedWienerGap G ≥ bound := by
  let e := G.overFinIso hcard
  have htwo' : IsTwoConnected (G.overFin hcard) :=
    (isoIsTwoConnected e).mp htwo
  have hunexceptional' : IsUnexceptional (G.overFin hcard) :=
    (isoIsUnexceptional e).mp hunexceptional
  have hbound := hcheck (G.overFin hcard) htwo' hunexceptional'
  rw [isoSzegedWienerGap e] at hbound
  exact hbound

end

end BKLPS.External
