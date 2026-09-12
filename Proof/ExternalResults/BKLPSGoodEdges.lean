import Proof.Definitions
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/- oh yeah this includes proposition 6 of BKLPS -/

/-!
The elementary good-edge facts used throughout BKLPS: the edges of a
geodesic are good, and consequently every pair contribution is nonnegative.
-/

namespace BKLPS.External

open SimpleGraph

noncomputable section

universe u

/-- Along an oriented geodesic, distance from the initial endpoint strictly
increases and distance from the terminal endpoint strictly decreases at every
dart. -/
lemma geodesicDartGood
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.length = G.dist a b) :
    ∀ d ∈ p.darts,
      G.dist a d.fst < G.dist a d.snd ∧
        G.dist b d.snd < G.dist b d.fst := by
  induction p with
  | nil => simp
  | @cons a x b h q ih =>
      intro d hd
      have hqgeo : q.length = G.dist x b :=
        length_eq_dist_of_subwalk hp (Walk.isSubwalk_cons q h)
      simp only [Walk.darts_cons, List.mem_cons] at hd
      rcases hd with rfl | hd
      · dsimp
        have hax : G.dist a x = 1 := dist_eq_one_iff_adj.mpr h
        have hbx : G.dist b x = q.length := by
          rw [dist_comm, ← hqgeo]
        have hba : G.dist b a = q.length + 1 := by
          rw [dist_comm, ← hp]
          simp
        rw [SimpleGraph.dist_self]
        omega
      · have hi := ih hqgeo d hd
        have hfst : d.fst ∈ q.support :=
          q.dart_fst_mem_support_of_mem_darts hd
        have hsnd : d.snd ∈ q.support :=
          q.dart_snd_mem_support_of_mem_darts hd
        have start_dist (y : V) (hy : y ∈ q.support) :
            G.dist a y = G.dist x y + 1 := by
          have hprefix_q :
              (q.takeUntil y hy).length = G.dist x y :=
            length_eq_dist_of_subwalk hqgeo (q.isSubwalk_takeUntil hy)
          have hprefix_p :
              ((q.takeUntil y hy).cons h).length = G.dist a y :=
            length_eq_dist_of_subwalk hp (by
              refine ⟨Walk.nil, q.dropUntil y hy, ?_⟩
              simp only [Walk.nil_append, Walk.cons_append, q.take_spec hy])
          simp only [Walk.length_cons] at hprefix_p
          omega
        rw [start_dist d.fst hfst, start_dist d.snd hsnd]
        exact ⟨by omega, hi.2⟩

/-- Every edge of a shortest path is good for its endpoints. -/
lemma geodesicEdgeGood
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.length = G.dist a b)
    (e : Sym2 V) (he : e ∈ p.edges) : IsGoodEdgeFor G a b e := by
  rw [Walk.edges] at he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  have hg := geodesicDartGood p hp d hd
  rcases d with ⟨⟨x, y⟩, hxy⟩
  exact ⟨hxy, Or.inl hg⟩

/-- The good-edge count dominates distance in a connected graph. -/
theorem goodEdgeCount_ge_dist
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (a b : V) :
    goodEdgeCount G a b ≥ G.dist a b := by
  classical
  obtain ⟨p, hpath, hp⟩ := hconn.exists_path_of_dist a b
  have hsubset : p.edges.toFinset ⊆ goodEdgeFinset G a b := by
    intro e he
    rw [List.mem_toFinset] at he
    simp only [goodEdgeFinset, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
    exact ⟨p.edges_subset_edgeSet he, geodesicEdgeGood p hp e he⟩
  calc
    G.dist a b = p.length := hp.symm
    _ = p.edges.length := p.length_edges.symm
    _ = p.edges.toFinset.card :=
      (List.toFinset_card_of_nodup hpath.isTrail.edges_nodup).symm
    _ ≤ (goodEdgeFinset G a b).card := Finset.card_le_card hsubset
    _ = goodEdgeCount G a b := rfl

/-- Every pair contribution is nonnegative in a connected graph. -/
theorem pairGap_nonneg
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (a b : V) :
    pairGap G a b ≥ 0 := by
  unfold pairGap
  exact sub_nonneg.mpr (by exact_mod_cast goodEdgeCount_ge_dist G hconn a b)

end

end BKLPS.External


/-!
# The good-edge double count

This file formalizes BKLPS Proposition 6.  The proof counts incidences
`(unordered vertex pair, good edge)` in the two possible orders.
-/

namespace BKLPS.External

open SimpleGraph
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 1000000

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The relation used in the double count: `e` is good for the unordered
vertex pair `p`. -/
private def IsGoodPairForEdge (G : SimpleGraph V) (p e : Sym2 V) : Prop :=
  Sym2.lift ⟨fun a b => IsGoodEdgeFor G a b e, by
    intro a b
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp only [IsGoodEdgeFor, Sym2.lift_mk]
        aesop⟩ p

private noncomputable def goodPairsForEdgeFinset
    (G : SimpleGraph V) (e : Sym2 V) : Finset (Sym2 V) :=
  by
    classical
    exact Finset.univ.filter fun p => IsGoodPairForEdge G p e

private noncomputable def goodEdgesForPairFinset
    (G : SimpleGraph V) (p : Sym2 V) : Finset (Sym2 V) :=
  by
    classical
    letI : Fintype G.edgeSet := Fintype.ofFinite _
    exact G.edgeFinset.filter fun e => IsGoodPairForEdge G p e

private theorem closerVertices_disjoint (G : SimpleGraph V) (x y : V) :
    Disjoint (closerVertices G x y) (closerVertices G y x) := by
  rw [Finset.disjoint_left]
  intro z hzx hzy
  simp only [closerVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hzx hzy
  omega

/-- For a fixed edge `xy`, the unordered pairs for which it is good are
exactly the pairs with one endpoint strictly closer to `x` and the other
strictly closer to `y`. -/
private theorem card_goodPairs_for_edge (G : SimpleGraph V) (x y : V)
    (hxy : G.Adj x y) :
    (goodPairsForEdgeFinset G s(x, y)).card =
      closerCount G x y * closerCount G y x := by
  classical
  let A := closerVertices G x y
  let B := closerVertices G y x
  let f : V × V → Sym2 V := fun p => s(p.1, p.2)
  have hdisj : Disjoint A B := closerVertices_disjoint G x y
  have hinj : Set.InjOn f (A.product B : Set (V × V)) := by
    intro p hp q hq hpq
    have hp' := Finset.mem_product.mp hp
    have hq' := Finset.mem_product.mp hq
    rcases (Sym2.eq_iff.mp hpq) with hsame | hswap
    · exact Prod.ext hsame.1 hsame.2
    · exfalso
      exact (Finset.disjoint_left.mp hdisj) hp'.1 (hswap.1 ▸ hq'.2)
  have hfiber :
      goodPairsForEdgeFinset G s(x, y) =
        (A.product B).image f := by
    ext p
    induction p using Sym2.inductionOn with
    | _ a b =>
        simp only [goodPairsForEdgeFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        simp [IsGoodPairForEdge, IsGoodEdgeFor, A, B, f, closerVertices,
          hxy, Sym2.eq_iff]
        aesop
  rw [hfiber, Finset.card_image_iff.mpr hinj]
  simp [A, B, closerCount]

private theorem goodEdgeCountOnPair_eq_card (G : SimpleGraph V) (p : Sym2 V) :
    goodEdgeCountOnPair G p =
      (goodEdgesForPairFinset G p).card := by
  classical
  induction p using Sym2.inductionOn with
  | _ a b =>
      unfold goodEdgesForPairFinset goodEdgeCountOnPair goodEdgeCount
      rfl

/-- BKLPS equation (1): the Szeged index is the sum of the numbers of good
edges over all unordered vertex pairs. -/
theorem szegedIndex_eq_sum_goodEdgeCountOnPair (G : SimpleGraph V) :
    szegedIndex G = ∑ p : Sym2 V, goodEdgeCountOnPair G p := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  change szegedIndex G =
    ∑ p ∈ (Finset.univ : Finset (Sym2 V)), goodEdgeCountOnPair G p
  simp_rw [goodEdgeCountOnPair_eq_card]
  have hfilter (p : Sym2 V) :
      (goodEdgesForPairFinset G p).card =
        ∑ e ∈ G.edgeFinset, if IsGoodPairForEdge G p e then 1 else 0 := by
    unfold goodEdgesForPairFinset
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [hfilter]
  rw [Finset.sum_comm]
  unfold szegedIndex
  rw [← Finset.sum_subtype G.edgeFinset (fun e => SimpleGraph.mem_edgeFinset)]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : G.Adj x y := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      rw [show szegedContribution G s(x, y) =
          closerCount G x y * closerCount G y x by rfl]
      rw [← card_goodPairs_for_edge G x y hxy, Finset.card_eq_sum_ones]
      unfold goodPairsForEdgeFinset
      rw [Finset.sum_filter]

/-- BKLPS Proposition 6: the Szeged--Wiener gap is the sum of the pair
contributions over unordered vertex pairs. -/
theorem szegedWienerGap_eq_sum_pairGapOnPair (G : SimpleGraph V) :
    szegedWienerGap G = ∑ p : Sym2 V, pairGapOnPair G p := by
  let d : Sym2 V → ℕ :=
    Sym2.lift ⟨G.dist, fun a b => dist_comm (G := G) (u := a) (v := b)⟩
  unfold szegedWienerGap
  rw [szegedIndex_eq_sum_goodEdgeCountOnPair]
  unfold wienerIndex
  change (↑(∑ p : Sym2 V, goodEdgeCountOnPair G p) : ℤ) -
      ↑(∑ p : Sym2 V, d p) = ∑ p : Sym2 V, pairGapOnPair G p
  calc
    (↑(∑ p : Sym2 V, goodEdgeCountOnPair G p) : ℤ) -
        ↑(∑ p : Sym2 V, d p) =
      (∑ p : Sym2 V, (goodEdgeCountOnPair G p : ℤ)) -
        ∑ p : Sym2 V, (d p : ℤ) := by
            simp only [Nat.cast_sum]
    _ = ∑ p : Sym2 V, ((goodEdgeCountOnPair G p : ℤ) -
          (d p : ℤ)) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ p : Sym2 V, pairGapOnPair G p := by
      apply Fintype.sum_congr
      intro p
      induction p using Sym2.inductionOn with
      | _ a b => rfl

/-- BKLPS equation (3), in denominator-free form: summing all vertex
contributions counts every unordered pair contribution twice. -/
theorem sum_vertexContribution_eq_two_mul_gap (G : SimpleGraph V) :
    (∑ a : V, vertexContribution G a) = 2 * szegedWienerGap G := by
  classical
  letI : LinearOrder V :=
    LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  let f : Sym2 V → ℤ := pairGapOnPair G
  let U : Finset V := Finset.univ
  let O : Finset (V × V) := U.offDiag
  let L : Finset (V × V) := O.filter fun q => q.1 < q.2
  let R : Finset (V × V) := O.filter fun q => ¬q.1 < q.2
  have hdiag (a : V) : f s(a, a) = 0 := by
    change (goodEdgeCount G a a : ℤ) - G.dist a a = 0
    simp only [SimpleGraph.dist_self, Nat.cast_zero, sub_zero]
    norm_cast
    unfold goodEdgeCount goodEdgeFinset
    rw [Finset.card_eq_zero]
    ext e
    constructor
    · intro he
      simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
      induction e using Sym2.inductionOn with
      | _ x y =>
          simp only [IsGoodEdgeFor, Sym2.lift_mk] at he
          omega
    · intro he
      simp at he
  have hswap (a b : V) : f s(a, b) = f s(b, a) := by
    rw [Sym2.eq_swap]
  have hLR : (∑ q ∈ R, f s(q.1, q.2)) = ∑ q ∈ L, f s(q.1, q.2) := by
    apply Finset.sum_equiv (Equiv.prodComm V V)
    · intro q
      simp only [R, L, Finset.mem_filter, O, Finset.mem_offDiag, U,
        Finset.mem_univ, true_and, Equiv.prodComm_apply]
      constructor
      · rintro ⟨hne, hnlt⟩
        exact ⟨hne.symm, lt_of_le_of_ne (le_of_not_gt hnlt) hne.symm⟩
      · rintro ⟨hne, hlt⟩
        exact ⟨hne.symm, not_lt_of_ge hlt.le⟩
    · intro q _
      exact hswap q.1 q.2
  have hoffdiag :
      (∑ q ∈ O, f s(q.1, q.2)) = 2 * (∑ q ∈ L, f s(q.1, q.2)) := by
    have hpartition :=
      Finset.sum_filter_add_sum_filter_not O (fun q : V × V => q.1 < q.2)
        (fun q => f s(q.1, q.2))
    change (∑ q ∈ L, f s(q.1, q.2)) +
        (∑ q ∈ R, f s(q.1, q.2)) =
        ∑ q ∈ O, f s(q.1, q.2) at hpartition
    rw [hLR] at hpartition
    omega
  have hordered :
      (∑ a : V, ∑ b : V, f s(a, b)) = ∑ q ∈ O, f s(q.1, q.2) := by
    change (∑ a ∈ U, ∑ b ∈ U, f s(a, b)) = _
    rw [← Finset.sum_product']
    change (∑ q ∈ U.product U, f s(q.1, q.2)) = _
    have hunion : U.diag ∪ U.offDiag = U.product U :=
      Finset.diag_union_offDiag U
    rw [← hunion]
    rw [Finset.sum_union (Finset.disjoint_diag_offDiag U)]
    rw [Finset.sum_diag]
    simp only [hdiag, Finset.sum_const_zero, zero_add]
    rfl
  have hsym_no_diag :
      (∑ p : Sym2 V, f p) =
        ∑ p ∈ (Finset.univ : Finset V).sym2 with ¬p.IsDiag, f p := by
    have hfull : (Finset.univ : Finset V).sym2 =
        (Finset.univ : Finset (Sym2 V)) :=
      Finset.sym2_univ (inst := inferInstance)
    rw [hfull]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p _ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hp
    induction p using Sym2.inductionOn with
    | _ a b =>
        simp only [Sym2.isDiag_iff_proj_eq] at hp
        subst b
        exact hdiag a
  have hsym_upper :
      (∑ p ∈ (Finset.univ : Finset V).sym2 with ¬p.IsDiag, f p) =
        ∑ q ∈ L, f s(q.1, q.2) := by
    dsimp [L, O, U]
    convert Finset.sum_sym2_filter_not_isDiag (Finset.univ : Finset V) f using 1 <;>
      apply Finset.sum_congr
    all_goals
      first
      | rfl
      | ext p; simp
      | intro p hp; rfl
  unfold vertexContribution
  change (∑ a : V, ∑ b : V, f s(a, b)) = 2 * szegedWienerGap G
  rw [hordered, hoffdiag, ← hsym_upper, ← hsym_no_diag,
    ← szegedWienerGap_eq_sum_pairGapOnPair]

end

end BKLPS.External
