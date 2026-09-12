import Proof.Definitions
import Proof.ExternalResults.BKLPSLemma7
import Proof.ExternalResults.BlockStructure
import Proof.Lemma2ExceptionalCones
import Proof.ExternalResults.BKLPSLemma7GoodsLowerBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.RingNF

/-! The `G-u ≅ K_(n-1)^2` case of the exceptional-deletion proof. -/

namespace BKLPS

open SimpleGraph

noncomputable section

universe u

/-- Numerical end of Subcase 1a, with
`a = n-2-s` and `b = s-1`. -/
theorem lemma2Subcase1aArithmetic (n s : ℤ)
    (hn : n ≥ 6) (hs₀ : s ≥ 2) (hs₁ : s ≤ n - 3) :
    2 * (n - 2 - s) * (s - 1) ≥ n - 2 := by
  have hprod : 0 ≤ (n - 3 - s) * (s - 2) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

/-- Numerical end of the `T ≠ ∅` part of Subcase 1b. -/
theorem lemma2Subcase1bNonemptyArithmetic (n t : ℤ)
    (hn : n ≥ 6) (ht₀ : t ≥ 1) (ht₁ : t ≤ n - 4) :
    2 * t * (n - 3 - t) ≥ n - 2 := by
  have hprod : 0 ≤ (t - 1) * (n - 4 - t) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

/-- Numerical finish of the last `S = {z,a}` or `S = {z,b}` case. -/
theorem lemma2Subcase1bTwoNeighborsArithmetic (n : ℤ) :
    2 + (n - 4) = n - 2 := by
  ring

/-- `S = N_G(u)` in the proof of Exceptional Deletion. -/
def lemma2S
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) : Finset V :=
  openNeighborhood G u

/-- The manuscript's `p_x`, counting neighbors of `x` which are closer to
`u` than `x` is. -/
def lemma2Px
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u x : V) : ℕ :=
  ((openNeighborhood G x).filter fun w => G.dist u w < G.dist u x).card

/-- Case 1 of Lemma 2, including the `z ∉ S` and `z ∈ S` subcases. -/
theorem lemma2Proof2
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_order : Fintype.card V ≥ 6)
    (h_unexceptional : IsUnexceptional G)
    (h_two_connected : IsTwoConnected G)
    (u v : V) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete : IsomorphicToKnt (deleteVertex G u) 2) :
    szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥
      (Fintype.card V : ℤ) - 2 := by
  /-
  This is Case 1 of the manuscript.  Under an isomorphism
  `G-u ≅ K_(n-1)^2`, let `z` be the degree-two vertex, let its two neighbors
  be `a,b`, put `R = V(G-u) \ {z,a,b}`, and use `lemma2S G u` for `S`.

  The proof splits on `z ∈ S`; the latter branch splits again on
  `T = R ∩ S` being empty.  The three resulting estimates are
  `2(n-2-s)(s-1)`, `2t(n-3-t)`, and `2+(n-4)`, each at least `n-2`.
  -/
  classical
  have hcardDelete : Fintype.card {x : V // x ≠ u} =
      Fintype.card V - 1 := by
    simpa using Fintype.card_subtype_compl (fun x : V => x = u)
  let m := Fintype.card {x : V // x ≠ u}
  have hm : 5 ≤ m := by omega
  letI : NeZero m := ⟨by omega⟩
  have hdelete' : Nonempty (deleteVertex G u ≃g Knt m 2) := by
    simpa [m] using h_delete
  obtain ⟨e⟩ := hdelete'
  let old : Fin m → V := fun x => (e.symm x).1
  have hold_ne (x : Fin m) : old x ≠ u := (e.symm x).2
  have hold_inj : Function.Injective old := by
    intro x y h
    apply e.symm.injective
    apply Subtype.ext
    exact h
  have holdAdj (x y : Fin m) :
      (Knt m 2).Adj x y ↔ G.Adj (old x) (old y) := by
    have h := e.map_rel_iff (a := e.symm x) (b := e.symm y)
    simpa [old, deleteVertex] using h
  let z : Fin m := ⟨0, by omega⟩
  let a : Fin m := ⟨1, by omega⟩
  let b : Fin m := ⟨2, by omega⟩
  have hza : (Knt m 2).Adj z a := by simp [Knt, z, a]
  have hzb : (Knt m 2).Adj z b := by simp [Knt, z, b]
  have hab : (Knt m 2).Adj a b := by simp [Knt, a, b]
  have hz_ne_a : z ≠ a := hza.ne
  have hz_ne_b : z ≠ b := hzb.ne
  have ha_ne_b : a ≠ b := hab.ne
  have hzNeighbors (x : Fin m) (hx : (Knt m 2).Adj z x) :
      x = a ∨ x = b := by
    have hx' : z ≠ x ∧ (x.val ≤ 2 ∨ x.val = 0) := by
      simpa [Knt, z] using hx
    have hxv : x.val ≠ 0 ∧ x.val ≤ 2 := by
      constructor
      · intro hzero
        exact hx'.1 (Fin.ext (by simpa [z] using hzero.symm))
      · rcases hx'.2 with h | h
        · exact h
        · exact False.elim (hx'.1 (Fin.ext (by simpa [z] using h.symm)))
    have hxval : x.val = 1 ∨ x.val = 2 := by omega
    rcases hxval with h | h
    · left; apply Fin.ext; simpa [a] using h
    · right; apply Fin.ext; simpa [b] using h
  have hclique (x y : Fin m) (hx : x ≠ z) (hy : y ≠ z)
      (hxy : x ≠ y) : (Knt m 2).Adj x y := by
    have hx0 : x.val ≠ 0 := by
      intro h
      exact hx (Fin.ext (by simpa [z] using h))
    have hy0 : y.val ≠ 0 := by
      intro h
      exact hy (Fin.ext (by simpa [z] using h))
    exact ⟨hxy, Or.inl ⟨hx0, hy0⟩⟩
  let R : Finset (Fin m) := Finset.univ \ {z, a, b}
  have hRcard : R.card = m - 3 := by
    rw [show R = Finset.univ \ {z, a, b} by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hz_ne_a, hz_ne_b, ha_ne_b]
  have hRmem (x : Fin m) (hx : x ∈ R) :
      x ≠ z ∧ x ≠ a ∧ x ≠ b := by
    simpa [R] using hx
  let S : Finset (Fin m) := Finset.univ.filter fun x => G.Adj u (old x)
  let s := S.card
  have hmemS (x : Fin m) : x ∈ S ↔ G.Adj u (old x) := by simp [S]
  obtain ⟨p, q, hpq, hup, huq⟩ :=
    External.exists_two_neighbors_of_twoConnected G h_two_connected u
  have hpu : p ≠ u := hup.ne.symm
  have hqu : q ≠ u := huq.ne.symm
  let pe : Fin m := e ⟨p, hpu⟩
  let qe : Fin m := e ⟨q, hqu⟩
  have hpeS : pe ∈ S := by simp [pe, S, old, hup]
  have hqeS : qe ∈ S := by simp [qe, S, old, huq]
  have hpe_ne_qe : pe ≠ qe := by
    intro h
    apply hpq
    have := e.injective h
    exact congrArg Subtype.val this
  have hsLower : 2 ≤ s := by
    have hsub : ({pe, qe} : Finset (Fin m)) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hpeS
      · exact hqeS
    have hc := Finset.card_le_card hsub
    simpa [s, hpe_ne_qe] using hc
  have hcardV : Fintype.card V = m + 1 := by omega
  have hdistTwoOfParent (x y : Fin m) (hxS : x ∉ S) (hyS : y ∈ S)
      (hxy : (Knt m 2).Adj x y) : G.dist u (old x) = 2 := by
    have hxyG := (holdAdj x y).mp hxy
    have huy : G.Adj u (old y) := (hmemS y).mp hyS
    have hle : G.dist u (old x) ≤ 2 :=
      G.dist_le (Walk.cons huy (Walk.cons hxyG.symm Walk.nil))
    have hne0 : G.dist u (old x) ≠ 0 := by
      intro h
      exact hold_ne x (h_two_connected.2.1.dist_eq_zero_iff.mp h).symm
    have hne1 : G.dist u (old x) ≠ 1 := by
      intro h
      exact hxS ((hmemS x).mpr (dist_eq_one_iff_adj.mp h))
    omega
  have hsubsetParents (P : Finset (Fin m)) (x : Fin m)
      (hxS : x ∉ S) (hPS : P ⊆ S)
      (hAdj : ∀ y ∈ P, (Knt m 2).Adj x y) :
      P.image old ⊆ External.distanceTwoParents G u (old x) := by
    intro w hw
    obtain ⟨y, hyP, rfl⟩ := Finset.mem_image.mp hw
    have hyS := hPS hyP
    have hxyG := (holdAdj x y).mp (hAdj y hyP)
    have huy := (hmemS y).mp hyS
    simpa [External.distanceTwoParents, openNeighborhood, hxyG.symm, huy]
  have hparentBound (P : Finset (Fin m)) (x : Fin m)
      (hxS : x ∉ S) (hPS : P ⊆ S)
      (hAdj : ∀ y ∈ P, (Knt m 2).Adj x y) :
      P.card ≤ (External.distanceTwoParents G u (old x)).card := by
    have himage : (P.image old).card = P.card :=
      Finset.card_image_iff.mpr hold_inj.injOn
    rw [← himage]
    exact Finset.card_le_card (hsubsetParents P x hxS hPS hAdj)
  have hsumIntoVertex (X : Finset (Fin m)) :
      vertexContribution G u ≥ ∑ x ∈ X, pairGap G u (old x) := by
    let XV : Finset V := X.image old
    have hsumImage : (∑ y ∈ XV, pairGap G u y) =
        ∑ x ∈ X, pairGap G u (old x) := by
      rw [show XV = X.image old by rfl, Finset.sum_image]
      exact hold_inj.injOn
    unfold vertexContribution
    rw [← hsumImage]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro y _ _
    exact External.pairGap_nonneg G h_two_connected.2.1 u y
  have subcaseNonempty
      (T : Finset (Fin m)) (t : ℕ) (c : Fin m)
      (htdef : t = T.card) (hTeq : T = R ∩ S)
      (hTsubR : T ⊆ R) (hTsubS : T ⊆ S)
      (htUpper : t ≤ m - 3) (htpos : 1 ≤ t)
      (hcS : c ∈ S) (hc_ne_z : c ≠ z) (hcNotR : c ∉ R)
      (hzAdjU : G.Adj u (old z)) :
      szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥
        (Fintype.card V : ℤ) - 2 := by
    let X : Finset (Fin m) := R \ T
    have hXcard : X.card = (m - 3) - t := by
      rw [show X = R \ T by rfl, Finset.card_sdiff_of_subset hTsubR,
        hRcard, htdef]
    let P : Finset (Fin m) := insert c T
    have hcNotT : c ∉ T := fun h => hcNotR (hTsubR h)
    have hPcard : P.card = t + 1 := by simp [P, hcNotT, htdef]
    have hPsubS : P ⊆ S := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hcS
      · exact hTsubS hy
    have hpairX (x : Fin m) (hx : x ∈ X) :
        pairGap G u (old x) ≥ (2 * (t : ℤ)) := by
      have hxR : x ∈ R := (Finset.mem_sdiff.mp hx).1
      have hxNotT : x ∉ T := (Finset.mem_sdiff.mp hx).2
      have hxNotS : x ∉ S := by
        intro hxS
        exact hxNotT (hTeq.symm ▸ Finset.mem_inter.mpr ⟨hxR, hxS⟩)
      have hAdjP : ∀ y ∈ P, (Knt m 2).Adj x y := by
        intro y hy
        have hxz := (hRmem x hxR).1
        rcases Finset.mem_insert.mp hy with hyc | hyT
        · subst y
          exact hclique x c hxz hc_ne_z (fun h => hcNotR (h ▸ hxR))
        · have hyR := hTsubR hyT
          exact hclique x y hxz (hRmem y hyR).1
            (fun h => hxNotT (h ▸ hyT))
      have hdist := hdistTwoOfParent x c hxNotS hcS
        (hAdjP c (by simp [P]))
      have hp := hparentBound P x hxNotS hPsubS hAdjP
      have hC2 := External.pairGap_ge_two_mul_parents_sub_two G u (old x) hdist
      rw [hPcard] at hp
      omega
    have hsumX : (∑ x ∈ X, pairGap G u (old x)) ≥
        (X.card : ℤ) * (2 * (t : ℤ)) := by
      have h := Finset.sum_le_sum fun x hx => hpairX x hx
      simpa [Finset.sum_const, nsmul_eq_mul] using h
    let del : Fin m → {x : V // x ≠ u} := fun x => ⟨old x, hold_ne x⟩
    have hdelInj : Function.Injective del := by
      intro x y h
      exact hold_inj (congrArg Subtype.val h)
    let Q : Finset (Sym2 {x : V // x ≠ u}) :=
      T.image fun y => s(del z, del y)
    have hQinj : Set.InjOn (fun y => s(del z, del y)) T := by
      intro x hx y hy h
      exact hdelInj ((Sym2.mkEmbedding (del z)).injective h)
    have hqsum :
        (∑ p ∈ Q, (pairGapOnPair G (Sym2.map Subtype.val p) -
          pairGapOnPair (deleteVertex G u) p)) ≥ 2 * (t : ℤ) := by
      rw [show Q = T.image (fun y => s(del z, del y)) by rfl,
        Finset.sum_image hQinj]
      have hsum := Finset.sum_le_sum fun y hy => by
        have hyR := hTsubR hy
        have hyS := hTsubS hy
        have hzy : ¬(deleteVertex G u).Adj (del z) (del y) := by
          intro h
          have hK : (Knt m 2).Adj z y := (holdAdj z y).mpr h
          rcases hzNeighbors y hK with hya | hyb
          · exact (hRmem y hyR).2.1 hya
          · exact (hRmem y hyR).2.2 hyb
        have hgain := External.pairGain_two_of_neighbor_nonedge G
          h_two_connected.2.1 u v h_distinct h_neighborhood
          (del z) (del y)
          (fun h => (hRmem y hyR).1 (hdelInj h.symm))
          hzAdjU ((hmemS y).mp hyS) hzy
        simpa [del, pairGapOnPair] using hgain
      rw [Finset.sum_sub_distrib]
      rw [Finset.sum_sub_distrib] at hsum
      simpa only [Sym2.map_pair_eq, pairGapOnPair, Sym2.lift_mk, del,
        Finset.sum_const, nsmul_eq_mul, htdef, mul_comm] using hsum
    have hvertex := hsumIntoVertex X
    have hglobal := External.gap_sub_deleteVertex_ge_vertexContribution_add_pairGainFinset
      G h_two_connected.2.1 u v h_distinct h_neighborhood Q
    have harith := lemma2Subcase1bNonemptyArithmetic (Fintype.card V) t
      (by exact_mod_cast h_order) (by exact_mod_cast htpos)
      (by
        have htplus : t + 3 ≤ m := by omega
        have htplusZ : (t : ℤ) + 3 ≤ (m : ℤ) := by exact_mod_cast htplus
        have hmVZ : (Fintype.card V : ℤ) = (m : ℤ) + 1 := by
          exact_mod_cast hcardV
        omega)
    have hXcardZ : (X.card : ℤ) = (m : ℤ) - 3 - t := by
      rw [hXcard, Nat.cast_sub (by omega : t ≤ m - 3),
        Nat.cast_sub (by omega : 3 ≤ m)]
      omega
    rw [hXcardZ] at hsumX
    have hmVZ : (m : ℤ) = (Fintype.card V : ℤ) - 1 := by
      have hcardVZ : (Fintype.card V : ℤ) = (m : ℤ) + 1 := by
        exact_mod_cast hcardV
      omega
    rw [hmVZ] at hsumX
    ring_nf at hsumX hqsum harith ⊢
    omega
  have subcaseEmpty
      (T : Finset (Fin m)) (t : ℕ) (c d : Fin m)
      (htdef : t = T.card) (hTeq : T = R ∩ S)
      (hTsubR : T ⊆ R) (htNotPos : ¬1 ≤ t)
      (hcS : c ∈ S) (hzS : z ∈ S) (hzAdjU : G.Adj u (old z))
      (hc_ne_z : c ≠ z) (hd_ne_z : d ≠ z) (hc_ne_d : c ≠ d)
      (hzc : (Knt m 2).Adj z c) (hzd : (Knt m 2).Adj z d)
      (hRdata : ∀ x ∈ R, x ≠ z ∧ x ≠ c ∧ x ≠ d) :
      szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥
        (Fintype.card V : ℤ) - 2 := by
    have htzero : t = 0 := by omega
    have hTempty : T = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa [← htdef] using htzero
    have hRNotS (x : Fin m) (hxR : x ∈ R) : x ∉ S := by
      intro hxS
      have hxT : x ∈ T := by
        exact hTeq.symm ▸ Finset.mem_inter.mpr ⟨hxR, hxS⟩
      simpa [hTempty] using hxT
    by_cases hdS : d ∈ S
    · have hpairR (x : Fin m) (hxR : x ∈ R) :
          pairGap G u (old x) ≥ (2 : ℤ) := by
        have hxNotS := hRNotS x hxR
        let P : Finset (Fin m) := {c, d}
        have hPsub : P ⊆ S := by
          intro y hy
          simp only [P, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with hyc | hyd
          · simpa [hyc] using hcS
          · simpa [hyd] using hdS
        have hAdjP : ∀ y ∈ P, (Knt m 2).Adj x y := by
          intro y hy
          have hxr := hRdata x hxR
          simp only [P, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with hyc | hyd
          · subst y
            exact hclique x c hxr.1 hc_ne_z (fun h => hxr.2.1 h)
          · subst y
            exact hclique x d hxr.1 hd_ne_z (fun h => hxr.2.2 h)
        have hdist := hdistTwoOfParent x c hxNotS hcS (hAdjP c (by simp [P]))
        have hp := hparentBound P x hxNotS hPsub hAdjP
        have hC2 := External.pairGap_ge_two_mul_parents_sub_two G u (old x) hdist
        have hPcard : P.card = 2 := by simp [P, hc_ne_d]
        rw [hPcard] at hp
        omega
      have hsumR : (∑ x ∈ R, pairGap G u (old x)) ≥
          (2 : ℤ) * (m - 3 : ℕ) := by
        have h := Finset.sum_le_sum fun x hx => hpairR x hx
        simp only [Finset.sum_const, nsmul_eq_mul] at h
        rw [hRcard] at h
        omega
      have hvertex := hsumIntoVertex R
      have hglobal := External.gap_sub_deleteVertex_ge_vertexContribution G
        h_two_connected.2.1 u v h_distinct h_neighborhood
      have hmVZ : (m : ℤ) = (Fintype.card V : ℤ) - 1 := by
        have hcardVZ : (Fintype.card V : ℤ) = (m : ℤ) + 1 := by
          exact_mod_cast hcardV
        omega
      have hm3 : 3 ≤ m := by omega
      rw [Nat.cast_sub hm3, hmVZ] at hsumR
      omega
    · have hdistD : G.dist u (old d) = 2 :=
        hdistTwoOfParent d c hdS hcS
          (hclique d c hd_ne_z hc_ne_z hc_ne_d.symm)
      have hpairD : pairGap G u (old d) ≥ (2 : ℤ) := by
        let P : Finset (Fin m) := {z, c}
        have hPsub : P ⊆ S := by
          intro y hy
          simp only [P, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with hyz | hyc
          · simpa [hyz] using hzS
          · simpa [hyc] using hcS
        have hAdjP : ∀ y ∈ P, (Knt m 2).Adj d y := by
          intro y hy
          simp only [P, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with hyz | hyc
          · subst y
            exact hzd.symm
          · subst y
            exact hclique d c hd_ne_z hc_ne_z hc_ne_d.symm
        have hp := hparentBound P d hdS hPsub hAdjP
        have hC2 := External.pairGap_ge_two_mul_parents_sub_two G u (old d) hdistD
        have hPcard : P.card = 2 := by simp [P, hc_ne_z, hc_ne_z.symm]
        rw [hPcard] at hp
        omega
      have hpairR (x : Fin m) (hxR : x ∈ R) :
          pairGap G u (old x) ≥ (1 : ℤ) := by
        have hxNotS := hRNotS x hxR
        have hxr := hRdata x hxR
        have hdx : (Knt m 2).Adj d x :=
          hclique d x hd_ne_z hxr.1 (fun h => hxr.2.2 h.symm)
        have hzx : ¬G.Adj (old z) (old x) := by
          intro h
          have hK := (holdAdj z x).mpr h
          rcases hzNeighbors x hK with h | h
          · exact (hRmem x hxR).2.1 h
          · exact (hRmem x hxR).2.2 h
        have hdistX : G.dist u (old x) = 2 :=
          hdistTwoOfParent x c hxNotS hcS
            (hclique x c hxr.1 hc_ne_z (fun h => hxr.2.1 h))
        exact External.pairGap_ge_one_of_horizontalEdge G h_two_connected.2.1
          u (old d) (old x) (old z) ((holdAdj d x).mp hdx)
          (by rw [hdistD, hdistX]) ((holdAdj d z).mp hzd.symm)
          (by rw [dist_eq_one_iff_adj.mpr hzAdjU, hdistD]; omega) hzx
      let Y : Finset (Fin m) := insert d R
      have hdNotR : d ∉ R := by
        intro h
        exact (hRdata d h).2.2 rfl
      have hsumY : (∑ x ∈ Y, pairGap G u (old x)) ≥
          (m - 3 : ℤ) + 2 := by
        rw [show Y = insert d R by rfl, Finset.sum_insert hdNotR]
        have hsumR := Finset.sum_le_sum fun x hx => hpairR x hx
        simp only [Finset.sum_const, nsmul_eq_mul] at hsumR
        rw [hRcard] at hsumR
        omega
      have hvertex := hsumIntoVertex Y
      have hglobal := External.gap_sub_deleteVertex_ge_vertexContribution G
        h_two_connected.2.1 u v h_distinct h_neighborhood
      have hmVZ : (m : ℤ) = (Fintype.card V : ℤ) - 1 := by
        have hcardVZ : (Fintype.card V : ℤ) = (m : ℤ) + 1 := by
          exact_mod_cast hcardV
        omega
      rw [hmVZ] at hsumY
      omega
  by_cases hzS : z ∈ S
  · have hzAdjU : G.Adj u (old z) := (hmemS z).mp hzS
    have huv : G.Adj u v := by
      have hu : u ∈ closedNeighborhood G u := by simp [closedNeighborhood]
      have hv := h_neighborhood hu
      simp only [closedNeighborhood, Finset.mem_insert] at hv
      rcases hv with h | h
      · exact False.elim (h_distinct h)
      · have hvu : G.Adj v u := by simpa [openNeighborhood] using h
        exact hvu.symm
    have hextraNeighbor : ∃ w : V,
        w ≠ u ∧ w ≠ old z ∧ G.Adj u w ∧ G.Adj (old z) w := by
      by_cases hvz : v = old z
      · obtain ⟨r₁, r₂, hrne, hur₁, hur₂⟩ :=
          External.exists_two_neighbors_of_twoConnected G h_two_connected u
        have hone : r₁ ≠ old z ∨ r₂ ≠ old z := by
          by_contra h
          push_neg at h
          exact hrne (h.1.trans h.2.symm)
        rcases hone with hr | hr
        · refine ⟨r₁, hur₁.ne.symm, hr, hur₁, ?_⟩
          have hrmem : r₁ ∈ closedNeighborhood G u := by
            simp [closedNeighborhood, openNeighborhood, hur₁]
          have hvmem := h_neighborhood hrmem
          simp only [closedNeighborhood, Finset.mem_insert] at hvmem
          rcases hvmem with h | h
          · exact False.elim (hr (h.trans hvz))
          · simpa [hvz, openNeighborhood] using h
        · refine ⟨r₂, hur₂.ne.symm, hr, hur₂, ?_⟩
          have hrmem : r₂ ∈ closedNeighborhood G u := by
            simp [closedNeighborhood, openNeighborhood, hur₂]
          have hvmem := h_neighborhood hrmem
          simp only [closedNeighborhood, Finset.mem_insert] at hvmem
          rcases hvmem with h | h
          · exact False.elim (hr (h.trans hvz))
          · simpa [hvz, openNeighborhood] using h
      · refine ⟨v, h_distinct.symm, hvz, huv, ?_⟩
        have hzmem : old z ∈ closedNeighborhood G u := by
          simp [closedNeighborhood, openNeighborhood, hzAdjU]
        have hvmem := h_neighborhood hzmem
        simp only [closedNeighborhood, Finset.mem_insert] at hvmem
        rcases hvmem with h | h
        · exact False.elim (hvz h.symm)
        · have hvzAdj : G.Adj v (old z) := by
            simpa [openNeighborhood] using h
          exact hvzAdj.symm
    obtain ⟨w, hwu, hwz, huw, hzw⟩ := hextraNeighbor
    let we : Fin m := e ⟨w, hwu⟩
    have holdWe : old we = w := by simp [old, we]
    have hweS : we ∈ S := by simpa [hmemS, holdWe] using huw
    have hzWe : (Knt m 2).Adj z we :=
      (holdAdj z we).mpr (by simpa [holdWe] using hzw)
    have habS : a ∈ S ∨ b ∈ S := by
      rcases hzNeighbors we hzWe with h | h
      · exact Or.inl (h ▸ hweS)
      · exact Or.inr (h ▸ hweS)
    let T : Finset (Fin m) := R ∩ S
    let t := T.card
    have hTsubR : T ⊆ R := Finset.inter_subset_left
    have hTsubS : T ⊆ S := Finset.inter_subset_right
    have htUpper : t ≤ m - 3 := by
      have hc := Finset.card_le_card hTsubR
      simpa [t, hRcard] using hc
    by_cases haS : a ∈ S
    · let c := a
      let d := b
      have hcS : c ∈ S := haS
      have hc_ne_z : c ≠ z := hz_ne_a.symm
      have hd_ne_z : d ≠ z := hz_ne_b.symm
      have hc_ne_d : c ≠ d := ha_ne_b
      have hcNotR : c ∉ R := by
        intro h
        exact (hRmem c h).2.1 rfl
      by_cases htpos : 1 ≤ t
      · exact subcaseNonempty T t c rfl rfl hTsubR hTsubS htUpper htpos
          hcS hc_ne_z hcNotR hzAdjU
      · exact subcaseEmpty T t c d rfl rfl hTsubR htpos hcS hzS hzAdjU
          hc_ne_z hd_ne_z hc_ne_d hza hzb hRmem
    · let c := b
      let d := a
      have hcS : c ∈ S := habS.resolve_left haS
      have hc_ne_z : c ≠ z := hz_ne_b.symm
      have hd_ne_z : d ≠ z := hz_ne_a.symm
      have hc_ne_d : c ≠ d := ha_ne_b.symm
      have hcNotR : c ∉ R := by
        intro h
        exact (hRmem c h).2.2 rfl
      by_cases htpos : 1 ≤ t
      · exact subcaseNonempty T t c rfl rfl hTsubR hTsubS htUpper htpos
          hcS hc_ne_z hcNotR hzAdjU
      · exact subcaseEmpty T t c d rfl rfl hTsubR htpos hcS hzS hzAdjU
          hc_ne_z hd_ne_z hc_ne_d hzb hza
          (by intro x hx; have h := hRmem x hx; exact ⟨h.1, h.2.2, h.2.1⟩)
  · have hSsub : S ⊆ (Finset.univ.erase z : Finset (Fin m)) := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun h => hzS (h ▸ hx), Finset.mem_univ x⟩
    have hsLe : s ≤ m - 1 := by
      have hc := Finset.card_le_card hSsub
      simpa [s] using hc
    have hsUpper : s ≤ m - 2 := by
      by_contra h
      have hseq : s = m - 1 := by omega
      have hSeq : S = Finset.univ.erase z := by
        apply Finset.eq_of_subset_of_card_le hSsub
        simpa [s, hseq]
      have hattach : ∀ x : V, (hx : x ≠ u) →
          (G.Adj u x ↔ (e ⟨x, hx⟩).val ≠ 0) := by
        intro x hx
        let xe : Fin m := e ⟨x, hx⟩
        have holdXe : old xe = x := by simp [old, xe]
        constructor
        · intro hux
          have hxeS : xe ∈ S := (hmemS xe).mpr (by simpa [holdXe] using hux)
          have hxez : xe ≠ z := (Finset.mem_erase.mp (hSeq ▸ hxeS)).1
          intro hzero
          exact hxez (Fin.ext (by simpa [z] using hzero))
        · intro hx0
          have hxez : xe ≠ z := by
            intro h
            apply hx0
            have hv := congrArg Fin.val h
            simpa [z] using hv
          have hxeS : xe ∈ S := by
            rw [hSeq]
            exact Finset.mem_erase.mpr ⟨hxez, Finset.mem_univ xe⟩
          simpa [holdXe] using (hmemS xe).mp hxeS
      have hexc := isExceptional_of_delete_low_attachment G u m
        (by omega) hcardV e hattach
      exact h_unexceptional hexc
    let X : Finset (Fin m) := (Finset.univ.erase z) \ S
    have hXcard : X.card = (m - 1) - s := by
      rw [show X = (Finset.univ.erase z) \ S by rfl,
        Finset.card_sdiff_of_subset hSsub]
      simp [s]
    have hpairX (x : Fin m) (hx : x ∈ X) :
        pairGap G u (old x) ≥ (2 * ((s : ℤ) - 1)) := by
      have hxErase : x ∈ (Finset.univ.erase z : Finset (Fin m)) :=
        (Finset.mem_sdiff.mp hx).1
      have hxz : x ≠ z := Finset.ne_of_mem_erase hxErase
      have hxS : x ∉ S := (Finset.mem_sdiff.mp hx).2
      have hAdjS : ∀ y ∈ S, (Knt m 2).Adj x y := by
        intro y hy
        have hyz : y ≠ z := fun h => hzS (h ▸ hy)
        exact hclique x y hxz hyz (fun h => hxS (h ▸ hy))
      obtain ⟨y, hyS⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      have hdist := hdistTwoOfParent x y hxS hyS (hAdjS y hyS)
      have hp := hparentBound S x hxS (fun _ h => h) hAdjS
      have hC2 := External.pairGap_ge_two_mul_parents_sub_two G u (old x) hdist
      change s ≤ (External.distanceTwoParents G u (old x)).card at hp
      omega
    have hsumX : (∑ x ∈ X, pairGap G u (old x)) ≥
        (X.card : ℤ) * (2 * ((s : ℤ) - 1)) := by
      have h := Finset.sum_le_sum fun x hx => hpairX x hx
      simpa [Finset.sum_const, nsmul_eq_mul] using h
    have hvertex := hsumIntoVertex X
    have hglobal := External.gap_sub_deleteVertex_ge_vertexContribution G
      h_two_connected.2.1 u v h_distinct h_neighborhood
    have harith := lemma2Subcase1aArithmetic (Fintype.card V) s
      (by exact_mod_cast h_order) (by exact_mod_cast hsLower)
      (by
        have hsplus : s + 2 ≤ m := by omega
        have hsplusZ : (s : ℤ) + 2 ≤ (m : ℤ) := by exact_mod_cast hsplus
        have hmVZ : (Fintype.card V : ℤ) = (m : ℤ) + 1 := by
          exact_mod_cast hcardV
        omega)
    have hXcardZ : (X.card : ℤ) = (m : ℤ) - 1 - s := by
      rw [hXcard, Nat.cast_sub (by omega : s ≤ m - 1),
        Nat.cast_sub (by omega : 1 ≤ m)]
      omega
    rw [hXcardZ] at hsumX
    have hmVZ : (m : ℤ) = (Fintype.card V : ℤ) - 1 := by
      have hcardVZ : (Fintype.card V : ℤ) = (m : ℤ) + 1 := by
        exact_mod_cast hcardV
      omega
    rw [hmVZ] at hsumX
    ring_nf at hsumX harith ⊢
    omega

end

end BKLPS
