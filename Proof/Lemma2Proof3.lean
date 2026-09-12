import Proof.Definitions
import Proof.ExternalResults.BKLPSLemma7
import Proof.Lemma2ExceptionalCones
import Proof.ExternalResults.BlockStructure
import Proof.ExternalResults.BKLPSLemma7GoodsLowerBounds
import Mathlib.Tactic.Linarith

/-! The `G-u ≅ K_(n-1)^(n-3)` case of Lemma 2. -/

namespace BKLPS

open SimpleGraph

noncomputable section

universe u

/-- The numerical finish of Case 2.  Put `a=s-1` and `b=n-1-s`;
both are positive and their sum is `n-2 ≥ 4`. -/
theorem lemma2Case2Arithmetic (n s : ℤ)
    (hn : n ≥ 6) (hs₀ : s ≥ 2) (hs₁ : s ≤ n - 2) :
    2 * (s - 1) * (n - 1 - s) - 2 ≥ n - 2 := by
  have hprod : 0 ≤ (s - 2) * (n - 2 - s) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

/-- Case 2 of Lemma 2: `G-u ≅ K_(n-1)^(n-3)`. -/
theorem lemma2Proof3
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h_order : Fintype.card V ≥ 6)
    (h_unexceptional : IsUnexceptional G)
    (h_two_connected : IsTwoConnected G)
    (u v : V) (h_distinct : u ≠ v)
    (h_neighborhood : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (h_delete : IsomorphicToKnt (deleteVertex G u) (Fintype.card V - 3)) :
    szegedWienerGap G - szegedWienerGap (deleteVertex G u) ≥
      (Fintype.card V : ℤ) - 2 := by
  /-
  This is Case 2.  Here `G-u ≅ K_(n-1)^(n-3) = K_(n-1)-e`.  With
  `S = N_G(u)` and `s = |S|`, unexceptionality rules out `s=n-1`, so
  `2 ≤ s ≤ n-2`.  The BKLPS Lemma 7 estimates give

    `η(G)-η(G-u) ≥ 2(s-1)(n-1-s)-2 ≥ n-2`.
  -/
  classical
  have hcardDelete : Fintype.card {x : V // x ≠ u} =
      Fintype.card V - 1 := by
    simpa using Fintype.card_subtype_compl (fun x : V => x = u)
  let m := Fintype.card {x : V // x ≠ u}
  have hm : 5 ≤ m := by omega
  letI : NeZero m := ⟨by omega⟩
  have hparam : Fintype.card V - 3 = m - 2 := by omega
  rw [hparam] at h_delete
  have h_delete' : Nonempty (deleteVertex G u ≃g Knt m (m - 2)) := by
    simpa [m] using h_delete
  obtain ⟨e⟩ := h_delete'
  let old : Fin m → V := fun x => (e.symm x).1
  have hold_ne (x : Fin m) : old x ≠ u := (e.symm x).2
  have hold_inj : Function.Injective old := by
    intro x y h
    apply e.symm.injective
    apply Subtype.ext
    exact h
  let S : Finset (Fin m) := Finset.univ.filter fun x => G.Adj u (old x)
  let s := S.card
  obtain ⟨a, b, hab, hua, hub⟩ :=
    External.exists_two_neighbors_of_twoConnected G h_two_connected u
  have hau : a ≠ u := hua.ne.symm
  have hbu : b ≠ u := hub.ne.symm
  let ae : Fin m := e ⟨a, hau⟩
  let be : Fin m := e ⟨b, hbu⟩
  have hae : ae ∈ S := by simp [ae, S, old, hua]
  have hbe : be ∈ S := by simp [be, S, old, hub]
  have habE : ae ≠ be := by
    intro h
    apply hab
    have := e.injective h
    exact congrArg Subtype.val this
  have hsLower : 2 ≤ s := by
    have hsub : ({ae, be} : Finset (Fin m)) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hae
      · exact hbe
    have hc := Finset.card_le_card hsub
    simpa [s, habE] using hc
  have hcardV : Fintype.card V = m + 1 := by omega
  have hsUpper : s ≤ m - 1 := by
    by_contra h
    have hsm : s = m := by
      have hle : s ≤ m := by
        calc
          s = S.card := rfl
          _ ≤ (Finset.univ : Finset (Fin m)).card :=
            Finset.card_le_card (Finset.subset_univ S)
          _ = m := by simp
      omega
    have hSuniv : S = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa [s] using hsm
    have hdom : ∀ x : V, x ≠ u → G.Adj u x := by
      intro x hx
      let z : Fin m := e ⟨x, hx⟩
      have hz : z ∈ S := by rw [hSuniv]; simp
      simpa [z, S, old] using hz
    have hexc := isExceptional_of_delete_high_dominating
      G u m (by omega) hcardV hdom ⟨e⟩
    exact h_unexceptional hexc
  let last : Fin m := ⟨m - 1, by omega⟩
  let bad : Fin m := if (0 : Fin m) ∈ S then last else 0
  let X : Finset (Fin m) := Finset.univ \ S
  have hXcard : X.card = m - s := by
    rw [show X = Finset.univ \ S by rfl, Finset.card_sdiff]
    simp [s]
  have hXpos : 1 ≤ X.card := by rw [hXcard]; omega
  let forbidden : Fin m := if (0 : Fin m) ∈ S then 0 else last
  let parents : Fin m → Finset (Fin m) := fun x =>
    if x = bad then S.erase forbidden else S
  have hcanonical (x y : Fin m) (hxX : x ∈ X) (hyP : y ∈ parents x) :
      (Knt m (m - 2)).Adj x y := by
    have hxS : x ∉ S := by simpa [X] using hxX
    have hyS : y ∈ S := by
      by_cases hxbad : x = bad
      · exact Finset.mem_of_mem_erase (by simpa [parents, hxbad] using hyP)
      · simpa [parents, hxbad] using hyP
    have hxy : x ≠ y := fun h => hxS (h ▸ hyS)
    refine ⟨hxy, ?_⟩
    by_cases hzS : (0 : Fin m) ∈ S
    · have hx0 : x ≠ 0 := fun h => hxS (h ▸ hzS)
      by_cases hy0 : y = 0
      · subst y
        right; right
        refine ⟨rfl, ?_⟩
        have hxlast : x ≠ last := by
          intro h
          have hxbad : x = bad := by simpa [bad, hzS] using h
          have hyErase : (0 : Fin m) ∈ S.erase forbidden := by
            simpa [parents, hxbad] using hyP
          have hne := Finset.ne_of_mem_erase hyErase
          exact hne (by simp [forbidden, hzS])
        have hxlt := x.isLt
        have hxlastVal : x.val ≠ m - 1 := by
          intro h
          exact hxlast (Fin.ext (by simp [last, h]))
        omega
      · exact Or.inl ⟨fun h => hx0 (Fin.ext h), fun h => hy0 (Fin.ext h)⟩
    · by_cases hx0 : x = 0
      · subst x
        right; left
        refine ⟨rfl, ?_⟩
        have hxbad : (0 : Fin m) = bad := by simp [bad, hzS]
        have hyErase : y ∈ S.erase forbidden := by
          simpa [parents, hxbad] using hyP
        have hylast : y ≠ last := by
          have := Finset.ne_of_mem_erase hyErase
          simpa [forbidden, hzS] using this
        have hylt := y.isLt
        have hylastVal : y.val ≠ m - 1 := by
          intro h
          exact hylast (Fin.ext (by simp [last, h]))
        omega
      · have hy0 : y ≠ 0 := fun h => hzS (h ▸ hyS)
        exact Or.inl ⟨fun h => hx0 (Fin.ext h), fun h => hy0 (Fin.ext h)⟩
  have hparentSubset (x : Fin m) (hxX : x ∈ X) :
      (parents x).image old ⊆ External.distanceTwoParents G u (old x) := by
    intro z hz
    obtain ⟨y, hyP, rfl⟩ := Finset.mem_image.mp hz
    have hyS : y ∈ S := by
      by_cases hxbad : x = bad
      · exact Finset.mem_of_mem_erase (by simpa [parents, hxbad] using hyP)
      · simpa [parents, hxbad] using hyP
    have hxS : x ∉ S := by simpa [X] using hxX
    have hxy : x ≠ y := fun h => hxS (h ▸ hyS)
    have hcan := hcanonical x y hxX hyP
    have hxyG : G.Adj (old x) (old y) := by
      have hxyDelete : (deleteVertex G u).Adj (e.symm x) (e.symm y) :=
        e.map_rel_iff.mp (by simpa using hcan)
      simpa [old] using hxyDelete
    have huy : G.Adj u (old y) := by simpa [S] using hyS
    simpa [External.distanceTwoParents, openNeighborhood, hxyG.symm, huy]
  have hparentsCard (x : Fin m) (hxX : x ∈ X) :
      (parents x).card ≤ (External.distanceTwoParents G u (old x)).card := by
    have himageCard : ((parents x).image old).card = (parents x).card :=
      Finset.card_image_iff.mpr hold_inj.injOn
    rw [← himageCard]
    exact Finset.card_le_card (hparentSubset x hxX)
  have hparentsBase (x : Fin m) : s - 1 ≤ (parents x).card := by
    by_cases hxbad : x = bad
    · by_cases hf : forbidden ∈ S
      · rw [show parents x = S.erase forbidden by simp [parents, hxbad],
          Finset.card_erase_of_mem hf]
      · rw [show parents x = S.erase forbidden by simp [parents, hxbad]]
        simp [hf, s]
    · simp [parents, hxbad, s]
  have hparentsGood (x : Fin m) (hxX : x ∈ X) (hxbad : x ≠ bad) :
      (parents x).card = s := by
    simp [parents, hxbad, s]
  have hdistTwo (x : Fin m) (hxX : x ∈ X) : G.dist u (old x) = 2 := by
    have hpcard : 1 ≤ (parents x).card := by
      have hb := hparentsBase x
      omega
    obtain ⟨y, hyP⟩ := Finset.card_pos.mp (by omega : 0 < (parents x).card)
    have hyS : y ∈ S := by
      by_cases hxbad : x = bad
      · exact Finset.mem_of_mem_erase (by simpa [parents, hxbad] using hyP)
      · simpa [parents, hxbad] using hyP
    have hxS : x ∉ S := by simpa [X] using hxX
    have hxy : x ≠ y := fun h => hxS (h ▸ hyS)
    have hcan := hcanonical x y hxX hyP
    have hxyG : G.Adj (old x) (old y) := by
      have hxyDelete : (deleteVertex G u).Adj (e.symm x) (e.symm y) :=
        e.map_rel_iff.mp (by simpa using hcan)
      simpa [old] using hxyDelete
    have huy : G.Adj u (old y) := by simpa [S] using hyS
    have hle : G.dist u (old x) ≤ 2 := by
      exact G.dist_le (Walk.cons huy (Walk.cons hxyG.symm Walk.nil))
    have hne0 : G.dist u (old x) ≠ 0 := by
      intro h
      exact hold_ne x (h_two_connected.2.1.dist_eq_zero_iff.mp h).symm
    have hne1 : G.dist u (old x) ≠ 1 := by
      intro h
      have hadj := dist_eq_one_iff_adj.mp h
      exact hxS (by simpa [S] using hadj)
    omega
  have hpairBase (x : Fin m) (hxX : x ∈ X) :
      pairGap G u (old x) ≥ (2 * (s : ℤ) - 4) := by
    have hC2 := External.pairGap_ge_two_mul_parents_sub_two G u (old x)
      (hdistTwo x hxX)
    have hp := hparentsCard x hxX
    have hb := hparentsBase x
    omega
  have hpairGood (x : Fin m) (hxX : x ∈ X) (hxbad : x ≠ bad) :
      pairGap G u (old x) ≥ (2 * (s : ℤ) - 2) := by
    have hC2 := External.pairGap_ge_two_mul_parents_sub_two G u (old x)
      (hdistTwo x hxX)
    have hp := hparentsCard x hxX
    have hg := hparentsGood x hxX hxbad
    omega
  have hsumX : (∑ x ∈ X, pairGap G u (old x)) ≥
      ((X.card : ℤ) - 1) * (2 * (s : ℤ) - 2) +
        (2 * (s : ℤ) - 4) := by
    by_cases hbadX : bad ∈ X
    · rw [← Finset.sum_erase_add _ _ hbadX]
      have hsum := Finset.sum_le_sum fun x hx =>
        hpairGood x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
      have hcardErase : (X.erase bad).card = X.card - 1 :=
        Finset.card_erase_of_mem hbadX
      simp only [Finset.sum_const, nsmul_eq_mul] at hsum
      have hcardCast : ((X.erase bad).card : ℤ) = (X.card : ℤ) - 1 := by
        rw [hcardErase, Nat.cast_sub (by omega : 1 ≤ X.card)]
        norm_num
      rw [hcardCast] at hsum
      have hbase := hpairBase bad hbadX
      omega
    · have hsum := Finset.sum_le_sum fun x hx =>
        hpairGood x hx (fun h => hbadX (h ▸ hx))
      simp only [Finset.sum_const, nsmul_eq_mul] at hsum
      have hnonneg : 0 ≤ 2 * (s : ℤ) - 4 := by omega
      have hid : (X.card : ℤ) * (2 * (s : ℤ) - 2) =
          ((X.card : ℤ) - 1) * (2 * (s : ℤ) - 2) +
            (2 * (s : ℤ) - 2) := by ring
      rw [hid] at hsum
      omega
  let XV : Finset V := X.image old
  have hsumImage : (∑ z ∈ XV, pairGap G u z) =
      ∑ x ∈ X, pairGap G u (old x) := by
    rw [show XV = X.image old by rfl, Finset.sum_image]
    exact hold_inj.injOn
  have hvertex : vertexContribution G u ≥
      ∑ x ∈ X, pairGap G u (old x) := by
    unfold vertexContribution
    rw [← hsumImage]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro z _ _
    exact External.pairGap_nonneg G h_two_connected.2.1 u z
  have hgap := External.gap_sub_deleteVertex_ge_vertexContribution G
    h_two_connected.2.1 u v h_distinct h_neighborhood
  have hXcardZ : (X.card : ℤ) = (m : ℤ) - s := by
    rw [hXcard, Nat.cast_sub (by omega : s ≤ m)]
  have harith := lemma2Case2Arithmetic (Fintype.card V) s
    (by exact_mod_cast h_order) (by exact_mod_cast hsLower)
    (by
      have hcardVZ : (Fintype.card V : ℤ) = (m : ℤ) + 1 := by
        exact_mod_cast hcardV
      have hsPlus : s + 1 ≤ m := by omega
      have hsUpperZ : (s : ℤ) ≤ (m : ℤ) - 1 := by
        have hsPlusZ : (s : ℤ) + 1 ≤ (m : ℤ) := by
          exact_mod_cast hsPlus
        omega
      omega)
  rw [hXcardZ] at hsumX
  have hmZ : (m : ℤ) = (Fintype.card V : ℤ) - 1 := by
    rw [show m = Fintype.card V - 1 by exact hcardDelete]
    omega
  rw [hmZ] at hsumX
  ring_nf at hsumX harith ⊢
  omega

end

end BKLPS
