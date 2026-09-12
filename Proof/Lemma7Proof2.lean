import Proof.Lemma7Proof1
import Proof.Theorem1Proof1
import Mathlib.Order.Interval.Finset.Fin

namespace BKLPS
open SimpleGraph
noncomputable section

lemma sharpnessDist (n : ℕ) (hn : n ≥ 10) (a b : Fin n) :
    (sharpnessGraph n).dist a b =
      if a = b then 0 else if (sharpnessGraph n).Adj a b then 1 else 2 := by
  by_cases hab : a = b
  · simp [hab]
  by_cases hadj : (sharpnessGraph n).Adj a b
  · simp [hab, hadj]
  · simp only [hab, hadj, ↓reduceIte]
    obtain ⟨p, hp⟩ := sharpnessWalkLeTwo n hn a b
    apply Nat.le_antisymm ((SimpleGraph.dist_le p).trans hp)
    exact (show (sharpnessGraph n).Reachable a b from ⟨p⟩).one_lt_dist_of_ne_of_not_adj hab hadj

def sharpnessX (n : ℕ) (hn : n ≥ 10) : Fin n := ⟨n - 2, by omega⟩

def sharpnessY (n : ℕ) (hn : n ≥ 10) : Fin n := ⟨n - 1, by omega⟩

@[simp] lemma sharpnessX_val (n : ℕ) (hn : n ≥ 10) :
    (sharpnessX n hn).val = n - 2 := rfl

@[simp] lemma sharpnessY_val (n : ℕ) (hn : n ≥ 10) :
    (sharpnessY n hn).val = n - 1 := rfl

def sharpnessXNonneighbors (n : ℕ) (hn : n ≥ 10) : Finset (Fin n) := by
  classical
  exact (sharpnessCore n).erase ⟨0, by omega⟩

def sharpnessYNonneighbors (n : ℕ) (hn : n ≥ 10) : Finset (Fin n) := by
  classical
  exact (sharpnessCore n).erase ⟨1, by omega⟩

def sharpnessOrderedNonedges (n : ℕ) (hn : n ≥ 10) : Finset (Fin n × Fin n) := by
  classical
  exact (sharpnessXNonneighbors n hn).image (fun q => (q, sharpnessX n hn)) ∪
    (sharpnessYNonneighbors n hn).image (fun q => (q, sharpnessY n hn))

lemma sharpnessCoreCard (n : ℕ) (hn : n ≥ 10) :
    (sharpnessCore n).card = n - 2 := by
  let x : Fin n := ⟨n - 2, by omega⟩
  have hcore : sharpnessCore n = Finset.Iio x := by
    ext q
    simp only [sharpnessCore, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Iio]
    change q.val < n - 2 ↔ q.val < x.val
    rfl
  rw [hcore, Fin.card_Iio]

lemma sharpnessXNonneighborsCard (n : ℕ) (hn : n ≥ 10) :
    (sharpnessXNonneighbors n hn).card = n - 3 := by
  have hz : (⟨0, by omega⟩ : Fin n) ∈ sharpnessCore n := by
    simp [sharpnessCore]
    omega
  rw [sharpnessXNonneighbors, Finset.card_erase_of_mem hz,
    sharpnessCoreCard n hn]
  omega

lemma sharpnessYNonneighborsCard (n : ℕ) (hn : n ≥ 10) :
    (sharpnessYNonneighbors n hn).card = n - 3 := by
  have ho : (⟨1, by omega⟩ : Fin n) ∈ sharpnessCore n := by
    simp [sharpnessCore]
    omega
  rw [sharpnessYNonneighbors, Finset.card_erase_of_mem ho,
    sharpnessCoreCard n hn]
  omega

lemma sharpnessOrderedNonedges_eq (n : ℕ) (hn : n ≥ 10) :
    sharpnessOrderedNonedges n hn =
      (theorem1OrderedPairs n).filter fun p => ¬(sharpnessGraph n).Adj p.1 p.2 := by
  classical
  ext p
  simp only [sharpnessOrderedNonedges, Finset.mem_union, Finset.mem_image,
    sharpnessXNonneighbors, sharpnessYNonneighbors, Finset.mem_erase,
    sharpnessCore, Finset.mem_filter, Finset.mem_univ, true_and,
    theorem1OrderedPairs, Finset.mem_offDiag]
  constructor
  · rintro (⟨q, ⟨hq0, hqcore⟩, rfl⟩ | ⟨q, ⟨hq1, hqcore⟩, rfl⟩)
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro hq
        have := congrArg Fin.val hq
        simp at this
        omega
      · change q.val < (sharpnessX n hn).val
        simpa using hqcore
      simp only [sharpnessGraph]
      intro h
      have hxval : (sharpnessX n hn).val = n - 2 := rfl
      rcases h.2 with h | h | h | h | h | h | h
      · omega
      · omega
      · apply hq0
        apply Fin.ext
        simpa using h.2
      · omega
      · omega
      · omega
      · omega
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro hq
        have := congrArg Fin.val hq
        simp at this
        omega
      · change q.val < (sharpnessY n hn).val
        simp
        omega
      simp only [sharpnessGraph]
      intro h
      have hyval : (sharpnessY n hn).val = n - 1 := rfl
      rcases h.2 with h | h | h | h | h | h | h
      · omega
      · omega
      · omega
      · omega
      · apply hq1
        apply Fin.ext
        simpa using h.2
      · omega
      · omega
  · rintro ⟨⟨hpne, hplt⟩, hnadj⟩
    have hpltv : p.1.val < p.2.val := hplt
    have hnew : p.2.val = n - 2 ∨ p.2.val = n - 1 := by
      by_contra h
      apply hnadj
      exact ⟨hpne, Or.inl ⟨by omega, by omega⟩⟩
    rcases hnew with hp2 | hp2
    · left
      refine ⟨p.1, ?_, ?_⟩
      · constructor
        · intro hp10
          have hp10v := congrArg Fin.val hp10
          apply hnadj
          exact ⟨hpne, Or.inr (Or.inr (Or.inl ⟨hp2, by simpa using hp10v⟩))⟩
        · omega
      · apply Prod.ext
        · rfl
        · apply Fin.ext
          simp [hp2]
    · right
      refine ⟨p.1, ?_, ?_⟩
      · constructor
        · intro hp11
          have hp11v := congrArg Fin.val hp11
          apply hnadj
          exact ⟨hpne, Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨hp2, by simpa using hp11v⟩))))⟩
        · by_contra hcore
          apply hnadj
          exact ⟨hpne, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨by omega, hp2⟩)))))⟩
      · apply Prod.ext
        · rfl
        · apply Fin.ext
          simp [hp2]

lemma sharpnessOrderedNonedgesCard (n : ℕ) (hn : n ≥ 10) :
    (sharpnessOrderedNonedges n hn).card = 2 * n - 6 := by
  classical
  have hdisjoint : Disjoint
      ((sharpnessXNonneighbors n hn).image (fun q => (q, sharpnessX n hn)))
      ((sharpnessYNonneighbors n hn).image (fun q => (q, sharpnessY n hn))) := by
    rw [Finset.disjoint_left]
    intro p hpX hpY
    rcases Finset.mem_image.mp hpX with ⟨q, hq, rfl⟩
    rcases Finset.mem_image.mp hpY with ⟨r, hr, hpair⟩
    have hsnd := congrArg Prod.snd hpair
    have hval := congrArg Fin.val hsnd
    simp at hval
    omega
  unfold sharpnessOrderedNonedges
  rw [Finset.card_union_of_disjoint hdisjoint,
    Finset.card_image_of_injective _ (fun _ _ h => Prod.mk.inj h |>.1),
    Finset.card_image_of_injective _ (fun _ _ h => Prod.mk.inj h |>.1),
    sharpnessXNonneighborsCard n hn, sharpnessYNonneighborsCard n hn]
  omega

lemma sharpnessWienerIndexNat (n : ℕ) (hn : n ≥ 10) :
    wienerIndex (sharpnessGraph n) = n.choose 2 + (2 * n - 6) := by
  unfold wienerIndex
  rw [sumSym2EqSumOrdered]
  · change (∑ p ∈ theorem1OrderedPairs n,
      (sharpnessGraph n).dist p.1 p.2) = _
    calc
      _ = ∑ p ∈ theorem1OrderedPairs n,
          (1 + if ¬(sharpnessGraph n).Adj p.1 p.2 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hne : p.1 ≠ p.2 :=
          (Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1).2.2
        rw [sharpnessDist n hn]
        simp only [hne, ↓reduceIte]
        by_cases h : (sharpnessGraph n).Adj p.1 p.2 <;> simp [h]
      _ = (theorem1OrderedPairs n).card +
          ((theorem1OrderedPairs n).filter fun p =>
            ¬(sharpnessGraph n).Adj p.1 p.2).card := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 1
        simpa using (Finset.sum_boole (R := ℕ)
          (fun p : Fin n × Fin n => ¬(sharpnessGraph n).Adj p.1 p.2)
          (theorem1OrderedPairs n))
      _ = n.choose 2 + (2 * n - 6) := by
        rw [theorem1OrderedPairsCard, ← sharpnessOrderedNonedges_eq n hn,
          sharpnessOrderedNonedgesCard n hn]
  · intro a
    exact SimpleGraph.dist_self

/-- `G_n` has diameter two and exactly `2n-6` nonedges, giving the displayed
Wiener-index formula from the manuscript. -/
theorem lemma7Proof2 (n : ℕ) (h_order : n ≥ 10) :
    (wienerIndex (sharpnessGraph n) : ℤ) =
      ((n : ℤ) ^ 2 + 3 * n - 12) / 2 := by
  rw [sharpnessWienerIndexNat n h_order]
  have hchooseNat : 2 * n.choose 2 = n * (n - 1) := by
    rw [Nat.choose_two_right]
    apply Nat.mul_div_cancel'
    rcases Nat.even_mul_pred_self n with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hchooseInt : 2 * (n.choose 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
    have hi := congrArg (fun x : ℕ => (x : ℤ)) hchooseNat
    push_cast at hi
    rw [Nat.cast_sub (by omega : 1 ≤ n)] at hi
    exact hi
  have hpoly :
      (n : ℤ) ^ 2 + 3 * n - 12 =
        2 * ((n.choose 2 : ℤ) + (2 * n - 6 : ℕ)) := by
    rw [Nat.cast_sub (by omega : 6 ≤ 2 * n), Nat.cast_mul]
    calc
      (n : ℤ) ^ 2 + 3 * n - 12 =
          (n : ℤ) * ((n : ℤ) - 1) + 4 * n - 12 := by ring
      _ = 2 * (n.choose 2 : ℤ) + 4 * n - 12 := by rw [hchooseInt]
      _ = 2 * ((n.choose 2 : ℤ) + (2 * (n : ℤ) - 6)) := by ring
  push_cast
  symm
  apply (Int.ediv_eq_iff_eq_mul_left (by norm_num : (2 : ℤ) ≠ 0)
    ⟨((n.choose 2 : ℤ) + (2 * n - 6 : ℕ)), by rw [hpoly]⟩).2
  rw [hpoly]
  ring

def sharpnessA (n : ℕ) (hn : n ≥ 10) : Fin n := ⟨0, by omega⟩

def sharpnessB (n : ℕ) (hn : n ≥ 10) : Fin n := ⟨1, by omega⟩

@[simp] lemma sharpnessA_val (n : ℕ) (hn : n ≥ 10) :
    (sharpnessA n hn).val = 0 := rfl

@[simp] lemma sharpnessB_val (n : ℕ) (hn : n ≥ 10) :
    (sharpnessB n hn).val = 1 := rfl

lemma sharpnessCloserOrdinary
    (n : ℕ) (hn : n ≥ 10) (c d : Fin n)
    (hc : 2 ≤ c.val) (hc' : c.val < n - 2)
    (hd : 2 ≤ d.val) (hd' : d.val < n - 2) (hcd : c ≠ d) :
    closerCount (sharpnessGraph n) c d = 1 ∧
      closerCount (sharpnessGraph n) d c = 1 := by
  have hset (r s : Fin n) (hr : 2 ≤ r.val) (hr' : r.val < n - 2)
      (hs : 2 ≤ s.val) (hs' : s.val < n - 2) (hrs : r ≠ s) :
      closerVertices (sharpnessGraph n) r s = {r} := by
    ext z
    simp only [closerVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    rw [sharpnessDist n hn, sharpnessDist n hn]
    by_cases hzr : z = r
    · subst z
      have hrsadj : (sharpnessGraph n).Adj r s :=
        ⟨hrs, Or.inl ⟨hr', hs'⟩⟩
      simp [hrs, hrsadj]
    by_cases hzs : z = s
    · subst z
      have hsrAdj : (sharpnessGraph n).Adj s r :=
        ⟨hrs.symm, Or.inl ⟨hs', hr'⟩⟩
      simp [hrs.symm, hzr, hsrAdj]
    simp only [hzr, hzs, ↓reduceIte]
    have hzrAdj : (sharpnessGraph n).Adj z r ↔ z.val < n - 2 := by
      simp only [sharpnessGraph]
      constructor
      · rintro ⟨_, h | h | h | h | h | h | h⟩
        · exact h.1
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
      · intro hz
        exact ⟨hzr, Or.inl ⟨hz, hr'⟩⟩
    have hzsAdj : (sharpnessGraph n).Adj z s ↔ z.val < n - 2 := by
      simp only [sharpnessGraph]
      constructor
      · rintro ⟨_, h | h | h | h | h | h | h⟩
        · exact h.1
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
      · intro hz
        exact ⟨hzs, Or.inl ⟨hz, hs'⟩⟩
    simp [hzrAdj, hzsAdj]
  constructor <;> unfold closerCount
  · rw [hset c d hc hc' hd hd' hcd]
    simp
  · rw [hset d c hd hd' hc hc' hcd.symm]
    simp

lemma sharpnessCloserAOrdinary
    (n : ℕ) (hn : n ≥ 10) (c : Fin n)
    (hc : 2 ≤ c.val) (hc' : c.val < n - 2) :
    closerCount (sharpnessGraph n) (sharpnessA n hn) c = 2 ∧
      closerCount (sharpnessGraph n) c (sharpnessA n hn) = 1 := by
  let a := sharpnessA n hn
  let x := sharpnessX n hn
  have haval : a.val = 0 := by simp [a]
  have hxval : x.val = n - 2 := by simp [x]
  have hac : (sharpnessGraph n).Adj a c := by
    refine ⟨?_, Or.inl ⟨by simp [a]; omega, hc'⟩⟩
    intro h
    have := congrArg Fin.val h
    simp [a] at this
    omega
  have hxa : (sharpnessGraph n).Adj x a := by
    refine ⟨?_, Or.inr (Or.inl ⟨by simp [x], by simp [a]⟩)⟩
    intro h
    have := congrArg Fin.val h
    simp [a, x] at this
    omega
  have hxc : ¬(sharpnessGraph n).Adj x c := by
    rintro ⟨_, h | h | h | h | h | h | h⟩ <;>
      simp [a, x] at h <;> omega
  have hacne : a ≠ c := hac.ne
  have hcx : c ≠ x := by
    intro h
    have := congrArg Fin.val h
    simp [x] at this
    omega
  have hax : a ≠ x := by
    intro h
    have := congrArg Fin.val h
    simp [a, x] at this
    omega
  have hleft : closerVertices (sharpnessGraph n) a c = {a, x} := by
    ext z
    simp only [closerVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    rw [sharpnessDist n hn, sharpnessDist n hn]
    by_cases hza : z = a
    · subst z
      simp [hac, hacne]
    by_cases hzc : z = c
    · subst z
      simp [hac.symm, hza, hcx]
    by_cases hzx : z = x
    · subst z
      simp [hxa, hxc, hza, hzc]
    simp only [hza, hzc, hzx, false_or, ↓reduceIte]
    have hzaAdj : (sharpnessGraph n).Adj z a ↔ z.val < n - 2 := by
      simp only [sharpnessGraph]
      constructor
      · rintro ⟨_, h | h | h | h | h | h | h⟩
        · exact h.1
        · exfalso
          apply hzx
          apply Fin.ext
          simp [x]
          omega
        · omega
        · omega
        · omega
        · omega
        · omega
      · intro hz
        exact ⟨hza, Or.inl ⟨hz, by simp [a]; omega⟩⟩
    have hzcAdj : (sharpnessGraph n).Adj z c ↔ z.val < n - 2 := by
      simp only [sharpnessGraph]
      constructor
      · rintro ⟨_, h | h | h | h | h | h | h⟩ <;> omega
      · intro hz
        exact ⟨hzc, Or.inl ⟨hz, hc'⟩⟩
    simp [hzaAdj, hzcAdj]
  have hright : closerVertices (sharpnessGraph n) c a = {c} := by
    ext z
    simp only [closerVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    rw [sharpnessDist n hn, sharpnessDist n hn]
    by_cases hzc : z = c
    · subst z
      simp [hac.symm, hacne.symm]
    by_cases hza : z = a
    · subst z
      simp [hac, hzc]
    by_cases hzx : z = x
    · subst z
      simp [hxa, hxc, hzc, hza]
    simp only [hzc, hza, hzx, ↓reduceIte]
    have hzaAdj : (sharpnessGraph n).Adj z a ↔ z.val < n - 2 := by
      simp only [sharpnessGraph]
      constructor
      · rintro ⟨_, h | h | h | h | h | h | h⟩
        · exact h.1
        · exfalso
          apply hzx
          apply Fin.ext
          omega
        · omega
        · omega
        · omega
        · omega
        · omega
      · intro hz
        exact ⟨hza, Or.inl ⟨hz, by simp [a]; omega⟩⟩
    have hzcAdj : (sharpnessGraph n).Adj z c ↔ z.val < n - 2 := by
      simp only [sharpnessGraph]
      constructor
      · rintro ⟨_, h | h | h | h | h | h | h⟩ <;> omega
      · intro hz
        exact ⟨hzc, Or.inl ⟨hz, hc'⟩⟩
    simp [hzaAdj, hzcAdj]
  constructor <;> unfold closerCount
  · rw [hleft]
    simp [hax]
  · rw [hright]
    simp

lemma sharpnessCloserAnchorOrdinary
    (n : ℕ) (hn : n ≥ 10) (a x c : Fin n)
    (hac : (sharpnessGraph n).Adj a c)
    (hxa : (sharpnessGraph n).Adj x a)
    (hxc : ¬(sharpnessGraph n).Adj x c)
    (hcx : c ≠ x)
    (hadjA : ∀ z, z ≠ a → z ≠ x →
      ((sharpnessGraph n).Adj z a ↔ z.val < n - 2))
    (hadjC : ∀ z, z ≠ c →
      ((sharpnessGraph n).Adj z c ↔ z.val < n - 2)) :
    closerCount (sharpnessGraph n) a c = 2 ∧
      closerCount (sharpnessGraph n) c a = 1 := by
  have hacne : a ≠ c := hac.ne
  have hax : a ≠ x := hxa.ne.symm
  have hleft : closerVertices (sharpnessGraph n) a c = {a, x} := by
    ext z
    simp only [closerVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    rw [sharpnessDist n hn, sharpnessDist n hn]
    by_cases hza : z = a
    · subst z
      simp [hac, hacne]
    by_cases hzc : z = c
    · subst z
      simp [hac.symm, hza, hcx]
    by_cases hzx : z = x
    · subst z
      simp [hxa, hxc, hza, hzc]
    simp [hza, hzc, hzx, hadjA z hza hzx, hadjC z hzc]
  have hright : closerVertices (sharpnessGraph n) c a = {c} := by
    ext z
    simp only [closerVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    rw [sharpnessDist n hn, sharpnessDist n hn]
    by_cases hzc : z = c
    · subst z
      simp [hac.symm, hacne.symm]
    by_cases hza : z = a
    · subst z
      simp [hac, hzc]
    by_cases hzx : z = x
    · subst z
      simp [hxa, hxc, hzc, hza]
    simp [hza, hzc, hzx, hadjA z hza hzx, hadjC z hzc]
  constructor <;> unfold closerCount
  · rw [hleft]
    simp [hax]
  · rw [hright]
    simp

lemma sharpnessCloserBOrdinary
    (n : ℕ) (hn : n ≥ 10) (c : Fin n)
    (hc : 2 ≤ c.val) (hc' : c.val < n - 2) :
    closerCount (sharpnessGraph n) (sharpnessB n hn) c = 2 ∧
      closerCount (sharpnessGraph n) c (sharpnessB n hn) = 1 := by
  let b := sharpnessB n hn
  let y := sharpnessY n hn
  have hbval : b.val = 1 := by simp [b]
  have hyval : y.val = n - 1 := by simp [y]
  have hyb : y ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [b, y] at this
    omega
  have hcy : c ≠ y := by
    intro h
    have := congrArg Fin.val h
    simp [y] at this
    omega
  have hac : (sharpnessGraph n).Adj b c := by
    refine ⟨?_, Or.inl ⟨by simp [b]; omega, hc'⟩⟩
    intro h
    have := congrArg Fin.val h
    simp [b] at this
    omega
  have hya : (sharpnessGraph n).Adj y b := by
    exact ⟨hyb, Or.inr (Or.inr (Or.inr
      (Or.inl ⟨by simp [y], by simp [b]⟩)))⟩
  have hyc : ¬(sharpnessGraph n).Adj y c := by
    rintro ⟨_, h | h | h | h | h | h | h⟩ <;>
      simp [b, y] at h <;> omega
  apply sharpnessCloserAnchorOrdinary n hn b y c hac hya hyc hcy
  · intro z hzb hzy
    simp only [sharpnessGraph]
    constructor
    · rintro ⟨_, h | h | h | h | h | h | h⟩
      · exact h.1
      · omega
      · omega
      · exfalso
        apply hzy
        apply Fin.ext
        simp [y]
        omega
      · omega
      · omega
      · omega
    · intro hz
      exact ⟨hzb, Or.inl ⟨hz, by simp [b]; omega⟩⟩
  · intro z hzc
    simp only [sharpnessGraph]
    constructor
    · rintro ⟨_, h | h | h | h | h | h | h⟩ <;> omega
    · intro hz
      exact ⟨hzc, Or.inl ⟨hz, hc'⟩⟩

lemma sharpnessCloserAB (n : ℕ) (hn : n ≥ 10) :
    closerCount (sharpnessGraph n) (sharpnessA n hn) (sharpnessB n hn) = 2 ∧
      closerCount (sharpnessGraph n) (sharpnessB n hn) (sharpnessA n hn) = 2 := by
  let a := sharpnessA n hn
  let b := sharpnessB n hn
  let x := sharpnessX n hn
  let y := sharpnessY n hn
  have haval : a.val = 0 := by simp [a]
  have hbval : b.val = 1 := by simp [b]
  have hxval : x.val = n - 2 := by simp [x]
  have hyval : y.val = n - 1 := by simp [y]
  have hbx : b ≠ x := by
    intro h
    have := congrArg Fin.val h
    omega
  have hay : a ≠ y := by
    intro h
    have := congrArg Fin.val h
    omega
  have hab : (sharpnessGraph n).Adj a b := by
    refine ⟨?_, Or.inl ⟨by simp [a]; omega, by simp [b]; omega⟩⟩
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  have hxa : (sharpnessGraph n).Adj x a := by
    refine ⟨?_, Or.inr (Or.inl ⟨by simp [x], by simp [a]⟩)⟩
    intro h
    have := congrArg Fin.val h
    simp [x, a] at this
    omega
  have hyb : (sharpnessGraph n).Adj y b := by
    refine ⟨?_, Or.inr (Or.inr (Or.inr
      (Or.inl ⟨by simp [y], by simp [b]⟩)))⟩
    intro h
    have := congrArg Fin.val h
    simp [y, b] at this
    omega
  have hxb : ¬(sharpnessGraph n).Adj x b := by
    rintro ⟨_, h | h | h | h | h | h | h⟩ <;>
      simp [a, b, x, y] at h <;> omega
  have hya : ¬(sharpnessGraph n).Adj y a := by
    rintro ⟨_, h | h | h | h | h | h | h⟩ <;>
      simp [a, b, x, y] at h <;> omega
  have hset (r s tip : Fin n)
      (hrs : (sharpnessGraph n).Adj r s)
      (htipr : (sharpnessGraph n).Adj tip r)
      (htips : ¬(sharpnessGraph n).Adj tip s)
      (hst : s ≠ tip)
      (hcommon : ∀ z, z ≠ r → z ≠ s → z ≠ tip →
        (sharpnessGraph n).Adj z r → (sharpnessGraph n).Adj z s) :
      closerVertices (sharpnessGraph n) r s = {r, tip} := by
    ext z
    simp only [closerVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    rw [sharpnessDist n hn, sharpnessDist n hn]
    by_cases hzr : z = r
    · subst z
      simp [hrs, hrs.ne]
    by_cases hzs : z = s
    · subst z
      simp [hrs.symm, hzr, hst]
    by_cases hzt : z = tip
    · subst z
      simp [htipr, htips, hzr, hzs]
    by_cases hzradj : (sharpnessGraph n).Adj z r
    · have hzsadj := hcommon z hzr hzs hzt hzradj
      simp [hzr, hzs, hzt, hzradj, hzsadj]
    · by_cases hzsadj : (sharpnessGraph n).Adj z s <;>
        simp [hzr, hzs, hzt, hzradj, hzsadj]
  have hcommonAB : ∀ z, z ≠ a → z ≠ b → z ≠ x →
      (sharpnessGraph n).Adj z a → (sharpnessGraph n).Adj z b := by
    intro z hza hzb hzx
    simp only [sharpnessGraph]
    rintro ⟨_, h | h | h | h | h | h | h⟩
    · exact ⟨hzb, Or.inl ⟨h.1, by simp [b]; omega⟩⟩
    · exact False.elim (hzx (Fin.ext (by simp [x]; omega)))
    · omega
    · omega
    · omega
    · omega
    · omega
  have hcommonBA : ∀ z, z ≠ b → z ≠ a → z ≠ y →
      (sharpnessGraph n).Adj z b → (sharpnessGraph n).Adj z a := by
    intro z hzb hza hzy
    simp only [sharpnessGraph]
    rintro ⟨_, h | h | h | h | h | h | h⟩
    · exact ⟨hza, Or.inl ⟨h.1, by simp [a]; omega⟩⟩
    · omega
    · omega
    · exact False.elim (hzy (Fin.ext (by simp [y]; omega)))
    · omega
    · omega
    · omega
  have hl := hset a b x hab hxa hxb hbx hcommonAB
  have hr := hset b a y hab.symm hyb hya hay hcommonBA
  constructor <;> unfold closerCount
  · rw [hl]
    have hax : a ≠ x := hxa.ne.symm
    simp [hax]
  · rw [hr]
    have hby : b ≠ y := hyb.ne.symm
    simp [hby]

lemma sharpnessCloserAX (n : ℕ) (hn : n ≥ 10) :
    closerCount (sharpnessGraph n) (sharpnessA n hn) (sharpnessX n hn) = n - 2 ∧
      closerCount (sharpnessGraph n) (sharpnessX n hn) (sharpnessA n hn) = 2 := by
  let a := sharpnessA n hn
  let x := sharpnessX n hn
  let y := sharpnessY n hn
  have haval : a.val = 0 := by simp [a]
  have hxval : x.val = n - 2 := by simp [x]
  have hyval : y.val = n - 1 := by simp [y]
  have hax : (sharpnessGraph n).Adj a x := by
    refine ⟨?_, Or.inr (Or.inr (Or.inl ⟨by simp [x], by simp [a]⟩))⟩
    intro h
    have := congrArg Fin.val h
    simp [a, x] at this
    omega
  have hxy : (sharpnessGraph n).Adj x y := by
    refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨by simp [x], by simp [y]⟩)))))⟩
    intro h
    have := congrArg Fin.val h
    simp [x, y] at this
    omega
  have hay : ¬(sharpnessGraph n).Adj a y := by
    rintro ⟨_, h | h | h | h | h | h | h⟩ <;>
      simp [a, x, y] at h <;> omega
  have hya : ¬(sharpnessGraph n).Adj y a := fun h => hay h.symm
  have hyane : y ≠ a := by
    intro h
    have := congrArg Fin.val h
    omega
  have haxne : a ≠ x := hax.ne
  have hxyne : x ≠ y := hxy.ne
  have hleft : closerVertices (sharpnessGraph n) a x = sharpnessCore n := by
    ext z
    simp only [closerVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      sharpnessCore]
    rw [sharpnessDist n hn, sharpnessDist n hn]
    by_cases hzcore : z.val < n - 2
    · by_cases hza : z = a
      · subst z
        have hacore : a.val < n - 2 := by omega
        simp [hax, haxne, hacore]
      · have hzaAdj : (sharpnessGraph n).Adj z a :=
          ⟨hza, Or.inl ⟨hzcore, by simp [a]; omega⟩⟩
        have hzxAdj : ¬(sharpnessGraph n).Adj z x := by
          rintro ⟨_, h | h | h | h | h | h | h⟩ <;>
            simp [a, x, y] at h <;> omega
        have hzx : z ≠ x := by
          intro h
          have := congrArg Fin.val h
          omega
        simp [hzcore, hza, hzx, hzaAdj, hzxAdj]
    · have hzcase : z = x ∨ z = y := by
        have hv : z.val = n - 2 ∨ z.val = n - 1 := by omega
        rcases hv with hv | hv
        · exact Or.inl (Fin.ext (by simp [x, hv]))
        · exact Or.inr (Fin.ext (by simp [y, hv]))
      rcases hzcase with rfl | rfl
      · simp [hzcore, hax.symm, haxne.symm]
      · simp [hzcore, hxy.symm, hya, hxyne.symm, hyane]
  have hright : closerVertices (sharpnessGraph n) x a = {x, y} := by
    ext z
    have hz := Finset.ext_iff.mp hleft z
    simp only [closerVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      sharpnessCore, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    have hzcase : z.val < n - 2 ∨ z = x ∨ z = y := by
      by_cases hcore : z.val < n - 2
      · exact Or.inl hcore
      · have hv : z.val = n - 2 ∨ z.val = n - 1 := by omega
        rcases hv with hv | hv
        · exact Or.inr (Or.inl (Fin.ext (by omega)))
        · exact Or.inr (Or.inr (Fin.ext (by omega)))
    rcases hzcase with hzcore | hzx | hzy
    · constructor
      · intro hrev
        have hfwd := hz.mpr hzcore
        omega
      · rintro (h | h)
        · have := congrArg Fin.val h
          omega
        · have := congrArg Fin.val h
          omega
    · subst z
      rw [sharpnessDist n hn, sharpnessDist n hn]
      simp [hax.symm, haxne.symm, hxyne]
    · subst z
      rw [sharpnessDist n hn, sharpnessDist n hn]
      simp [hxy.symm, hya, hxyne.symm, hyane]
  constructor <;> unfold closerCount
  · rw [hleft, sharpnessCoreCard n hn]
  · rw [hright]
    simp [hxyne]

lemma sharpnessCloserBY (n : ℕ) (hn : n ≥ 10) :
    closerCount (sharpnessGraph n) (sharpnessB n hn) (sharpnessY n hn) = n - 2 ∧
      closerCount (sharpnessGraph n) (sharpnessY n hn) (sharpnessB n hn) = 2 := by
  let b := sharpnessB n hn
  let x := sharpnessX n hn
  let y := sharpnessY n hn
  have hbval : b.val = 1 := by simp [b]
  have hxval : x.val = n - 2 := by simp [x]
  have hyval : y.val = n - 1 := by simp [y]
  have hby : (sharpnessGraph n).Adj b y := by
    refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨by simp [y], by simp [b]⟩))))⟩
    intro h
    have := congrArg Fin.val h
    omega
  have hxy : (sharpnessGraph n).Adj x y := by
    refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨by simp [x], by simp [y]⟩)))))⟩
    intro h
    have := congrArg Fin.val h
    omega
  have hbx : ¬(sharpnessGraph n).Adj b x := by
    rintro ⟨_, h | h | h | h | h | h | h⟩ <;>
      simp [b, x, y] at h <;> omega
  have hleft : closerVertices (sharpnessGraph n) b y = sharpnessCore n := by
    ext z
    simp only [closerVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      sharpnessCore]
    rw [sharpnessDist n hn, sharpnessDist n hn]
    by_cases hzcore : z.val < n - 2
    · by_cases hzb : z = b
      · subst z
        have hbcore : b.val < n - 2 := by omega
        simp [hby, hby.ne, hbcore]
      · have hzbAdj : (sharpnessGraph n).Adj z b :=
          ⟨hzb, Or.inl ⟨hzcore, by simp [b]; omega⟩⟩
        have hzyAdj : ¬(sharpnessGraph n).Adj z y := by
          rintro ⟨_, h | h | h | h | h | h | h⟩ <;>
            simp [b, x, y] at h <;> omega
        have hzy : z ≠ y := by
          intro h
          have := congrArg Fin.val h
          omega
        simp [hzcore, hzb, hzy, hzbAdj, hzyAdj]
    · have hzcase : z = x ∨ z = y := by
        have hv : z.val = n - 2 ∨ z.val = n - 1 := by omega
        rcases hv with hv | hv
        · exact Or.inl (Fin.ext (by omega))
        · exact Or.inr (Fin.ext (by omega))
      rcases hzcase with rfl | rfl
      · have hxb : ¬(sharpnessGraph n).Adj x b := fun h => hbx h.symm
        have hxbne : x ≠ b := by
          intro h
          have := congrArg Fin.val h
          omega
        simp [hzcore, hxy, hxb, hxbne, hxy.ne]
      · have hybne : y ≠ b := hby.ne.symm
        simp [hzcore, hby.symm, hybne]
  have hright : closerVertices (sharpnessGraph n) y b = {x, y} := by
    ext z
    have hz := Finset.ext_iff.mp hleft z
    simp only [closerVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      sharpnessCore, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    have hzcase : z.val < n - 2 ∨ z = x ∨ z = y := by
      by_cases hcore : z.val < n - 2
      · exact Or.inl hcore
      · have hv : z.val = n - 2 ∨ z.val = n - 1 := by omega
        rcases hv with hv | hv
        · exact Or.inr (Or.inl (Fin.ext (by omega)))
        · exact Or.inr (Or.inr (Fin.ext (by omega)))
    rcases hzcase with hzcore | hzx | hzy
    · constructor
      · intro hrev
        have hfwd := hz.mpr hzcore
        omega
      · rintro (h | h)
        · have := congrArg Fin.val h
          omega
        · have := congrArg Fin.val h
          omega
    · subst z
      rw [sharpnessDist n hn, sharpnessDist n hn]
      have hxyne := hxy.ne
      have hxb : ¬(sharpnessGraph n).Adj x b := fun h => hbx h.symm
      have hxbne : x ≠ b := by
        intro h
        have := congrArg Fin.val h
        omega
      simp [hxy, hxb, hxbne, hxyne]
    · subst z
      rw [sharpnessDist n hn, sharpnessDist n hn]
      simp [hby.symm, hby.ne.symm]
  constructor <;> unfold closerCount
  · rw [hleft, sharpnessCoreCard n hn]
  · rw [hright]
    simp [hxy.ne]

lemma sharpnessCloserXY (n : ℕ) (hn : n ≥ 10) :
    closerCount (sharpnessGraph n) (sharpnessX n hn) (sharpnessY n hn) = 2 ∧
      closerCount (sharpnessGraph n) (sharpnessY n hn) (sharpnessX n hn) = 2 := by
  let a := sharpnessA n hn
  let b := sharpnessB n hn
  let x := sharpnessX n hn
  let y := sharpnessY n hn
  have hxy : (sharpnessGraph n).Adj x y := by
    refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨by simp [x], by simp [y]⟩)))))⟩
    intro h
    have := congrArg Fin.val h
    simp [x, y] at this
    omega
  have hxa : (sharpnessGraph n).Adj x a := by
    refine ⟨?_, Or.inr (Or.inl ⟨by simp [x], by simp [a]⟩)⟩
    intro h
    have := congrArg Fin.val h
    simp [x, a] at this
    omega
  have hya : ¬(sharpnessGraph n).Adj y a := by
    rintro ⟨_, h | h | h | h | h | h | h⟩ <;>
      simp [a, b, x, y] at h <;> omega
  have hyb : (sharpnessGraph n).Adj y b := by
    refine ⟨?_, Or.inr (Or.inr (Or.inr
      (Or.inl ⟨by simp [y], by simp [b]⟩)))⟩
    intro h
    have := congrArg Fin.val h
    simp [y, b] at this
    omega
  have hxb : ¬(sharpnessGraph n).Adj x b := by
    rintro ⟨_, h | h | h | h | h | h | h⟩ <;>
      simp [a, b, x, y] at h <;> omega
  have hset (r s q : Fin n) (hrs : (sharpnessGraph n).Adj r s)
      (hqr : (sharpnessGraph n).Adj q r) (hqs : ¬(sharpnessGraph n).Adj q s)
      (hsq : s ≠ q)
      (hcommon : ∀ z, z ≠ r → z ≠ s → z ≠ q →
        (sharpnessGraph n).Adj z r → (sharpnessGraph n).Adj z s) :
      closerVertices (sharpnessGraph n) r s = {r, q} := by
    ext z
    simp only [closerVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    rw [sharpnessDist n hn, sharpnessDist n hn]
    by_cases hzr : z = r
    · subst z
      simp [hrs, hrs.ne]
    by_cases hzq : z = q
    · subst z
      simp [hqr, hqs, hzr, hsq.symm]
    by_cases hzs : z = s
    · subst z
      simp [hrs.symm, hzr, hzq]
    by_cases hzrAdj : (sharpnessGraph n).Adj z r
    · have hzsAdj := hcommon z hzr hzs hzq hzrAdj
      simp [hzr, hzq, hzs, hzrAdj, hzsAdj]
    · by_cases hzsAdj : (sharpnessGraph n).Adj z s <;>
        simp [hzr, hzq, hzs, hzrAdj, hzsAdj]
  have hcommonXY : ∀ z, z ≠ x → z ≠ y → z ≠ a →
      (sharpnessGraph n).Adj z x → (sharpnessGraph n).Adj z y := by
    intro z hzx hzy hza
    simp only [sharpnessGraph]
    rintro ⟨_, h | h | h | h | h | h | h⟩
    · simp [x] at h
    · simp [x] at h
      omega
    · exact False.elim (hza (Fin.ext (by simp [a]; omega)))
    · simp [x] at h
      omega
    · simp [x] at h
      omega
    · simp [x] at h
      omega
    · exact False.elim (hzy (Fin.ext (by simp [x, y] at h ⊢; omega)))
  have hcommonYX : ∀ z, z ≠ y → z ≠ x → z ≠ b →
      (sharpnessGraph n).Adj z y → (sharpnessGraph n).Adj z x := by
    intro z hzy hzx hzb
    simp only [sharpnessGraph]
    rintro ⟨_, h | h | h | h | h | h | h⟩
    · simp [y] at h
      omega
    · simp [y] at h
      omega
    · simp [y] at h
      omega
    · simp [y] at h
      omega
    · exact False.elim (hzb (Fin.ext (by simp [b, y] at h ⊢; omega)))
    · exact False.elim (hzx (Fin.ext (by simp [x, y] at h ⊢; omega)))
    · simp [y] at h
      omega
  have hya_ne : y ≠ a := by
    intro h
    have : n - 1 = 0 := by simpa [y, a] using congrArg Fin.val h
    omega
  have hxb_ne : x ≠ b := by
    intro h
    have : n - 2 = 1 := by simpa [x, b] using congrArg Fin.val h
    omega
  have hl := hset x y a hxy hxa.symm (fun h => hya h.symm) hya_ne hcommonXY
  have hr := hset y x b hxy.symm hyb.symm (fun h => hxb h.symm) hxb_ne hcommonYX
  constructor <;> unfold closerCount
  · rw [hl]
    simp [hxa.ne]
  · rw [hr]
    simp [hyb.ne]

end
end BKLPS
