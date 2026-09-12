import Proof.Lemma7Proof1
import Proof.Lemma7Proof2
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Data.Sym.Card
import Mathlib.Order.Interval.Finset.Fin

/-! Szeged-index computation and assembly of the sharpness example. -/

namespace BKLPS

open SimpleGraph

noncomputable section

open scoped BigOperators

/-- Ordered edges with both ends in the set `A = V(Q) \ {a,b}`. -/
def sharpnessOrdinaryPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (sharpnessOrdinaryCore n).offDiag.filter fun p => p.1 < p.2

/-- The edges from `a` to the ordinary vertices of the core. -/
def sharpnessAOrdinaryEdges (n : ℕ) (hn : n ≥ 10) : Finset (Fin n × Fin n) :=
  (sharpnessOrdinaryCore n).image fun q => (sharpnessA n hn, q)

/-- The edges from `b` to the ordinary vertices of the core. -/
def sharpnessBOrdinaryEdges (n : ℕ) (hn : n ≥ 10) : Finset (Fin n × Fin n) :=
  (sharpnessOrdinaryCore n).image fun q => (sharpnessB n hn, q)

/-- The core edge `ab` and the three edges outside the core. -/
def sharpnessSpecialEdges (n : ℕ) (hn : n ≥ 10) : Finset (Fin n × Fin n) :=
  {(sharpnessA n hn, sharpnessB n hn),
    (sharpnessA n hn, sharpnessX n hn),
    (sharpnessB n hn, sharpnessY n hn),
    (sharpnessX n hn, sharpnessY n hn)}

/-- The seven edge classes from the manuscript, represented with increasing
endpoints so that each unordered edge occurs exactly once. -/
def sharpnessEdgeClasses (n : ℕ) (hn : n ≥ 10) : Finset (Fin n × Fin n) :=
  sharpnessOrdinaryPairs n ∪
    sharpnessAOrdinaryEdges n hn ∪
    sharpnessBOrdinaryEdges n hn ∪
    sharpnessSpecialEdges n hn

private lemma orderedPairsOfCard {α : Type} [LinearOrder α] (s : Finset α) :
    (s.offDiag.filter fun p => p.1 < p.2).card = s.card.choose 2 := by
  have h := Finset.sum_sym2_filter_not_isDiag s (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have himage : s.sym2.filter (fun p => ¬p.IsDiag) =
      s.offDiag.image Sym2.mk := by
    rw [Finset.sym2_eq_image, Sym2.filter_image_mk_not_isDiag]
  rw [himage, Sym2.card_image_offDiag] at h
  exact h.symm

lemma sharpnessOrdinaryCoreCard (n : ℕ) (hn : n ≥ 10) :
    (sharpnessOrdinaryCore n).card = n - 4 := by
  let lo : Fin n := ⟨2, by omega⟩
  let hi : Fin n := ⟨n - 2, by omega⟩
  have hset : sharpnessOrdinaryCore n = Finset.Ico lo hi := by
    ext q
    simp only [sharpnessOrdinaryCore, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_Ico]
    change (2 ≤ q.val ∧ q.val < n - 2) ↔ lo.val ≤ q.val ∧ q.val < hi.val
    rfl
  rw [hset, Fin.card_Ico]
  simp [lo, hi]
  omega

lemma sharpnessOrdinaryPairsCard (n : ℕ) (hn : n ≥ 10) :
    (sharpnessOrdinaryPairs n).card = (n - 4).choose 2 := by
  rw [sharpnessOrdinaryPairs, orderedPairsOfCard,
    sharpnessOrdinaryCoreCard n hn]

lemma sharpnessAOrdinaryEdgesCard (n : ℕ) (hn : n ≥ 10) :
    (sharpnessAOrdinaryEdges n hn).card = n - 4 := by
  rw [sharpnessAOrdinaryEdges,
    Finset.card_image_of_injective _ (fun _ _ h => Prod.mk.inj h |>.2),
    sharpnessOrdinaryCoreCard n hn]

lemma sharpnessBOrdinaryEdgesCard (n : ℕ) (hn : n ≥ 10) :
    (sharpnessBOrdinaryEdges n hn).card = n - 4 := by
  rw [sharpnessBOrdinaryEdges,
    Finset.card_image_of_injective _ (fun _ _ h => Prod.mk.inj h |>.2),
    sharpnessOrdinaryCoreCard n hn]

lemma sharpnessSzegedIndexAsOrderedSum (n : ℕ) :
    szegedIndex (sharpnessGraph n) =
      ∑ p ∈ theorem1OrderedPairs n with (sharpnessGraph n).Adj p.1 p.2,
        closerCount (sharpnessGraph n) p.1 p.2 *
          closerCount (sharpnessGraph n) p.2 p.1 := by
  classical
  unfold szegedIndex
  rw [← Finset.sum_subtype (sharpnessGraph n).edgeFinset (by intro e; simp)
    (szegedContribution (sharpnessGraph n))]
  have hedge : (sharpnessGraph n).edgeFinset =
      (Finset.univ : Finset (Sym2 (Fin n))).filter
        fun e => e ∈ (sharpnessGraph n).edgeSet := by
    ext e
    simp
  rw [hedge, Finset.sum_filter]
  have hs := sumSym2EqSumOrdered
    (n := n) (M := ℕ)
    (f := fun e => if e ∈ (sharpnessGraph n).edgeSet then
      szegedContribution (sharpnessGraph n) e else 0)
    (by intro a; simp)
  rw [hs]
  change (∑ p ∈ theorem1OrderedPairs n,
      if (sharpnessGraph n).Adj p.1 p.2 then
        closerCount (sharpnessGraph n) p.1 p.2 *
          closerCount (sharpnessGraph n) p.2 p.1 else 0) = _
  rw [← Finset.sum_filter]

lemma sharpnessOrderedEdges_eq_classes (n : ℕ) (hn : n ≥ 10) :
    (theorem1OrderedPairs n).filter
        (fun p => (sharpnessGraph n).Adj p.1 p.2) =
      sharpnessEdgeClasses n hn := by
  classical
  let a := sharpnessA n hn
  let b := sharpnessB n hn
  let x := sharpnessX n hn
  let y := sharpnessY n hn
  ext p
  simp only [Finset.mem_filter, sharpnessEdgeClasses, sharpnessSpecialEdges,
    Finset.mem_union]
  constructor
  · rintro ⟨hp, hadj⟩
    have hlt : p.1.val < p.2.val :=
      (Finset.mem_filter.mp hp).2
    rcases hadj.2 with hcore | h | h | h | h | h | h
    · by_cases hp10 : p.1.val = 0
      · by_cases hp21 : p.2.val = 1
        · right
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact Or.inl (Prod.ext (Fin.ext (by simp [a]; omega))
            (Fin.ext (by simp [b]; omega)))
        · left; left; right
          refine Finset.mem_image.mpr ⟨p.2, ?_, ?_⟩
          · simp [sharpnessOrdinaryCore]
            omega
          · exact Prod.ext (Fin.ext (by simp [a]; omega)) rfl
      · by_cases hp11 : p.1.val = 1
        · left; right
          refine Finset.mem_image.mpr ⟨p.2, ?_, ?_⟩
          · simp [sharpnessOrdinaryCore]
            omega
          · exact Prod.ext (Fin.ext (by simp [b]; omega)) rfl
        · left; left; left
          refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨?_, ?_, hadj.ne⟩, ?_⟩
          · simp [sharpnessOrdinaryCore]
            omega
          · simp [sharpnessOrdinaryCore]
            omega
          · exact (show p.1 < p.2 from hlt)
    · omega
    · right
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inl (Prod.ext (Fin.ext (by simp [a, x]; omega))
        (Fin.ext (by simp [a, x]; omega))))
    · omega
    · right
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inl (Prod.ext (Fin.ext (by simp [b, y]; omega))
        (Fin.ext (by simp [b, y]; omega)))))
    · right
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (Prod.ext (Fin.ext (by simp [x, y]; omega))
        (Fin.ext (by simp [x, y]; omega)))))
    · omega
  · rintro (((hord | ha) | hb) | hs)
    · rcases Finset.mem_filter.mp hord with ⟨hp, hlt⟩
      rcases Finset.mem_offDiag.mp hp with ⟨hp1, hp2, hpne⟩
      refine ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr
          ⟨by simp, by simp, hpne⟩, hlt⟩
      · refine ⟨hpne, Or.inl ⟨?_, ?_⟩⟩
        · have hp1v : 2 ≤ p.1.val ∧ p.1.val < n - 2 := by
            simpa [sharpnessOrdinaryCore] using hp1
          exact hp1v.2
        · have hp2v : 2 ≤ p.2.val ∧ p.2.val < n - 2 := by
            simpa [sharpnessOrdinaryCore] using hp2
          exact hp2v.2
    · rcases Finset.mem_image.mp ha with ⟨q, hq, rfl⟩
      have hqv : 2 ≤ q.val ∧ q.val < n - 2 := by
        simpa [sharpnessOrdinaryCore] using hq
      have hne : sharpnessA n hn ≠ q := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
        omega
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr
        ⟨by simp, by simp, hne⟩, ?_⟩, ?_⟩
      · change 0 < q.val
        omega
      · exact ⟨hne, Or.inl ⟨by simp; omega, hqv.2⟩⟩
    · rcases Finset.mem_image.mp hb with ⟨q, hq, rfl⟩
      have hqv : 2 ≤ q.val ∧ q.val < n - 2 := by
        simpa [sharpnessOrdinaryCore] using hq
      have hne : sharpnessB n hn ≠ q := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
        omega
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr
        ⟨by simp, by simp, hne⟩, ?_⟩, ?_⟩
      · change 1 < q.val
        omega
      · exact ⟨hne, Or.inl ⟨by simp; omega, hqv.2⟩⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl | rfl <;>
        simp [theorem1OrderedPairs, sharpnessGraph, sharpnessA, sharpnessB,
          sharpnessX, sharpnessY] <;> omega

private lemma sharpnessOrdinaryContributionSum (n : ℕ) (hn : n ≥ 10) :
    (∑ p ∈ sharpnessOrdinaryPairs n,
      closerCount (sharpnessGraph n) p.1 p.2 *
        closerCount (sharpnessGraph n) p.2 p.1) = (n - 4).choose 2 := by
  calc
    _ = ∑ _p ∈ sharpnessOrdinaryPairs n, 1 := by
      apply Finset.sum_congr rfl
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp, _⟩
      rcases Finset.mem_offDiag.mp hp with ⟨hp1, hp2, hpne⟩
      have hp1v : 2 ≤ p.1.val ∧ p.1.val < n - 2 := by
        simpa [sharpnessOrdinaryCore] using hp1
      have hp2v : 2 ≤ p.2.val ∧ p.2.val < n - 2 := by
        simpa [sharpnessOrdinaryCore] using hp2
      obtain ⟨h₁, h₂⟩ := sharpnessCloserOrdinary n hn p.1 p.2
        hp1v.1 hp1v.2 hp2v.1 hp2v.2 hpne
      rw [h₁, h₂]
    _ = (sharpnessOrdinaryPairs n).card := by simp
    _ = (n - 4).choose 2 := sharpnessOrdinaryPairsCard n hn

private lemma sharpnessAOrdinaryContributionSum (n : ℕ) (hn : n ≥ 10) :
    (∑ p ∈ sharpnessAOrdinaryEdges n hn,
      closerCount (sharpnessGraph n) p.1 p.2 *
        closerCount (sharpnessGraph n) p.2 p.1) = 2 * (n - 4) := by
  calc
    _ = ∑ _p ∈ sharpnessAOrdinaryEdges n hn, 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
      have hqv : 2 ≤ q.val ∧ q.val < n - 2 := by
        simpa [sharpnessOrdinaryCore] using hq
      obtain ⟨h₁, h₂⟩ := sharpnessCloserAOrdinary n hn q hqv.1 hqv.2
      rw [h₁, h₂]
    _ = 2 * (sharpnessAOrdinaryEdges n hn).card := by simp [mul_comm]
    _ = 2 * (n - 4) := by rw [sharpnessAOrdinaryEdgesCard n hn]

private lemma sharpnessBOrdinaryContributionSum (n : ℕ) (hn : n ≥ 10) :
    (∑ p ∈ sharpnessBOrdinaryEdges n hn,
      closerCount (sharpnessGraph n) p.1 p.2 *
        closerCount (sharpnessGraph n) p.2 p.1) = 2 * (n - 4) := by
  calc
    _ = ∑ _p ∈ sharpnessBOrdinaryEdges n hn, 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
      have hqv : 2 ≤ q.val ∧ q.val < n - 2 := by
        simpa [sharpnessOrdinaryCore] using hq
      obtain ⟨h₁, h₂⟩ := sharpnessCloserBOrdinary n hn q hqv.1 hqv.2
      rw [h₁, h₂]
    _ = 2 * (sharpnessBOrdinaryEdges n hn).card := by simp [mul_comm]
    _ = 2 * (n - 4) := by rw [sharpnessBOrdinaryEdgesCard n hn]

private lemma sharpnessSpecialContributionSum (n : ℕ) (hn : n ≥ 10) :
    (∑ p ∈ sharpnessSpecialEdges n hn,
      closerCount (sharpnessGraph n) p.1 p.2 *
        closerCount (sharpnessGraph n) p.2 p.1) = 4 + 4 * (n - 2) + 4 := by
  let a := sharpnessA n hn
  let b := sharpnessB n hn
  let x := sharpnessX n hn
  let y := sharpnessY n hn
  have hab_ax : (a, b) ≠ (a, x) := by
    intro h
    have hv := congrArg (fun p : Fin n × Fin n => p.2.val) h
    simp [a, b, x] at hv
    omega
  have hab_by : (a, b) ≠ (b, y) := by
    intro h
    have hv := congrArg (fun p : Fin n × Fin n => p.1.val) h
    simp [a, b] at hv
  have hab_xy : (a, b) ≠ (x, y) := by
    intro h
    have hv := congrArg (fun p : Fin n × Fin n => p.1.val) h
    simp [a, x] at hv
    omega
  have hax_by : (a, x) ≠ (b, y) := by
    intro h
    have hv := congrArg (fun p : Fin n × Fin n => p.1.val) h
    simp [a, b] at hv
  have hax_xy : (a, x) ≠ (x, y) := by
    intro h
    have hv := congrArg (fun p : Fin n × Fin n => p.1.val) h
    simp [a, x] at hv
    omega
  have hby_xy : (b, y) ≠ (x, y) := by
    intro h
    have hv := congrArg (fun p : Fin n × Fin n => p.1.val) h
    simp [b, x] at hv
    omega
  have hab := sharpnessCloserAB n hn
  have hax := sharpnessCloserAX n hn
  have hby := sharpnessCloserBY n hn
  have hxy := sharpnessCloserXY n hn
  unfold sharpnessSpecialEdges
  change (∑ p ∈ ({(a, b), (a, x), (b, y), (x, y)} : Finset (Fin n × Fin n)),
      closerCount (sharpnessGraph n) p.1 p.2 *
        closerCount (sharpnessGraph n) p.2 p.1) = _
  rw [Finset.sum_insert (by simp [hab_ax, hab_by, hab_xy]),
    Finset.sum_insert (by simp [hax_by, hax_xy]),
    Finset.sum_insert (by simp [hby_xy]), Finset.sum_singleton]
  change
    closerCount (sharpnessGraph n) a b * closerCount (sharpnessGraph n) b a +
      (closerCount (sharpnessGraph n) a x * closerCount (sharpnessGraph n) x a +
      (closerCount (sharpnessGraph n) b y * closerCount (sharpnessGraph n) y b +
      closerCount (sharpnessGraph n) x y * closerCount (sharpnessGraph n) y x)) = _
  rw [hab.1, hab.2, hax.1, hax.2, hby.1, hby.2, hxy.1, hxy.2]
  omega

private lemma sharpnessDisjointOrdinaryA (n : ℕ) (hn : n ≥ 10) :
    Disjoint (sharpnessOrdinaryPairs n) (sharpnessAOrdinaryEdges n hn) := by
  rw [Finset.disjoint_left]
  intro p hp ha
  rcases Finset.mem_filter.mp hp with ⟨hp, _⟩
  rcases Finset.mem_offDiag.mp hp with ⟨hp1, _, _⟩
  have hp1v : 2 ≤ p.1.val := by
    have h : 2 ≤ p.1.val ∧ p.1.val < n - 2 := by
      simpa [sharpnessOrdinaryCore] using hp1
    exact h.1
  rcases Finset.mem_image.mp ha with ⟨q, _, rfl⟩
  simp at hp1v

private lemma sharpnessDisjointOrdinaryB (n : ℕ) (hn : n ≥ 10) :
    Disjoint (sharpnessOrdinaryPairs n) (sharpnessBOrdinaryEdges n hn) := by
  rw [Finset.disjoint_left]
  intro p hp hb
  rcases Finset.mem_filter.mp hp with ⟨hp, _⟩
  rcases Finset.mem_offDiag.mp hp with ⟨hp1, _, _⟩
  have hp1v : 2 ≤ p.1.val := by
    have h : 2 ≤ p.1.val ∧ p.1.val < n - 2 := by
      simpa [sharpnessOrdinaryCore] using hp1
    exact h.1
  rcases Finset.mem_image.mp hb with ⟨q, _, rfl⟩
  simp at hp1v

private lemma sharpnessDisjointAB (n : ℕ) (hn : n ≥ 10) :
    Disjoint (sharpnessAOrdinaryEdges n hn) (sharpnessBOrdinaryEdges n hn) := by
  rw [Finset.disjoint_left]
  intro p ha hb
  rcases Finset.mem_image.mp ha with ⟨q, _, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨r, _, h⟩
  have hv := congrArg (fun p : Fin n × Fin n => p.1.val) h
  simp at hv

private lemma sharpnessDisjointOrdinarySpecial (n : ℕ) (hn : n ≥ 10) :
    Disjoint (sharpnessOrdinaryPairs n) (sharpnessSpecialEdges n hn) := by
  rw [Finset.disjoint_left]
  intro p hp hs
  rcases Finset.mem_filter.mp hp with ⟨hp, _⟩
  rcases Finset.mem_offDiag.mp hp with ⟨hp1, hp2, _⟩
  have hp1v : 2 ≤ p.1.val ∧ p.1.val < n - 2 := by
    simpa [sharpnessOrdinaryCore] using hp1
  have hp2v : 2 ≤ p.2.val ∧ p.2.val < n - 2 := by
    simpa [sharpnessOrdinaryCore] using hp2
  simp only [sharpnessSpecialEdges, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl <;>
    simp at hp1v hp2v <;> omega

private lemma sharpnessDisjointASpecial (n : ℕ) (hn : n ≥ 10) :
    Disjoint (sharpnessAOrdinaryEdges n hn) (sharpnessSpecialEdges n hn) := by
  rw [Finset.disjoint_left]
  intro p ha hs
  rcases Finset.mem_image.mp ha with ⟨q, hq, rfl⟩
  have hqv : 2 ≤ q.val ∧ q.val < n - 2 := by
    simpa [sharpnessOrdinaryCore] using hq
  simp [sharpnessSpecialEdges, sharpnessA, sharpnessB, sharpnessX,
    sharpnessY] at hs
  rcases hs with h | h
  · have hv := congrArg Fin.val h
    simp at hv
    omega
  · rcases h with h | ⟨h, _⟩
    · have hv := congrArg Fin.val h
      simp at hv
      omega
    · omega

private lemma sharpnessDisjointBSpecial (n : ℕ) (hn : n ≥ 10) :
    Disjoint (sharpnessBOrdinaryEdges n hn) (sharpnessSpecialEdges n hn) := by
  rw [Finset.disjoint_left]
  intro p hb hs
  rcases Finset.mem_image.mp hb with ⟨q, hq, rfl⟩
  have hqv : 2 ≤ q.val ∧ q.val < n - 2 := by
    simpa [sharpnessOrdinaryCore] using hq
  simp [sharpnessSpecialEdges, sharpnessA, sharpnessB, sharpnessX,
    sharpnessY] at hs
  rcases hs with h | ⟨h, _⟩
  · have hv := congrArg Fin.val h
    simp at hv
    omega
  · omega

private lemma sharpnessSzegedIndexNat (n : ℕ) (hn : n ≥ 10) :
    szegedIndex (sharpnessGraph n) =
      (n - 4).choose 2 + 2 * (n - 4) + 2 * (n - 4) +
        (4 + 4 * (n - 2) + 4) := by
  rw [sharpnessSzegedIndexAsOrderedSum,
    sharpnessOrderedEdges_eq_classes n hn]
  unfold sharpnessEdgeClasses
  have hOA := sharpnessDisjointOrdinaryA n hn
  have hOB := sharpnessDisjointOrdinaryB n hn
  have hAB := sharpnessDisjointAB n hn
  have hOS := sharpnessDisjointOrdinarySpecial n hn
  have hAS := sharpnessDisjointASpecial n hn
  have hBS := sharpnessDisjointBSpecial n hn
  have hOAB : Disjoint
      (sharpnessOrdinaryPairs n ∪ sharpnessAOrdinaryEdges n hn)
      (sharpnessBOrdinaryEdges n hn) := by
    rw [Finset.disjoint_left]
    intro p hp hb
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.disjoint_left.mp hOB) hp hb
    · exact (Finset.disjoint_left.mp hAB) hp hb
  have hAllS : Disjoint
      (sharpnessOrdinaryPairs n ∪ sharpnessAOrdinaryEdges n hn ∪
        sharpnessBOrdinaryEdges n hn)
      (sharpnessSpecialEdges n hn) := by
    rw [Finset.disjoint_left]
    intro p hp hs
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact (Finset.disjoint_left.mp hOS) hp hs
      · exact (Finset.disjoint_left.mp hAS) hp hs
    · exact (Finset.disjoint_left.mp hBS) hp hs
  rw [Finset.sum_union hAllS, Finset.sum_union hOAB,
    Finset.sum_union hOA, sharpnessOrdinaryContributionSum n hn,
    sharpnessAOrdinaryContributionSum n hn,
    sharpnessBOrdinaryContributionSum n hn,
    sharpnessSpecialContributionSum n hn]

/-- The edge-class computation of the Szeged index of `G_n`. -/
theorem lemma7SzegedIndex (n : ℕ) (h_order : n ≥ 10) :
    (szegedIndex (sharpnessGraph n) : ℤ) =
      ((n : ℤ) ^ 2 + 7 * n - 12) / 2 := by
  /-
  Split the edge sum into the five classes in the manuscript: edges inside
  `A`, edges from `a` or `b` to `A`, `ab`, the two attachment edges, and
  `xy`.  Their contributions are

    `(n-4).choose 2`, `4(n-4)`, `4`, `4(n-2)`, and `4`.
  -/
  rw [sharpnessSzegedIndexNat n h_order]
  let S : ℕ := (n - 4).choose 2 + 2 * (n - 4) + 2 * (n - 4) +
    (4 + 4 * (n - 2) + 4)
  change (S : ℤ) = ((n : ℤ) ^ 2 + 7 * n - 12) / 2
  have hchooseNat : 2 * (n - 4).choose 2 = (n - 4) * (n - 5) := by
    have hbase : 2 * (n - 4).choose 2 = (n - 4) * (n - 4 - 1) := by
      rw [Nat.choose_two_right]
      apply Nat.mul_div_cancel'
      rcases Nat.even_mul_pred_self (n - 4) with ⟨k, hk⟩
      exact ⟨k, by omega⟩
    have hpred : n - 4 - 1 = n - 5 := by omega
    rwa [hpred] at hbase
  have hchooseInt : 2 * ((n - 4).choose 2 : ℤ) =
      ((n : ℤ) - 4) * ((n : ℤ) - 5) := by
    have hi := congrArg (fun z : ℕ => (z : ℤ)) hchooseNat
    push_cast at hi
    rw [Nat.cast_sub (by omega : 4 ≤ n),
      Nat.cast_sub (by omega : 5 ≤ n)] at hi
    exact hi
  have hpoly : (n : ℤ) ^ 2 + 7 * n - 12 = 2 * (S : ℤ) := by
    dsimp [S]
    push_cast
    rw [Nat.cast_sub (by omega : 4 ≤ n),
      Nat.cast_sub (by omega : 2 ≤ n)]
    calc
      (n : ℤ) ^ 2 + 7 * n - 12 =
          ((n : ℤ) - 4) * ((n : ℤ) - 5) +
            8 * ((n : ℤ) - 4) + 8 * ((n : ℤ) - 2) + 16 := by ring
      _ = 2 * ((n - 4).choose 2 : ℤ) +
            8 * ((n : ℤ) - 4) + 8 * ((n : ℤ) - 2) + 16 := by
          rw [hchooseInt]
      _ = 2 * (((n - 4).choose 2 : ℤ) +
            2 * ((n : ℤ) - 4) + 2 * ((n : ℤ) - 4) +
            (4 + 4 * ((n : ℤ) - 2) + 4)) := by ring
  symm
  apply (Int.ediv_eq_iff_eq_mul_left (by norm_num : (2 : ℤ) ≠ 0)
    ⟨(S : ℤ), by rw [hpoly]⟩).2
  rw [hpoly]
  ring

/-- The complete existence proof for the sharpness result. -/
theorem lemma7Proof3 (n : ℕ) (h_order : n ≥ 10) :
    ∃ G : SimpleGraph (Fin n),
      IsUnexceptional G ∧ IsTwoConnected G ∧
        szegedWienerGap G = (2 * n : ℤ) := by
  refine ⟨sharpnessGraph n, (lemma7Proof1 n h_order).2,
    (lemma7Proof1 n h_order).1, ?_⟩
  unfold szegedWienerGap
  rw [lemma7SzegedIndex n h_order, lemma7Proof2 n h_order]
  omega

end

end BKLPS
