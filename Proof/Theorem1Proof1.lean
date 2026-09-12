import Proof.Definitions
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring.RingNF

/-! First half of the proof of Theorem 1: compute the gap of `K_n^t`. -/

namespace BKLPS

noncomputable section

open SimpleGraph
open scoped BigOperators

/-- The set `A = N(z)` in the proof of Theorem 1.  Vertex `0` is `z`. -/
def theorem1A (n t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun x => x.val ≠ 0 ∧ x.val ≤ t

/-- The set `B = V(G) \ N[z]` in the proof of Theorem 1. -/
def theorem1B (n t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun x => t < x.val

/-- Rewrite a symmetric sum whose diagonal vanishes as a sum over the
strictly ordered pairs. -/
lemma sumSym2EqSumOrdered {n : ℕ} {M : Type} [AddCommMonoid M]
    (f : Sym2 (Fin n) → M) (hdiag : ∀ a, f s(a, a) = 0) :
    ∑ p : Sym2 (Fin n), f p =
      ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag with p.1 < p.2,
        f s(p.1, p.2) := by
  have hz : ∑ p ∈ (Finset.univ : Finset (Sym2 (Fin n))) with p.IsDiag, f p = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    obtain ⟨a, rfl⟩ := p.mem_diagSet_iff_isDiag.mpr (Finset.mem_filter.mp hp).2
    exact hdiag a
  rw [← Finset.sym2_univ]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Fin n)).sym2) (p := fun p => p.IsDiag)]
  simp only [Finset.sym2_univ]
  rw [hz, zero_add]
  exact Finset.sum_sym2_filter_not_isDiag _ _

/-- The canonical finset containing each unordered pair exactly once. -/
def theorem1OrderedPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ.offDiag).filter fun p => p.1 < p.2

lemma theorem1OrderedPairsCard (n : ℕ) :
    (theorem1OrderedPairs n).card = n.choose 2 := by
  have h := sumSym2EqSumOrdered
    (n := n) (M := ℕ) (f := fun p => if p.IsDiag then 0 else 1) (by simp)
  simp only [Sym2.mk_isDiag_iff] at h
  have hl : (∑ p : Sym2 (Fin n), if p.IsDiag then 0 else 1) =
      Fintype.card {p : Sym2 (Fin n) // ¬ p.IsDiag} := by
    rw [Fintype.card_of_subtype]
    · simpa only [Set.mem_setOf_eq, ite_not] using
        (Finset.sum_boole (R := ℕ) (fun p : Sym2 (Fin n) => ¬p.IsDiag) Finset.univ)
    · intro x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hr : (∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag with p.1 < p.2,
      if p.1 = p.2 then 0 else 1) = (theorem1OrderedPairs n).card := by
    change (∑ p ∈ theorem1OrderedPairs n, if p.1 = p.2 then 0 else 1) = _
    calc
      _ = ∑ p ∈ theorem1OrderedPairs n, 1 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpne := (Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1).2.2
        simp [hpne]
      _ = (theorem1OrderedPairs n).card := by simp
  rw [hl, hr, Sym2.card_subtype_not_diag] at h
  simpa using h.symm

/-- The ordered pairs consisting of `0` and a vertex in `B`. -/
def theorem1SpecialPairs (n t : ℕ) : Finset (Fin n × Fin n) :=
  (theorem1OrderedPairs n).filter fun p => p.1.val = 0 ∧ t < p.2.val

/-- Ordered old-clique pairs crossing from `A` to `B`. -/
def theorem1CrossPairs (n t : ℕ) : Finset (Fin n × Fin n) :=
  (theorem1OrderedPairs n).filter fun p =>
    p.1.val ≠ 0 ∧ p.1.val ≤ t ∧ t < p.2.val

/-- The `t` ordered attachment edges from `0` to `A`. -/
def theorem1AttachmentPairs (n t : ℕ) : Finset (Fin n × Fin n) :=
  (theorem1OrderedPairs n).filter fun p =>
    p.1.val = 0 ∧ p.2.val ≤ t

/-- The ordered pairs which are edges of `K_n^t`. -/
def theorem1OrderedEdges (n t : ℕ) : Finset (Fin n × Fin n) :=
  (theorem1OrderedPairs n).filter fun p => (Knt n t).Adj p.1 p.2

lemma theorem1BCard (n t : ℕ) (h_lower : t ≥ 1) (h_upper : t ≤ n - 1) :
    (theorem1B n t).card = n - t - 1 := by
  have htn : t < n := by omega
  let ft : Fin n := ⟨t, htn⟩
  have hB : theorem1B n t = Finset.Ioi ft := by
    ext x
    simp only [theorem1B, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ioi]
    rfl
  rw [hB, Fin.card_Ioi]
  simp [ft, Nat.sub_sub, Nat.add_comm]

lemma theorem1ACard (n t : ℕ) (h_lower : t ≥ 1) (h_upper : t ≤ n - 1) :
    (theorem1A n t).card = t := by
  have hn : 1 < n := by omega
  have htn : t < n := by omega
  let one : Fin n := ⟨1, hn⟩
  let ft : Fin n := ⟨t, htn⟩
  have hA : theorem1A n t = Finset.Icc one ft := by
    ext x
    simp only [theorem1A, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Icc]
    change (x.val ≠ 0 ∧ x.val ≤ t) ↔ (1 ≤ x.val ∧ x.val ≤ t)
    omega
  rw [hA, Fin.card_Icc]
  simp [one, ft]

lemma theorem1SpecialPairsCard (n t : ℕ)
    (h_lower : t ≥ 1) (h_upper : t ≤ n - 1) :
    (theorem1SpecialPairs n t).card = n - t - 1 := by
  have himage : (theorem1SpecialPairs n t).image Prod.snd = theorem1B n t := by
    ext b
    constructor
    · intro hb
      rcases Finset.mem_image.mp hb with ⟨p, hp, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2.2⟩
    · intro hb
      have htb := (Finset.mem_filter.mp hb).2
      have hn : 0 < n := by omega
      let z : Fin n := ⟨0, hn⟩
      apply Finset.mem_image.mpr
      refine ⟨(z, b), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, by simp [z, htb]⟩
      apply Finset.mem_filter.mpr
      constructor
      · simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
        intro hzb
        have hzv := congrArg Fin.val hzb
        simp [z] at hzv
        omega
      · change (0 : ℕ) < b.val
        omega
  have hinj : Set.InjOn Prod.snd
      (↑(theorem1SpecialPairs n t) : Set (Fin n × Fin n)) := by
    intro p hp q hq hpq
    have hp' : p ∈ theorem1SpecialPairs n t := hp
    have hq' : q ∈ theorem1SpecialPairs n t := hq
    apply Prod.ext
    · have hp0 := (Finset.mem_filter.mp hp').2.1
      have hq0 := (Finset.mem_filter.mp hq').2.1
      apply Fin.ext
      omega
    · exact hpq
  calc
    (theorem1SpecialPairs n t).card =
        ((theorem1SpecialPairs n t).image Prod.snd).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = (theorem1B n t).card := congrArg Finset.card himage
    _ = n - t - 1 := theorem1BCard n t h_lower h_upper

lemma theorem1CrossPairsCard (n t : ℕ)
    (h_lower : t ≥ 1) (h_upper : t ≤ n - 1) :
    (theorem1CrossPairs n t).card = t * (n - t - 1) := by
  have heq : theorem1CrossPairs n t = theorem1A n t ×ˢ theorem1B n t := by
    ext p
    simp only [theorem1CrossPairs, theorem1OrderedPairs, theorem1A, theorem1B,
      Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
      Finset.mem_product]
    constructor
    · intro h
      exact ⟨⟨h.2.1, h.2.2.1⟩, h.2.2.2⟩
    · intro h
      have hpne : p.1 ≠ p.2 := by
        intro hp
        have hv := congrArg Fin.val hp
        omega
      have hplt : p.1 < p.2 := by
        change p.1.val < p.2.val
        omega
      exact ⟨⟨hpne, hplt⟩, h.1.1, h.1.2, h.2⟩
  rw [heq, Finset.card_product, theorem1ACard n t h_lower h_upper,
    theorem1BCard n t h_lower h_upper]

lemma theorem1AttachmentPairsCard (n t : ℕ)
    (h_lower : t ≥ 1) (h_upper : t ≤ n - 1) :
    (theorem1AttachmentPairs n t).card = t := by
  have hn : 0 < n := by omega
  let z : Fin n := ⟨0, hn⟩
  have heq : theorem1AttachmentPairs n t = {z} ×ˢ theorem1A n t := by
    ext p
    simp only [theorem1AttachmentPairs, theorem1OrderedPairs, theorem1A,
      Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
      Finset.mem_product, Finset.mem_singleton]
    constructor
    · intro h
      have hpz : p.1 = z := by
        apply Fin.ext
        simpa [z] using h.2.1
      have hp20 : p.2.val ≠ 0 := by
        have hplt : p.1.val < p.2.val := h.1.2
        omega
      exact ⟨hpz, hp20, h.2.2⟩
    · intro h
      have hp0 : p.1.val = 0 := by
        simpa [z] using congrArg Fin.val h.1
      have hpne : p.1 ≠ p.2 := by
        intro hp
        apply h.2.1
        rw [← congrArg Fin.val hp]
        exact hp0
      have hplt : p.1 < p.2 := by
        change p.1.val < p.2.val
        omega
      exact ⟨⟨hpne, hplt⟩, hp0, h.2.2⟩
  rw [heq, Finset.card_product, theorem1ACard n t h_lower h_upper]
  simp

lemma theorem1OrderedEdgesEqSdiff (n t : ℕ) :
    theorem1OrderedEdges n t =
      theorem1OrderedPairs n \ theorem1SpecialPairs n t := by
  ext p
  simp only [theorem1OrderedEdges, theorem1SpecialPairs, Finset.mem_filter,
    Finset.mem_sdiff]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro hs
    have hpne : p.1 ≠ p.2 :=
      (Finset.mem_offDiag.mp (Finset.mem_filter.mp h.1).1).2.2
    rcases h.2 with ⟨_, hold | hzleft | hzright⟩
    · exact hold.1 hs.2.1
    · omega
    · apply hpne
      apply Fin.ext
      omega
  · intro h
    refine ⟨h.1, ?_⟩
    have hpne : p.1 ≠ p.2 :=
      (Finset.mem_offDiag.mp (Finset.mem_filter.mp h.1).1).2.2
    have hlt : p.1.val < p.2.val := (Finset.mem_filter.mp h.1).2
    refine ⟨hpne, ?_⟩
    by_cases hp0 : p.1.val = 0
    · have hnot := h.2
      simp only [h.1, true_and, not_and] at hnot
      exact Or.inr (Or.inl ⟨hp0, by omega⟩)
    · exact Or.inl ⟨hp0, by omega⟩

lemma theorem1OrderedEdgesCard (n t : ℕ)
    (h_lower : t ≥ 1) (h_upper : t ≤ n - 1) :
    (theorem1OrderedEdges n t).card = n.choose 2 - (n - t - 1) := by
  have hs : theorem1SpecialPairs n t ⊆ theorem1OrderedPairs n := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  rw [theorem1OrderedEdgesEqSdiff, Finset.card_sdiff_of_subset hs,
    theorem1OrderedPairsCard,
    theorem1SpecialPairsCard n t h_lower h_upper]

lemma theorem1AttachmentFilter (n t : ℕ) :
    (theorem1OrderedEdges n t).filter
        (fun p => p.1.val = 0 ∧ p.2.val ≤ t) = theorem1AttachmentPairs n t := by
  ext p
  simp only [theorem1OrderedEdges, theorem1AttachmentPairs, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨h.1.1, h.2⟩
  · intro h
    refine ⟨⟨h.1, ?_⟩, h.2⟩
    have hpne : p.1 ≠ p.2 :=
      (Finset.mem_offDiag.mp (Finset.mem_filter.mp h.1).1).2.2
    exact ⟨hpne, Or.inr (Or.inl h.2)⟩

lemma theorem1CrossFilter (n t : ℕ) :
    (theorem1OrderedEdges n t).filter
        (fun p => p.1.val ≠ 0 ∧ p.1.val ≤ t ∧ t < p.2.val) =
      theorem1CrossPairs n t := by
  ext p
  simp only [theorem1OrderedEdges, theorem1CrossPairs, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨h.1.1, h.2⟩
  · intro h
    refine ⟨⟨h.1, ?_⟩, h.2⟩
    have hpne : p.1 ≠ p.2 :=
      (Finset.mem_offDiag.mp (Finset.mem_filter.mp h.1).1).2.2
    exact ⟨hpne, Or.inl ⟨h.2.1, by omega⟩⟩

lemma theorem1KntWalkLeTwo (n t : ℕ)
    (h_lower : t ≥ 1) (h_upper : t ≤ n - 1) (a b : Fin n) :
    ∃ p : (Knt n t).Walk a b, p.length ≤ 2 := by
  have hn : 1 < n := by omega
  let x : Fin n := ⟨1, hn⟩
  by_cases hab : a = b
  · subst b
    exact ⟨Walk.nil, by simp⟩
  by_cases hadj : (Knt n t).Adj a b
  · exact ⟨hadj.toWalk, by simp⟩
  · have ha0_or_hb0 : a.val = 0 ∨ b.val = 0 := by
      simp only [Knt] at hadj
      omega
    have haxne : a ≠ x := by
      intro hax
      apply hadj
      rcases ha0_or_hb0 with ha0 | hb0
      · subst a
        simp [x] at ha0
      · subst a
        have hxne : (⟨1, hn⟩ : Fin n) ≠ b := by simpa [x] using hab
        simp [Knt, x, hb0, h_lower, hxne]
    have hxbne : x ≠ b := by
      intro hxb
      apply hadj
      rcases ha0_or_hb0 with ha0 | hb0
      · subst b
        have hxne : a ≠ (⟨1, hn⟩ : Fin n) := by simpa [x] using hab
        simp [Knt, x, ha0, h_lower, hxne]
      · subst b
        simp [x] at hb0
    have hax : (Knt n t).Adj a x := by
      have haxne' : a ≠ (⟨1, hn⟩ : Fin n) := by simpa [x] using haxne
      rcases ha0_or_hb0 with ha0 | hb0
      · simp [Knt, x, ha0, h_lower, haxne']
      · have ha0 : a.val ≠ 0 := by
          intro h
          apply hab
          apply Fin.ext
          omega
        simp [Knt, x, ha0, haxne']
    have hxb : (Knt n t).Adj x b := by
      have hxbne' : (⟨1, hn⟩ : Fin n) ≠ b := by simpa [x] using hxbne
      rcases ha0_or_hb0 with ha0 | hb0
      · have hb0 : b.val ≠ 0 := by
          intro h
          apply hab
          apply Fin.ext
          omega
        simp [Knt, x, hb0, hxbne']
      · simp [Knt, x, hb0, h_lower, hxbne']
    exact ⟨hax.toWalk.append hxb.toWalk, by simp⟩

lemma theorem1KntDist (n t : ℕ)
    (h_lower : t ≥ 1) (h_upper : t ≤ n - 1) (a b : Fin n) :
    (Knt n t).dist a b =
      if a = b then 0 else if (Knt n t).Adj a b then 1 else 2 := by
  by_cases hab : a = b
  · simp [hab]
  by_cases hadj : (Knt n t).Adj a b
  · simp [hab, hadj]
  · simp only [hab, hadj, ↓reduceIte]
    obtain ⟨p, hp⟩ := theorem1KntWalkLeTwo n t h_lower h_upper a b
    apply Nat.le_antisymm ((SimpleGraph.dist_le p).trans hp)
    exact (show (Knt n t).Reachable a b from ⟨p⟩).one_lt_dist_of_ne_of_not_adj hab hadj

lemma theorem1KntDistOfLt (n t : ℕ)
    (h_lower : t ≥ 1) (h_upper : t ≤ n - 1)
    (a b : Fin n) (hab : a < b) :
    (Knt n t).dist a b = if a.val = 0 ∧ t < b.val then 2 else 1 := by
  rw [theorem1KntDist n t h_lower h_upper]
  have hne : a ≠ b := ne_of_lt hab
  simp only [hne, ↓reduceIte]
  by_cases h : a.val = 0 ∧ t < b.val
  · have hn : ¬(Knt n t).Adj a b := by
      rintro ⟨_, habold | hzleft | hzright⟩
      · exact habold.1 h.1
      · omega
      · apply hne
        apply Fin.ext
        omega
    simp [h, hn]
  · have hadj : (Knt n t).Adj a b := by
      refine ⟨hne, ?_⟩
      by_cases ha : a.val = 0
      · exact Or.inr (Or.inl ⟨ha, by omega⟩)
      · exact Or.inl ⟨ha, by omega⟩
    simp [h, hadj]

lemma theorem1WienerIndex (n t : ℕ)
    (h_lower : t ≥ 1) (h_upper : t ≤ n - 1) :
    wienerIndex (Knt n t) = n.choose 2 + (n - t - 1) := by
  unfold wienerIndex
  rw [sumSym2EqSumOrdered]
  · change (∑ p ∈ theorem1OrderedPairs n, (Knt n t).dist p.1 p.2) = _
    calc
      _ = ∑ p ∈ theorem1OrderedPairs n,
          (1 + if p.1.val = 0 ∧ t < p.2.val then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hlt := (Finset.mem_filter.mp hp).2
        rw [theorem1KntDistOfLt n t h_lower h_upper p.1 p.2 hlt]
        split <;> simp_all
      _ = (theorem1OrderedPairs n).card + (theorem1SpecialPairs n t).card := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 1
        simp [theorem1SpecialPairs]
      _ = n.choose 2 + (n - t - 1) := by
        rw [theorem1OrderedPairsCard, theorem1SpecialPairsCard n t h_lower h_upper]
  · intro a
    exact SimpleGraph.dist_self

lemma theorem1OldCloserCount (n t : ℕ)
    (h_lower : t ≥ 1) (h_upper : t ≤ n - 1)
    (a b : Fin n) (ha : a.val ≠ 0) (hb : b.val ≠ 0) (hab : a ≠ b) :
    closerCount (Knt n t) a b =
      if a.val ≤ t ∧ t < b.val then 2 else 1 := by
  have hn : 0 < n := by omega
  let z : Fin n := ⟨0, hn⟩
  have hza : z ≠ a := by
    intro h
    apply ha
    simpa [z] using congrArg Fin.val h.symm
  have haz : a ≠ z := hza.symm
  have hzb : z ≠ b := by
    intro h
    apply hb
    simpa [z] using congrArg Fin.val h.symm
  have hset : closerVertices (Knt n t) a b =
      insert a (if a.val ≤ t ∧ t < b.val then {z} else ∅) := by
    ext x
    simp only [closerVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    by_cases hxa : x = a
    · subst x
      have hadj : (Knt n t).Adj a b := ⟨hab, Or.inl ⟨ha, hb⟩⟩
      rw [SimpleGraph.dist_self, theorem1KntDist n t h_lower h_upper]
      by_cases hcross : a.val ≤ t ∧ t < b.val <;>
        simp [hcross, hab, hadj, hza.symm]
    by_cases hxb : x = b
    · subst x
      rw [SimpleGraph.dist_self, theorem1KntDist n t h_lower h_upper]
      by_cases hcross : a.val ≤ t ∧ t < b.val <;>
        simp [hcross, hab, hxa, hzb.symm]
    by_cases hx0 : x.val = 0
    · have hxz : x = z := by apply Fin.ext; simpa [z]
      subst x
      rw [theorem1KntDist n t h_lower h_upper,
        theorem1KntDist n t h_lower h_upper]
      have hza_adj : (Knt n t).Adj z a ↔ a.val ≤ t := by
        simp [Knt, z, hza, ha]
      have hzb_adj : (Knt n t).Adj z b ↔ b.val ≤ t := by
        simp [Knt, z, hzb, hb]
      simp only [hza, hzb, hza_adj, hzb_adj, ↓reduceIte]
      by_cases hat : a.val ≤ t <;> by_cases hbt : b.val ≤ t <;>
        by_cases htb : t < b.val <;> simp [hat, hbt, htb] <;> omega
    · have hxadja : (Knt n t).Adj x a := by
        refine ⟨hxa, Or.inl ⟨hx0, ha⟩⟩
      have hxnadjb : (Knt n t).Adj x b := by
        refine ⟨hxb, Or.inl ⟨hx0, hb⟩⟩
      have hxz : x ≠ z := by
        intro hxz
        apply hx0
        simpa [z] using congrArg Fin.val hxz
      rw [theorem1KntDist n t h_lower h_upper,
        theorem1KntDist n t h_lower h_upper]
      by_cases hcross : a.val ≤ t ∧ t < b.val <;>
        simp [hcross, hxa, hxb, hxadja, hxnadjb, hxz]
  unfold closerCount
  rw [hset]
  split
  · rw [Finset.card_insert_of_notMem]
    · simp
    · simpa using hza.symm
  · simp

lemma theorem1AttachmentCloserCounts (n t : ℕ)
    (h_lower : t ≥ 1) (h_upper : t ≤ n - 1)
    (a : Fin n) (ha0 : a.val ≠ 0) (hat : a.val ≤ t) :
    let z : Fin n := ⟨0, by omega⟩
    closerCount (Knt n t) z a = 1 ∧
      closerCount (Knt n t) a z = n - t := by
  have hn : 0 < n := by omega
  let z : Fin n := ⟨0, hn⟩
  have hza : z ≠ a := by
    intro h
    apply ha0
    simpa [z] using congrArg Fin.val h.symm
  have haz : a ≠ z := hza.symm
  have hzad : (Knt n t).Adj z a := by
    simp [Knt, z, hza, ha0, hat]
  have hfirst : closerVertices (Knt n t) z a = {z} := by
    ext x
    simp only [closerVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    by_cases hxz : x = z
    · subst x
      rw [SimpleGraph.dist_self, theorem1KntDist n t h_lower h_upper]
      simp [hza, hzad]
    by_cases hxa : x = a
    · subst x
      rw [SimpleGraph.dist_self, theorem1KntDist n t h_lower h_upper]
      simp [haz, hzad.symm]
    have hx0 : x.val ≠ 0 := by
      intro hx0
      apply hxz
      apply Fin.ext
      simpa [z]
    have hxadja : (Knt n t).Adj x a := ⟨hxa, Or.inl ⟨hx0, ha0⟩⟩
    rw [theorem1KntDist n t h_lower h_upper,
      theorem1KntDist n t h_lower h_upper]
    have hxz_adj : (Knt n t).Adj x z ↔ x.val ≤ t := by
      simp [Knt, z, hxz, hx0]
    simp only [hxz, hxa, hxadja, hxz_adj, ↓reduceIte]
    by_cases hxt : x.val ≤ t <;> simp [hxt]
  have hsecond : closerVertices (Knt n t) a z = insert a (theorem1B n t) := by
    ext x
    simp only [closerVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, theorem1B]
    by_cases hxa : x = a
    · subst x
      rw [SimpleGraph.dist_self, theorem1KntDist n t h_lower h_upper]
      simp [haz, hzad.symm]
    by_cases hxz : x = z
    · subst x
      rw [SimpleGraph.dist_self, theorem1KntDist n t h_lower h_upper]
      simp [z, hza, hzad]
    have hx0 : x.val ≠ 0 := by
      intro hx0
      apply hxz
      apply Fin.ext
      simpa [z]
    have hxadja : (Knt n t).Adj x a := ⟨hxa, Or.inl ⟨hx0, ha0⟩⟩
    have hxz_adj : (Knt n t).Adj x z ↔ x.val ≤ t := by
      simp [Knt, z, hxz, hx0]
    rw [theorem1KntDist n t h_lower h_upper,
      theorem1KntDist n t h_lower h_upper]
    simp only [hxa, hxz, hxadja, hxz_adj, ↓reduceIte]
    by_cases hxt : x.val ≤ t <;> by_cases htx : t < x.val <;>
      simp [hxt, htx] <;> omega
  dsimp
  constructor
  · unfold closerCount
    rw [hfirst]
    simp
  · unfold closerCount
    rw [hsecond, Finset.card_insert_of_notMem]
    · rw [theorem1BCard n t h_lower h_upper]
      omega
    · simp [theorem1B, ha0, hat]

lemma theorem1SzegedIndexAsOrderedSum (n t : ℕ) :
    szegedIndex (Knt n t) =
      ∑ p ∈ theorem1OrderedPairs n with (Knt n t).Adj p.1 p.2,
        closerCount (Knt n t) p.1 p.2 * closerCount (Knt n t) p.2 p.1 := by
  classical
  unfold szegedIndex
  rw [← Finset.sum_subtype (Knt n t).edgeFinset (by intro e; simp)
    (szegedContribution (Knt n t))]
  have hedge : (Knt n t).edgeFinset =
      (Finset.univ : Finset (Sym2 (Fin n))).filter fun e => e ∈ (Knt n t).edgeSet := by
    ext e
    simp
  rw [hedge, Finset.sum_filter]
  have hs := sumSym2EqSumOrdered
    (n := n) (M := ℕ)
    (f := fun e => if e ∈ (Knt n t).edgeSet then szegedContribution (Knt n t) e else 0)
    (by intro a; simp)
  rw [hs]
  change (∑ p ∈ theorem1OrderedPairs n,
      if (Knt n t).Adj p.1 p.2 then
        closerCount (Knt n t) p.1 p.2 * closerCount (Knt n t) p.2 p.1 else 0) = _
  rw [← Finset.sum_filter]

lemma theorem1EdgeContribution (n t : ℕ)
    (h_lower : t ≥ 1) (h_upper : t ≤ n - 1)
    (p : Fin n × Fin n) (hp : p ∈ theorem1OrderedPairs n)
    (hedge : (Knt n t).Adj p.1 p.2) :
    closerCount (Knt n t) p.1 p.2 * closerCount (Knt n t) p.2 p.1 =
      1 + (if p.1.val = 0 ∧ p.2.val ≤ t then n - t - 1 else 0) +
        (if p.1.val ≠ 0 ∧ p.1.val ≤ t ∧ t < p.2.val then 1 else 0) := by
  have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  have hpne : p.1 ≠ p.2 := ne_of_lt hlt
  by_cases hp0 : p.1.val = 0
  · have hp20 : p.2.val ≠ 0 := by omega
    have hp2t : p.2.val ≤ t := by
      rcases hedge.2 with hold | hzleft | hzright
      · exact False.elim (hold.1 hp0)
      · exact hzleft.2
      · apply False.elim
        apply hpne
        apply Fin.ext
        omega
    have hc := theorem1AttachmentCloserCounts n t h_lower h_upper p.2 hp20 hp2t
    have hn : 0 < n := by omega
    let z : Fin n := ⟨0, hn⟩
    have hpz : p.1 = z := by apply Fin.ext; simpa [z]
    dsimp only at hc
    rw [hpz, hc.1, hc.2]
    simp [z, hp2t]
    omega
  · have hp20 : p.2.val ≠ 0 := by omega
    rw [theorem1OldCloserCount n t h_lower h_upper p.1 p.2 hp0 hp20 hpne,
      theorem1OldCloserCount n t h_lower h_upper p.2 p.1 hp20 hp0 hpne.symm]
    have hreverse : ¬(p.2.val ≤ t ∧ t < p.1.val) := by omega
    by_cases hcross : p.1.val ≤ t ∧ t < p.2.val <;>
      simp [hp0, hcross, hreverse] <;> omega

lemma theorem1SzegedIndex (n t : ℕ)
    (h_lower : t ≥ 1) (h_upper : t ≤ n - 1) :
    szegedIndex (Knt n t) =
      n.choose 2 - (n - t - 1) + 2 * t * (n - t - 1) := by
  rw [theorem1SzegedIndexAsOrderedSum]
  change (∑ p ∈ theorem1OrderedEdges n t,
    closerCount (Knt n t) p.1 p.2 * closerCount (Knt n t) p.2 p.1) = _
  have hatt : (∑ p ∈ theorem1OrderedEdges n t,
      if p.1.val = 0 ∧ p.2.val ≤ t then n - t - 1 else 0) =
      (n - t - 1) * (theorem1AttachmentPairs n t).card := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      theorem1AttachmentFilter]
    simp [mul_comm]
  have hcross : (∑ p ∈ theorem1OrderedEdges n t,
      if p.1.val ≠ 0 ∧ p.1.val ≤ t ∧ t < p.2.val then 1 else 0) =
      (theorem1CrossPairs n t).card := by
    simpa [theorem1CrossFilter] using
      (Finset.sum_boole (R := ℕ)
        (fun p : Fin n × Fin n =>
          p.1.val ≠ 0 ∧ p.1.val ≤ t ∧ t < p.2.val)
        (theorem1OrderedEdges n t))
  calc
    _ = ∑ p ∈ theorem1OrderedEdges n t,
        (1 + (if p.1.val = 0 ∧ p.2.val ≤ t then n - t - 1 else 0) +
          (if p.1.val ≠ 0 ∧ p.1.val ≤ t ∧ t < p.2.val then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact theorem1EdgeContribution n t h_lower h_upper p
        (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
    _ = (theorem1OrderedEdges n t).card +
        (n - t - 1) * (theorem1AttachmentPairs n t).card +
          (theorem1CrossPairs n t).card := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hatt, hcross]
      simp
    _ = n.choose 2 - (n - t - 1) + 2 * t * (n - t - 1) := by
      rw [theorem1OrderedEdgesCard n t h_lower h_upper,
        theorem1AttachmentPairsCard n t h_lower h_upper,
        theorem1CrossPairsCard n t h_lower h_upper]
      ring

/-- The direct Wiener/Szeged computation for `K_n^t`. -/
theorem theorem1Proof1 (n t : ℕ) (h_lower : t ≥ 1) (h_upper : t ≤ n - 1) :
    szegedWienerGap (Knt n t) =
      2 * ((t : ℤ) - 1) * ((n : ℤ) - t - 1) := by
  /-
  The manuscript partitions the old clique into `theorem1A n t` and
  `theorem1B n t`.  Its edge contributions are respectively

  * `1` inside either part;
  * `2` between the two parts;
  * `n - t` on each edge from vertex `0` to `A`.

  Together with `W(K_n^t) = n.choose 2 + (n - t - 1)`, these counts simplify
  to `2(t-1)(n-t-1)`.
  -/
  have hle : n - t - 1 ≤ n.choose 2 := by
    rw [← theorem1SpecialPairsCard n t h_lower h_upper,
      ← theorem1OrderedPairsCard n]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have ht_le : t ≤ n := by omega
  have hone : 1 ≤ n - t := by omega
  have hcast : ((n - t - 1 : ℕ) : ℤ) = (n : ℤ) - t - 1 := by
    rw [Nat.cast_sub hone, Nat.cast_sub ht_le]
    push_cast
    rfl
  unfold szegedWienerGap
  rw [theorem1SzegedIndex n t h_lower h_upper,
    theorem1WienerIndex n t h_lower h_upper]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hle]
  rw [hcast]
  push_cast
  ring

end

end BKLPS
