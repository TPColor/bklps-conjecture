import Proof.Definitions

/-! Construction and structural verification of the sharpness graph `G_n`. -/

namespace BKLPS

open SimpleGraph

noncomputable section

/-- The graph `G_n` from the proof of Lemma 7: a clique `Q ≅ K_(n-2)`, two
new vertices `x,y`, and the additional edges `ax`, `by`, and `xy`.

On `Fin n`, the clique uses vertices `< n-2`, with `a=0`, `b=1`, `x=n-2`,
and `y=n-1`.  Only the range `n ≥ 10` is used. -/
def sharpnessGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧
    ((u.val < n - 2 ∧ v.val < n - 2) ∨
      (u.val = n - 2 ∧ v.val = 0) ∨ (v.val = n - 2 ∧ u.val = 0) ∨
      (u.val = n - 1 ∧ v.val = 1) ∨ (v.val = n - 1 ∧ u.val = 1) ∨
      (u.val = n - 2 ∧ v.val = n - 1) ∨
      (v.val = n - 2 ∧ u.val = n - 1))
  symm u v h := by
    rcases h with ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | h | h | h | h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  loopless u h := h.1 rfl

instance instDecidableRelSharpnessGraph (n : ℕ) : DecidableRel (sharpnessGraph n).Adj := by
  intro u v
  unfold sharpnessGraph
  infer_instance

/-- The clique `Q` in the sharpness construction. -/
def sharpnessCore (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun q => q.val < n - 2

/-- The set `A = V(Q) \ {a,b}` used in the Szeged-index computation. -/
def sharpnessOrdinaryCore (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun q => 2 ≤ q.val ∧ q.val < n - 2

lemma sharpnessWalkLeTwo (n : ℕ) (hn : n ≥ 10) (a b : Fin n) :
    ∃ p : (sharpnessGraph n).Walk a b, p.length ≤ 2 := by
  have h0n : 0 < n := by omega
  have h1n : 1 < n := by omega
  let z : Fin n := ⟨0, h0n⟩
  let o : Fin n := ⟨1, h1n⟩
  by_cases hab : a = b
  · subst b
    exact ⟨Walk.nil, by simp⟩
  by_cases hadj : (sharpnessGraph n).Adj a b
  · exact ⟨hadj.toWalk, by simp⟩
  have from_new (c d : Fin n) (hcd : c ≠ d)
      (hnadj : ¬(sharpnessGraph n).Adj c d) (hc : n - 2 ≤ c.val) :
      ∃ p : (sharpnessGraph n).Walk c d, p.length ≤ 2 := by
    have hc_cases : c.val = n - 2 ∨ c.val = n - 1 := by omega
    rcases hc_cases with hcval | hcval
    · have hcdcore : d.val < n - 2 := by
        by_contra h
        have hd_cases : d.val = n - 2 ∨ d.val = n - 1 := by omega
        rcases hd_cases with hd | hd
        · exact hcd (Fin.ext (by omega))
        · apply hnadj
          exact ⟨hcd, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨hcval, hd⟩)))))⟩
      have hcz : (sharpnessGraph n).Adj c z := by
        constructor
        · intro h
          have := congrArg Fin.val h
          simp [z] at this
          omega
        · exact Or.inr (Or.inl ⟨hcval, by simp [z]⟩)
      have hzd : (sharpnessGraph n).Adj z d := by
        constructor
        · intro h
          apply hnadj
          rw [← h]
          exact hcz
        · exact Or.inl ⟨by simp [z]; omega, hcdcore⟩
      exact ⟨hcz.toWalk.append hzd.toWalk, by simp⟩
    · have hcdcore : d.val < n - 2 := by
        by_contra h
        have hd_cases : d.val = n - 2 ∨ d.val = n - 1 := by omega
        rcases hd_cases with hd | hd
        · apply hnadj
          exact ⟨hcd, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr ⟨hd, hcval⟩)))))⟩
        · exact hcd (Fin.ext (by omega))
      have hco : (sharpnessGraph n).Adj c o := by
        constructor
        · intro h
          have := congrArg Fin.val h
          simp [o] at this
          omega
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hcval, by simp [o]⟩)))
      have hod : (sharpnessGraph n).Adj o d := by
        constructor
        · intro h
          apply hnadj
          rw [← h]
          exact hco
        · exact Or.inl ⟨by simp [o]; omega, hcdcore⟩
      exact ⟨hco.toWalk.append hod.toWalk, by simp⟩
  · have hnew : n - 2 ≤ a.val ∨ n - 2 ≤ b.val := by
      by_contra h
      push_neg at h
      apply hadj
      exact ⟨hab, Or.inl h⟩
    rcases hnew with ha | hb
    · exact from_new a b hab hadj ha
    · obtain ⟨p, hp⟩ := from_new b a (Ne.symm hab) (fun h => hadj h.symm) hb
      exact ⟨p.reverse, by simpa using hp⟩

lemma sharpnessConnected (n : ℕ) (hn : n ≥ 10) :
    (sharpnessGraph n).Connected := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨?_⟩
  intro a b
  obtain ⟨p, _⟩ := sharpnessWalkLeTwo n hn a b
  exact ⟨p⟩

lemma sharpnessDeleteConnected (n : ℕ) (hn : n ≥ 10) (v : Fin n) :
    ((sharpnessGraph n).induce {w : Fin n | w ≠ v}).Connected := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let x : Fin n := ⟨n - 2, by omega⟩
  let y : Fin n := ⟨n - 1, by omega⟩
  let cval : ℕ := if v.val = 2 then 3 else 2
  have hcval_lt : cval < n := by
    simp only [cval]
    split <;> omega
  let c : Fin n := ⟨cval, hcval_lt⟩
  have hcOrd : 2 ≤ c.val ∧ c.val < n - 2 := by
    simp only [c, cval]
    split <;> omega
  have hcv : c ≠ v := by
    intro h
    have hv := congrArg Fin.val h
    simp only [c, cval] at hv
    split at hv <;> omega
  let c' : {w : Fin n // w ≠ v} := ⟨c, hcv⟩
  have hcoreAdj {r s : Fin n} (hr : r.val < n - 2) (hs : s.val < n - 2)
      (hne : r ≠ s) : (sharpnessGraph n).Adj r s :=
    ⟨hne, Or.inl ⟨hr, hs⟩⟩
  have hinduceAdj {r s : Fin n} (hr : r ≠ v) (hs : s ≠ v)
      (h : (sharpnessGraph n).Adj r s) :
      ((sharpnessGraph n).induce {w : Fin n | w ≠ v}).Adj ⟨r, hr⟩ ⟨s, hs⟩ := h
  have reachHub (z : {w : Fin n // w ≠ v}) :
      ((sharpnessGraph n).induce {w : Fin n | w ≠ v}).Reachable z c' := by
    by_cases hzc : z.1 = c
    · have hzceq : z = c' := Subtype.ext hzc
      subst z
      exact ⟨Walk.nil⟩
    by_cases hzcore : z.1.val < n - 2
    · exact (hinduceAdj z.2 hcv (hcoreAdj hzcore hcOrd.2 hzc)).reachable
    have hznew : z.1.val = n - 2 ∨ z.1.val = n - 1 := by omega
    rcases hznew with hzx | hzy
    · by_cases hva : v = a
      · have hyv : y ≠ v := by
          intro h
          have hv := congrArg Fin.val (h.trans hva)
          simp [a, y] at hv
          omega
        have hbv : b ≠ v := by
          intro h
          have hv := congrArg Fin.val (h.trans hva)
          simp [a, b] at hv
        let y' : {w : Fin n // w ≠ v} := ⟨y, hyv⟩
        let b' : {w : Fin n // w ≠ v} := ⟨b, hbv⟩
        have hzyAdj : (sharpnessGraph n).Adj z.1 y := by
          refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨hzx, by simp [y]⟩)))))⟩
          intro h
          have hv := congrArg Fin.val h
          simp [y] at hv
          omega
        have hybAdj : (sharpnessGraph n).Adj y b := by
          refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inl
            ⟨by simp [y], by simp [b]⟩)))⟩
          intro h
          have hv := congrArg Fin.val h
          simp [y, b] at hv
          omega
        have hbcAdj : (sharpnessGraph n).Adj b c :=
          hcoreAdj (by simp [b]; omega) hcOrd.2 (by
            intro h
            have hv := congrArg Fin.val h
            simp [b] at hv
            omega)
        exact (hinduceAdj z.2 hyv hzyAdj).reachable |>.trans
          ((hinduceAdj hyv hbv hybAdj).reachable |>.trans
            (hinduceAdj hbv hcv hbcAdj).reachable)
      · have hav : a ≠ v := Ne.symm hva
        let a' : {w : Fin n // w ≠ v} := ⟨a, hav⟩
        have hzaAdj : (sharpnessGraph n).Adj z.1 a := by
          refine ⟨?_, Or.inr (Or.inl ⟨hzx, by simp [a]⟩)⟩
          intro h
          have hv := congrArg Fin.val h
          simp [a] at hv
          omega
        have hacAdj : (sharpnessGraph n).Adj a c :=
          hcoreAdj (by simp [a]; omega) hcOrd.2 (by
            intro h
            have hv := congrArg Fin.val h
            simp [a] at hv
            omega)
        exact (hinduceAdj z.2 hav hzaAdj).reachable |>.trans
          (hinduceAdj hav hcv hacAdj).reachable
    · by_cases hvb : v = b
      · have hxv : x ≠ v := by
          intro h
          have hv := congrArg Fin.val (h.trans hvb)
          simp [b, x] at hv
          omega
        have hav : a ≠ v := by
          intro h
          have hv := congrArg Fin.val (h.trans hvb)
          simp [a, b] at hv
        let x' : {w : Fin n // w ≠ v} := ⟨x, hxv⟩
        let a' : {w : Fin n // w ≠ v} := ⟨a, hav⟩
        have hzxAdj : (sharpnessGraph n).Adj z.1 x := by
          refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr ⟨by simp [x], hzy⟩)))))⟩
          intro h
          have hv := congrArg Fin.val h
          simp [x] at hv
          omega
        have hxaAdj : (sharpnessGraph n).Adj x a := by
          refine ⟨?_, Or.inr (Or.inl ⟨by simp [x], by simp [a]⟩)⟩
          intro h
          have hv := congrArg Fin.val h
          simp [x, a] at hv
          omega
        have hacAdj : (sharpnessGraph n).Adj a c :=
          hcoreAdj (by simp [a]; omega) hcOrd.2 (by
            intro h
            have hv := congrArg Fin.val h
            simp [a] at hv
            omega)
        exact (hinduceAdj z.2 hxv hzxAdj).reachable |>.trans
          ((hinduceAdj hxv hav hxaAdj).reachable |>.trans
            (hinduceAdj hav hcv hacAdj).reachable)
      · have hbv : b ≠ v := Ne.symm hvb
        let b' : {w : Fin n // w ≠ v} := ⟨b, hbv⟩
        have hzbAdj : (sharpnessGraph n).Adj z.1 b := by
          refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hzy, by simp [b]⟩)))⟩
          intro h
          have hv := congrArg Fin.val h
          simp [b] at hv
          omega
        have hbcAdj : (sharpnessGraph n).Adj b c :=
          hcoreAdj (by simp [b]; omega) hcOrd.2 (by
            intro h
            have hv := congrArg Fin.val h
            simp [b] at hv
            omega)
        exact (hinduceAdj z.2 hbv hzbAdj).reachable |>.trans
          (hinduceAdj hbv hcv hbcAdj).reachable
  exact (SimpleGraph.connected_iff
    ((sharpnessGraph n).induce {w : Fin n | w ≠ v})).mpr
    ⟨fun r s => (reachHub r).trans (reachHub s).symm, ⟨c'⟩⟩

private lemma sharpnessXDegree (n : ℕ) (hn : n ≥ 10) :
    (sharpnessGraph n).degree ⟨n - 2, by omega⟩ = 2 := by
  let x : Fin n := ⟨n - 2, by omega⟩
  let a : Fin n := ⟨0, by omega⟩
  let y : Fin n := ⟨n - 1, by omega⟩
  have hneighbors : (sharpnessGraph n).neighborFinset x = {a, y} := by
    ext z
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨_, h | h | h | h | h | h | h⟩
      · have hh := h.1
        change n - 2 < n - 2 at hh
        omega
      · exact Or.inl (Fin.ext (by change z.val = 0; exact h.2))
      · have hh := h.2
        change n - 2 = 0 at hh
        omega
      · have hh := h.1
        change n - 2 = n - 1 at hh
        omega
      · have hh := h.2
        change n - 2 = 1 at hh
        omega
      · exact Or.inr (Fin.ext (by change z.val = n - 1; exact h.2))
      · have hh := h.2
        change n - 2 = n - 1 at hh
        omega
    · rintro (rfl | rfl)
      · refine ⟨?_, Or.inr (Or.inl ⟨by simp [x], by simp [a]⟩)⟩
        intro h
        have hv := congrArg Fin.val h
        simp [x, a] at hv
        omega
      · refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨by simp [x], by simp [y]⟩)))))⟩
        intro h
        have hv := congrArg Fin.val h
        simp [x, y] at hv
        omega
  change ((sharpnessGraph n).neighborFinset x).card = 2
  rw [hneighbors]
  have hay : a ≠ y := by
    intro h
    have hv := congrArg Fin.val h
    simp [a, y] at hv
    omega
  simp [hay]

private lemma sharpnessYDegree (n : ℕ) (hn : n ≥ 10) :
    (sharpnessGraph n).degree ⟨n - 1, by omega⟩ = 2 := by
  let y : Fin n := ⟨n - 1, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let x : Fin n := ⟨n - 2, by omega⟩
  have hneighbors : (sharpnessGraph n).neighborFinset y = {b, x} := by
    ext z
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨_, h | h | h | h | h | h | h⟩
      · have hh := h.1
        change n - 1 < n - 2 at hh
        omega
      · have hh := h.1
        change n - 1 = n - 2 at hh
        omega
      · have hh := h.2
        change n - 1 = 0 at hh
        omega
      · exact Or.inl (Fin.ext (by simp [b, y] at h ⊢; omega))
      · have hh := h.2
        change n - 1 = 1 at hh
        omega
      · have hh := h.1
        change n - 1 = n - 2 at hh
        omega
      · exact Or.inr (Fin.ext (by change z.val = n - 2; exact h.1))
    · rintro (rfl | rfl)
      · refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inl
          ⟨by simp [y], by simp [b]⟩)))⟩
        intro h
        have hv := congrArg Fin.val h
        simp [y, b] at hv
        omega
      · refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr ⟨by simp [x], by simp [y]⟩)))))⟩
        intro h
        have hv := congrArg Fin.val h
        simp [x, y] at hv
        omega
  change ((sharpnessGraph n).neighborFinset y).card = 2
  rw [hneighbors]
  have hbx : b ≠ x := by
    intro h
    have hv := congrArg Fin.val h
    simp [b, x] at hv
    omega
  simp [hbx]

private lemma KntOldDegreeLower (n t : ℕ) (hn : n ≥ 3) (q : Fin n)
    (hq : q.val ≠ 0) : n - 2 ≤ (Knt n t).degree q := by
  let z : Fin n := ⟨0, by omega⟩
  let s : Finset (Fin n) := (Finset.univ.erase z).erase q
  have hqmem : q ∈ Finset.univ.erase z := by
    simp [z]
    intro h
    have hv := congrArg Fin.val h
    simp [z] at hv
    exact hq hv
  have hzmem : z ∈ (Finset.univ : Finset (Fin n)) := by simp
  have hscard : s.card = n - 2 := by
    change (((Finset.univ : Finset (Fin n)).erase z).erase q).card = n - 2
    rw [Finset.card_erase_of_mem hqmem,
      Finset.card_erase_of_mem hzmem]
    simp
    omega
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hscard]
  apply Finset.card_le_card
  intro r hr
  have hrs : r ≠ q ∧ r ≠ z := by
    simpa [s] using hr
  simp only [SimpleGraph.mem_neighborFinset]
  refine ⟨hrs.1.symm, Or.inl ⟨hq, ?_⟩⟩
  intro hr0
  apply hrs.2
  apply Fin.ext
  simp [z, hr0]

private lemma KntZeroDegreeLower (n t : ℕ) (hn : n ≥ 4) (ht : t ≥ 3) :
    3 ≤ (Knt n t).degree ⟨0, by omega⟩ := by
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  let w : Fin n := ⟨2, by omega⟩
  let r : Fin n := ⟨3, by omega⟩
  let s : Finset (Fin n) := {o, w, r}
  have hscard : s.card = 3 := by
    simp [s, o, w, r]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hscard]
  apply Finset.card_le_card
  intro q hq
  simp only [s, Finset.mem_insert, Finset.mem_singleton] at hq
  simp only [SimpleGraph.mem_neighborFinset]
  rcases hq with rfl | rfl | rfl
  · exact ⟨by simp [z, o], Or.inr (Or.inl ⟨by simp [z], by simp [o]; omega⟩)⟩
  · exact ⟨by simp [z, w], Or.inr (Or.inl ⟨by simp [z], by simp [w]; omega⟩)⟩
  · exact ⟨by simp [z, r], Or.inr (Or.inl ⟨by simp [z], by simp [r]; omega⟩)⟩

/-- The constructed graph is 2-connected and unexceptional. -/
theorem lemma7Proof1 (n : ℕ) (h_order : n ≥ 10) :
    IsTwoConnected (sharpnessGraph n) ∧ IsUnexceptional (sharpnessGraph n) := by
  /-
  Deleting either new vertex leaves the clique together with a leaf attached
  to it, hence connected; deleting a clique vertex leaves the two new
  vertices attached through the remaining clique (or directly through `xy`).
  Degree and nonedge patterns distinguish this graph from all three
  exceptional graphs.
  -/
  constructor
  · exact ⟨by simp; omega, sharpnessConnected n h_order,
      sharpnessDeleteConnected n h_order⟩
  · intro hexceptional
    rcases hexceptional with hcomplete | hknt2 | hkntn2
    · unfold IsomorphicToKn at hcomplete
      obtain ⟨e⟩ := hcomplete
      let b : Fin n := ⟨1, by omega⟩
      let x : Fin n := ⟨n - 2, by omega⟩
      have hbxne : b ≠ x := by
        intro h
        have hv := congrArg Fin.val h
        simp [b, x] at hv
        omega
      have hbx : ¬(sharpnessGraph n).Adj b x := by
        rintro ⟨_, h | h | h | h | h | h | h⟩ <;>
          simp [b, x] at h <;> omega
      have himgne : e b ≠ e x := fun h => hbxne (e.injective h)
      have htarget : (completeGraph (Fin (Fintype.card (Fin n)))).Adj
          (e b) (e x) := by
        simpa using himgne
      exact hbx (e.map_rel_iff.mp htarget)
    · unfold IsomorphicToKnt at hknt2
      obtain ⟨e⟩ := hknt2
      let x : Fin n := ⟨n - 2, by omega⟩
      let y : Fin n := ⟨n - 1, by omega⟩
      have hxyne : x ≠ y := by
        intro h
        have hv := congrArg Fin.val h
        simp [x, y] at hv
        omega
      have hxdeg : (Knt (Fintype.card (Fin n)) 2).degree (e x) = 2 := by
        rw [e.degree_eq]
        simpa [x] using sharpnessXDegree n h_order
      have hydeg : (Knt (Fintype.card (Fin n)) 2).degree (e y) = 2 := by
        rw [e.degree_eq]
        simpa [y] using sharpnessYDegree n h_order
      have hxzero : (e x).val = 0 := by
        by_contra h
        have hlower := KntOldDegreeLower (Fintype.card (Fin n)) 2
          (by simp; omega) (e x) h
        simp only [Fintype.card_fin] at hlower
        rw [hxdeg] at hlower
        omega
      have hyzero : (e y).val = 0 := by
        by_contra h
        have hlower := KntOldDegreeLower (Fintype.card (Fin n)) 2
          (by simp; omega) (e y) h
        simp only [Fintype.card_fin] at hlower
        rw [hydeg] at hlower
        omega
      apply hxyne
      apply e.injective
      exact Fin.ext (by omega)
    · unfold IsomorphicToKnt at hkntn2
      obtain ⟨e⟩ := hkntn2
      let x : Fin n := ⟨n - 2, by omega⟩
      have hxdeg : (Knt (Fintype.card (Fin n))
          (Fintype.card (Fin n) - 2)).degree (e x) = 2 := by
        rw [e.degree_eq]
        simpa [x] using sharpnessXDegree n h_order
      by_cases hxzero : (e x).val = 0
      · have hlower := KntZeroDegreeLower (Fintype.card (Fin n))
          (Fintype.card (Fin n) - 2) (by simp; omega) (by simp; omega)
        have heq : e x =
            (⟨0, by simp; omega⟩ : Fin (Fintype.card (Fin n))) := Fin.ext hxzero
        rw [← heq, hxdeg] at hlower
        omega
      · have hlower := KntOldDegreeLower (Fintype.card (Fin n))
          (Fintype.card (Fin n) - 2) (by simp; omega) (e x) hxzero
        simp only [Fintype.card_fin] at hlower
        rw [hxdeg] at hlower
        omega

end

end BKLPS
