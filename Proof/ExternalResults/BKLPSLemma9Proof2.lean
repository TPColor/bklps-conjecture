import Proof.ExternalResults.BKLPSLemma9Proof1
import Proof.ExternalResults.UniqueCutBlocks
import Proof.ExternalResults.GraphIsomorphismInvariants

/-! The block conclusion from the proof of BKLPS Lemma 9. -/

namespace BKLPS.External

open SimpleGraph

noncomputable section

universe u

/-- A graph with two distinct vertices and no edges is disconnected. -/
theorem not_connected_of_no_edges
    {W : Type u} (K : SimpleGraph W) (a b : W) (hab : a ≠ b)
    (hno : ∀ x y : W, ¬K.Adj x y) : ¬K.Connected := by
  intro hconn
  obtain ⟨p⟩ := hconn a b
  induction p with
  | nil => exact hab rfl
  | @cons x y z hxy p ih => exact hno x y hxy

/-- Among three distinct candidates one can choose two, neither forced to
be the distinguished vertex, in the direction of any Boolean attachment
implication.  The third candidate remains available for rerouting. -/
theorem orient_three_candidates
    {α : Type u} (P Q : α → Prop) [DecidablePred P]
    (a b c v : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hQa : Q a) (hQb : Q b) (hQc : Q c) :
    ∃ z w r : α, z ≠ w ∧ z ≠ r ∧ w ≠ r ∧ z ≠ v ∧ w ≠ v ∧
      Q z ∧ Q w ∧ Q r ∧ (P z → P w) := by
  have choose (s t r : α) (hst : s ≠ t) (hsr : s ≠ r) (htr : t ≠ r)
      (hsv : s ≠ v) (htv : t ≠ v)
      (hQs : Q s) (hQt : Q t) (hQr : Q r) :
      ∃ z w r' : α, z ≠ w ∧ z ≠ r' ∧ w ≠ r' ∧ z ≠ v ∧ w ≠ v ∧
        Q z ∧ Q w ∧ Q r' ∧ (P z → P w) := by
    by_cases hs : P s
    · by_cases ht : P t
      · exact ⟨s, t, r, hst, hsr, htr, hsv, htv,
          hQs, hQt, hQr, fun _ => ht⟩
      · exact ⟨t, s, r, hst.symm, htr, hsr, htv, hsv,
          hQt, hQs, hQr, fun h => False.elim (ht h)⟩
    · exact ⟨s, t, r, hst, hsr, htr, hsv, htv,
        hQs, hQt, hQr, fun h => False.elim (hs h)⟩
  by_cases hva : v = a
  · exact choose b c a hbc hab.symm hac.symm
      (by simpa [hva] using hab.symm) (by simpa [hva] using hac.symm)
      hQb hQc hQa
  · by_cases hvb : v = b
    · exact choose a c b hac hab hbc.symm
        (by simpa [hvb] using hab) (by simpa [hvb] using hbc.symm)
        hQa hQc hQb
    · by_cases hvc : v = c
      · exact choose a b c hab hac hbc
          (by simpa [hvc] using hac) (by simpa [hvc] using hbc) hQa hQb hQc
      · exact choose a b c hab hac hbc (fun h => hva h.symm)
          (fun h => hvb h.symm) hQa hQb hQc

/-- A dominating vertex of a block also dominates a non-cut vertex in the
whole graph, provided it receives the deleted-vertex attachment whenever
the dominated vertex does.  Edges from a non-cut block vertex cannot leave
its block, which is the substantive point of this conversion. -/
theorem closedNeighborhood_subset_of_block_dominates
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u}) (hC : IsBlock (deleteVertex G u) C)
    (z w : {x : V // x ≠ u}) (hzC : z ∈ C) (hwC : w ∈ C)
    (hzv : z.1 ≠ v) (hzw : z ≠ w)
    (hwdom : ∀ t : C, (⟨w, hwC⟩ : C) ≠ t →
      ((deleteVertex G u).induce C).Adj ⟨w, hwC⟩ t)
    (hattach : G.Adj u z.1 → G.Adj u w.1) :
    closedNeighborhood G z.1 ⊆ closedNeighborhood G w.1 := by
  classical
  intro t ht
  have ht' : t = z.1 ∨ G.Adj z.1 t := by
    simpa [closedNeighborhood, openNeighborhood] using ht
  rcases ht' with rfl | hzt
  · have hwz : G.Adj w.1 z.1 := by
      have h := hwdom ⟨z, hzC⟩ (by
        intro heq
        exact hzw (congrArg Subtype.val heq).symm)
      exact h
    simp [closedNeighborhood, openNeighborhood, hwz]
  · by_cases htu : t = u
    · subst t
      have huw : G.Adj u w.1 := hattach hzt.symm
      simp [closedNeighborhood, openNeighborhood, huw.symm]
    · let t' : {x : V // x ≠ u} := ⟨t, htu⟩
      have htC : t' ∈ C :=
        adj_mem_isBlock_of_uniqueCut (deleteVertex G u) ⟨v, huv.symm⟩
          hunique C hC hzC (by
            intro h
            exact hzv (congrArg Subtype.val h)) hzt
      by_cases htw : t' = w
      · have : t = w.1 := congrArg Subtype.val htw
        simp [closedNeighborhood, this]
      · have hwt := hwdom ⟨t', htC⟩ (by
          intro heq
          exact htw (congrArg Subtype.val heq).symm)
        have hwtG : G.Adj w.1 t := hwt
        simp [closedNeighborhood, openNeighborhood, hwtG]

/-- The preceding bridge only needs local closed-neighborhood containment;
full domination is a convenient special case. -/
theorem closedNeighborhood_subset_of_block_subset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u}) (hC : IsBlock (deleteVertex G u) C)
    (z w : {x : V // x ≠ u}) (hzC : z ∈ C) (hwC : w ∈ C)
    (hzv : z.1 ≠ v) (hzw : z ≠ w)
    (hlocal : ∀ t : C, t = ⟨z, hzC⟩ ∨
        ((deleteVertex G u).induce C).Adj ⟨z, hzC⟩ t →
      t = ⟨w, hwC⟩ ∨
        ((deleteVertex G u).induce C).Adj ⟨w, hwC⟩ t)
    (hattach : G.Adj u z.1 → G.Adj u w.1) :
    closedNeighborhood G z.1 ⊆ closedNeighborhood G w.1 := by
  classical
  intro t ht
  have ht' : t = z.1 ∨ G.Adj z.1 t := by
    simpa [closedNeighborhood, openNeighborhood] using ht
  by_cases htu : t = u
  · subst t
    have huz : G.Adj u z.1 := by
      rcases ht' with h | h
      · exact False.elim (z.2 h.symm)
      · exact h.symm
    have huw := hattach huz
    simp [closedNeighborhood, openNeighborhood, huw.symm]
  · let tH : {x : V // x ≠ u} := ⟨t, htu⟩
    have htC : tH ∈ C := by
      rcases ht' with h | h
      · have : tH = z := Subtype.ext h
        simpa [this] using hzC
      · exact adj_mem_isBlock_of_uniqueCut (deleteVertex G u)
          ⟨v, huv.symm⟩ hunique C hC hzC (by
            intro hvc
            exact hzv (congrArg Subtype.val hvc)) h
    have hloc := hlocal ⟨tH, htC⟩ (by
      rcases ht' with h | h
      · left
        apply Subtype.ext
        apply Subtype.ext
        exact h
      · right
        exact h)
    rcases hloc with h | h
    · have : t = w.1 := congrArg (fun q : C => q.1.1) h
      simp [closedNeighborhood, this]
    · have hwt : G.Adj w.1 t := h
      simp [closedNeighborhood, openNeighborhood, hwt]

/-- If a third vertex dominates a block, every walk in `G-u` can be
rerouted away from two specified non-cut vertices of that block.  Adding the
edge `uv` then connects the surviving copy of `u` as well. -/
theorem connected_avoiding_two_of_block_dominator
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (huvAdj : G.Adj u v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u}) (hC : IsBlock (deleteVertex G u) C)
    (z w r : {x : V // x ≠ u})
    (hzC : z ∈ C) (hwC : w ∈ C) (hrC : r ∈ C)
    (hzv : z.1 ≠ v) (hwv : w.1 ≠ v)
    (hzw : z ≠ w) (hzr : z ≠ r) (hwr : w ≠ r)
    (hrdom : ∀ t : C, (⟨r, hrC⟩ : C) ≠ t →
      ((deleteVertex G u).induce C).Adj ⟨r, hrC⟩ t) :
    (G.induce {x : V | x ≠ z.1 ∧ x ≠ w.1}).Connected := by
  classical
  let H := deleteVertex G u
  let J := G.induce {x : V | x ≠ z.1 ∧ x ≠ w.1}
  let vc : {x : V // x ≠ u} := ⟨v, huv.symm⟩
  let rJ : {x : V // x ≠ z.1 ∧ x ≠ w.1} :=
    ⟨r.1, fun h => hzr (Subtype.ext h.symm),
      fun h => hwr (Subtype.ext h.symm)⟩
  let f : {x : V // x ≠ u} → {x : V // x ≠ z.1 ∧ x ≠ w.1} :=
    fun x => if h : x = z ∨ x = w then rJ else
      ⟨x.1, fun hx => h (Or.inl (Subtype.ext hx)),
        fun hx => h (Or.inr (Subtype.ext hx))⟩
  have hf : ∀ a b : {x : V // x ≠ u}, H.Adj a b →
      f a = f b ∨ J.Adj (f a) (f b) := by
    intro a b hab
    by_cases ha : a = z ∨ a = w
    · simp only [f, dif_pos ha]
      by_cases hb : b = z ∨ b = w
      · left
        simp only [dif_pos hb]
      · simp only [dif_neg hb]
        have hbC : b ∈ C := by
          rcases ha with rfl | rfl
          · exact adj_mem_isBlock_of_uniqueCut H vc hunique C hC hzC
              (by intro h; exact hzv (congrArg Subtype.val h)) hab
          · exact adj_mem_isBlock_of_uniqueCut H vc hunique C hC hwC
              (by intro h; exact hwv (congrArg Subtype.val h)) hab
        by_cases hbr : b = r
        · left
          subst b
          apply Subtype.ext
          rfl
        · right
          have hrb := hrdom ⟨b, hbC⟩ (by
            intro h
            exact hbr (congrArg Subtype.val h).symm)
          exact hrb
    · simp only [f, dif_neg ha]
      by_cases hb : b = z ∨ b = w
      · simp only [dif_pos hb]
        have haC : a ∈ C := by
          rcases hb with rfl | rfl
          · exact adj_mem_isBlock_of_uniqueCut H vc hunique C hC hzC
              (by intro h; exact hzv (congrArg Subtype.val h)) hab.symm
          · exact adj_mem_isBlock_of_uniqueCut H vc hunique C hC hwC
              (by intro h; exact hwv (congrArg Subtype.val h)) hab.symm
        by_cases har : a = r
        · left
          subst a
          apply Subtype.ext
          rfl
        · right
          have hra := hrdom ⟨a, haC⟩ (by
            intro h
            exact har (congrArg Subtype.val h).symm)
          exact hra.symm
      · simp only [dif_neg hb]
        exact Or.inr hab
  let uJ : {x : V // x ≠ z.1 ∧ x ≠ w.1} :=
    ⟨u, z.2.symm, w.2.symm⟩
  let vJ : {x : V // x ≠ z.1 ∧ x ≠ w.1} :=
    ⟨v, hzv.symm, hwv.symm⟩
  haveI : Nonempty {x : V // x ≠ z.1 ∧ x ≠ w.1} := ⟨uJ⟩
  have hreach (a : {x : V // x ≠ z.1 ∧ x ≠ w.1}) :
      J.Reachable a uJ := by
    by_cases hau : a.1 = u
    · have h : a = uJ := Subtype.ext hau
      subst a
      exact Reachable.refl uJ
    · let aH : {x : V // x ≠ u} := ⟨a.1, hau⟩
      obtain ⟨p⟩ := hunique.1.2.1 aH vc
      let q := Walk.mapAdjOrEq f (by
        intro x y hxy
        exact hf x y hxy) p
      have hfa : f aH = a := by
        have haz : aH ≠ z := by
          intro h
          exact a.2.1 (congrArg Subtype.val h)
        have haw : aH ≠ w := by
          intro h
          exact a.2.2 (congrArg Subtype.val h)
        apply Subtype.ext
        simp [f, haz, haw, aH]
      have hfv : f vc = vJ := by
        have hvz : vc ≠ z := by
          intro h
          exact hzv (congrArg Subtype.val h).symm
        have hvw : vc ≠ w := by
          intro h
          exact hwv (congrArg Subtype.val h).symm
        apply Subtype.ext
        simp [f, hvz, hvw, vc, vJ]
      have hav : J.Reachable a vJ := by
        exact ⟨q.copy hfa hfv⟩
      have hvu : J.Adj vJ uJ := huvAdj.symm
      exact hav.trans hvu.reachable
  change J.Connected
  rw [connected_iff_exists_forall_reachable]
  exact ⟨uJ, fun a => (hreach a).symm⟩

/-- A two-point version of the preceding rerouting argument.  Each deleted
block vertex may be replaced by its own surviving block vertex; the three
local hypotheses say precisely that this replacement sends every affected
edge to an edge or collapses it.  This is the form needed for the small
`K_t^2` attachment patterns in BKLPS Case 2. -/
theorem connected_avoiding_two_of_block_replacements
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (huvAdj : G.Adj u v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u}) (hC : IsBlock (deleteVertex G u) C)
    (z w rz rw : {x : V // x ≠ u})
    (hzC : z ∈ C) (hwC : w ∈ C) (hrzC : rz ∈ C) (hrwC : rw ∈ C)
    (hzv : z.1 ≠ v) (hwv : w.1 ≠ v) (hzw : z ≠ w)
    (hzrz : z ≠ rz) (hwrz : w ≠ rz) (hzrw : z ≠ rw) (hwrw : w ≠ rw)
    (hzmap : ∀ t : C,
      ((deleteVertex G u).induce C).Adj ⟨z, hzC⟩ t →
        rz = t.1 ∨ ((deleteVertex G u).induce C).Adj ⟨rz, hrzC⟩ t)
    (hwmap : ∀ t : C,
      ((deleteVertex G u).induce C).Adj ⟨w, hwC⟩ t →
        rw = t.1 ∨ ((deleteVertex G u).induce C).Adj ⟨rw, hrwC⟩ t)
    (hcross : rz = rw ∨ (deleteVertex G u).Adj rz rw) :
    (G.induce {x : V | x ≠ z.1 ∧ x ≠ w.1}).Connected := by
  classical
  let H := deleteVertex G u
  let J := G.induce {x : V | x ≠ z.1 ∧ x ≠ w.1}
  let vc : {x : V // x ≠ u} := ⟨v, huv.symm⟩
  let rzJ : {x : V // x ≠ z.1 ∧ x ≠ w.1} :=
    ⟨rz.1, fun h => hzrz (Subtype.ext h.symm),
      fun h => hwrz (Subtype.ext h.symm)⟩
  let rwJ : {x : V // x ≠ z.1 ∧ x ≠ w.1} :=
    ⟨rw.1, fun h => hzrw (Subtype.ext h.symm),
      fun h => hwrw (Subtype.ext h.symm)⟩
  let f : {x : V // x ≠ u} → {x : V // x ≠ z.1 ∧ x ≠ w.1} :=
    fun x => if hxz : x = z then rzJ else if hxw : x = w then rwJ else
      ⟨x.1, fun h => hxz (Subtype.ext h), fun h => hxw (Subtype.ext h)⟩
  have hf : ∀ a b : {x : V // x ≠ u}, H.Adj a b →
      f a = f b ∨ J.Adj (f a) (f b) := by
    intro a b hab
    by_cases haz : a = z
    · subst a
      have hbz : b ≠ z := by intro h; subst b; exact hab.ne rfl
      by_cases hbw : b = w
      · subst b
        simp only [f, dif_pos rfl, dif_neg hzw.symm]
        change rzJ = rwJ ∨ J.Adj rzJ rwJ
        rcases hcross with h | h
        · left
          exact Subtype.ext (congrArg (fun q : {x : V // x ≠ u} => q.1) h)
        · right; exact h
      · let bJ : {x : V // x ≠ z.1 ∧ x ≠ w.1} :=
          ⟨b.1, fun h => hbz (Subtype.ext h), fun h => hbw (Subtype.ext h)⟩
        simp only [f, dif_pos rfl, dif_neg hbz, dif_neg hbw]
        change rzJ = bJ ∨ J.Adj rzJ bJ
        have hbC : b ∈ C :=
          adj_mem_isBlock_of_uniqueCut H vc hunique C hC hzC
            (by intro h; exact hzv (congrArg Subtype.val h)) hab
        rcases hzmap ⟨b, hbC⟩ hab with h | h
        · left
          exact Subtype.ext (congrArg (fun q : {x : V // x ≠ u} => q.1) h)
        · right; exact h
    · by_cases haw : a = w
      · subst a
        have hbw : b ≠ w := by intro h; subst b; exact hab.ne rfl
        by_cases hbz : b = z
        · subst b
          simp only [f, dif_neg hzw.symm, dif_pos rfl]
          change rwJ = rzJ ∨ J.Adj rwJ rzJ
          rcases hcross with h | h
          · left
            exact Subtype.ext
              (congrArg (fun q : {x : V // x ≠ u} => q.1) h).symm
          · right; exact h.symm
        · let bJ : {x : V // x ≠ z.1 ∧ x ≠ w.1} :=
            ⟨b.1, fun h => hbz (Subtype.ext h), fun h => hbw (Subtype.ext h)⟩
          simp only [f, dif_neg hzw.symm, dif_pos rfl, dif_neg hbz, dif_neg hbw]
          change rwJ = bJ ∨ J.Adj rwJ bJ
          have hbC : b ∈ C :=
            adj_mem_isBlock_of_uniqueCut H vc hunique C hC hwC
              (by intro h; exact hwv (congrArg Subtype.val h)) hab
          rcases hwmap ⟨b, hbC⟩ hab with h | h
          · left
            exact Subtype.ext (congrArg (fun q : {x : V // x ≠ u} => q.1) h)
          · right; exact h
      · by_cases hbz : b = z
        · subst b
          let aJ : {x : V // x ≠ z.1 ∧ x ≠ w.1} :=
            ⟨a.1, fun h => haz (Subtype.ext h), fun h => haw (Subtype.ext h)⟩
          simp only [f, dif_neg haz, dif_neg haw, dif_pos rfl]
          change aJ = rzJ ∨ J.Adj aJ rzJ
          have haC : a ∈ C :=
            adj_mem_isBlock_of_uniqueCut H vc hunique C hC hzC
              (by intro h; exact hzv (congrArg Subtype.val h)) hab.symm
          rcases hzmap ⟨a, haC⟩ hab.symm with h | h
          · left
            exact Subtype.ext
              (congrArg (fun q : {x : V // x ≠ u} => q.1) h).symm
          · right; exact h.symm
        · by_cases hbw : b = w
          · subst b
            let aJ : {x : V // x ≠ z.1 ∧ x ≠ w.1} :=
              ⟨a.1, fun h => haz (Subtype.ext h), fun h => haw (Subtype.ext h)⟩
            simp only [f, dif_neg haz, dif_neg haw, dif_pos rfl, dif_neg hzw.symm]
            change aJ = rwJ ∨ J.Adj aJ rwJ
            have haC : a ∈ C :=
              adj_mem_isBlock_of_uniqueCut H vc hunique C hC hwC
                (by intro h; exact hwv (congrArg Subtype.val h)) hab.symm
            rcases hwmap ⟨a, haC⟩ hab.symm with h | h
            · left
              exact Subtype.ext
                (congrArg (fun q : {x : V // x ≠ u} => q.1) h).symm
            · right; exact h.symm
          · let aJ : {x : V // x ≠ z.1 ∧ x ≠ w.1} :=
              ⟨a.1, fun h => haz (Subtype.ext h), fun h => haw (Subtype.ext h)⟩
            let bJ : {x : V // x ≠ z.1 ∧ x ≠ w.1} :=
              ⟨b.1, fun h => hbz (Subtype.ext h), fun h => hbw (Subtype.ext h)⟩
            simp only [f, dif_neg haz, dif_neg haw, dif_neg hbz, dif_neg hbw]
            change aJ = bJ ∨ J.Adj aJ bJ
            exact Or.inr hab
  let uJ : {x : V // x ≠ z.1 ∧ x ≠ w.1} := ⟨u, z.2.symm, w.2.symm⟩
  let vJ : {x : V // x ≠ z.1 ∧ x ≠ w.1} := ⟨v, hzv.symm, hwv.symm⟩
  haveI : Nonempty {x : V // x ≠ z.1 ∧ x ≠ w.1} := ⟨uJ⟩
  have hreach (a : {x : V // x ≠ z.1 ∧ x ≠ w.1}) : J.Reachable a uJ := by
    by_cases hau : a.1 = u
    · have ha : a = uJ := Subtype.ext hau
      subst a
      exact Reachable.refl uJ
    · let aH : {x : V // x ≠ u} := ⟨a.1, hau⟩
      obtain ⟨p⟩ := hunique.1.2.1 aH vc
      let q := Walk.mapAdjOrEq f (fun {_ _} hxy => hf _ _ hxy) p
      have hfa : f aH = a := by
        have haz : aH ≠ z := by intro h; exact a.2.1 (congrArg Subtype.val h)
        have haw : aH ≠ w := by intro h; exact a.2.2 (congrArg Subtype.val h)
        apply Subtype.ext
        simp [f, haz, haw, aH]
      have hfv : f vc = vJ := by
        have hvz : vc ≠ z := by intro h; exact hzv (congrArg Subtype.val h).symm
        have hvw : vc ≠ w := by intro h; exact hwv (congrArg Subtype.val h).symm
        apply Subtype.ext
        simp [f, hvz, hvw, vc, vJ]
      have hav : J.Reachable a vJ := ⟨q.copy hfa hfv⟩
      exact hav.trans (show J.Adj vJ uJ from huvAdj.symm).reachable
  change J.Connected
  rw [connected_iff_exists_forall_reachable]
  exact ⟨uJ, fun a => (hreach a).symm⟩

/-- If the global dominator is the cut vertex itself, delete that cut
vertex first.  A surviving neighbor `x` of `u` replaces `z`; every affected
block edge is then routed through the surviving local dominator `r`. -/
theorem connected_avoiding_block_vertex_and_cut
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G)
    (u v : V) (huv : u ≠ v)
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {q : V // q ≠ u}) (hC : IsBlock (deleteVertex G u) C)
    (z x r : {q : V // q ≠ u})
    (hzC : z ∈ C) (hxC : x ∈ C) (hrC : r ∈ C)
    (hzv : z.1 ≠ v) (hxv : x.1 ≠ v) (hrv : r.1 ≠ v)
    (hzx : z ≠ x) (hzr : z ≠ r)
    (hux : G.Adj u x.1)
    (hrdom : ∀ t : C, (⟨r, hrC⟩ : C) ≠ t →
      ((deleteVertex G u).induce C).Adj ⟨r, hrC⟩ t) :
    (G.induce {q : V | q ≠ z.1 ∧ q ≠ v}).Connected := by
  classical
  let K := deleteVertex G v
  let J := G.induce {q : V | q ≠ z.1 ∧ q ≠ v}
  let xJ : {q : V // q ≠ z.1 ∧ q ≠ v} :=
    ⟨x.1, fun h => hzx (Subtype.ext h.symm), hxv⟩
  let f : {q : V // q ≠ v} → {q : V // q ≠ z.1 ∧ q ≠ v} := fun q =>
    if hq : q.1 = z.1 then xJ else ⟨q.1, hq, q.2⟩
  have reach_x_to_block (b : {q : V // q ≠ u}) (hbC : b ∈ C)
      (hbz : b ≠ z) (hbv : b.1 ≠ v) :
      J.Reachable xJ ⟨b.1, fun h => hbz (Subtype.ext h), hbv⟩ := by
    let bJ : {q : V // q ≠ z.1 ∧ q ≠ v} :=
      ⟨b.1, fun h => hbz (Subtype.ext h), hbv⟩
    let rJ : {q : V // q ≠ z.1 ∧ q ≠ v} :=
      ⟨r.1, fun h => hzr (Subtype.ext h.symm), hrv⟩
    have hxrReach : J.Reachable xJ rJ := by
      by_cases hxr : x = r
      · have : xJ = rJ := Subtype.ext
          (congrArg (fun q : {q : V // q ≠ u} => q.1) hxr)
        exact this ▸ Reachable.refl xJ
      · have hrx := hrdom ⟨x, hxC⟩ (by
          intro h
          exact hxr (congrArg (fun q : C => q.1) h).symm)
        exact (show J.Adj xJ rJ from hrx.symm).reachable
    have hrbReach : J.Reachable rJ bJ := by
      by_cases hrb : r = b
      · have : rJ = bJ := Subtype.ext
          (congrArg (fun q : {q : V // q ≠ u} => q.1) hrb)
        exact this ▸ Reachable.refl rJ
      · have hrbAdj := hrdom ⟨b, hbC⟩ (by
          intro h
          have hEq : r = b := congrArg (fun q : C => q.val) h
          exact hrb hEq)
        exact (show J.Adj rJ bJ from hrbAdj).reachable
    simpa [bJ] using hxrReach.trans hrbReach
  have hf : ∀ a b : {q : V // q ≠ v}, K.Adj a b →
      J.Reachable (f a) (f b) := by
    intro a b hab
    by_cases haz : a.1 = z.1
    · have haEq : a.1 = z.1 := haz
      have hbz : b.1 ≠ z.1 := by intro h; exact hab.ne (Subtype.ext (haz.trans h.symm))
      by_cases hbu : b.1 = u
      · have hbEq : b = ⟨u, huv⟩ := Subtype.ext hbu
        subst b
        simp only [f, dif_pos haz, dif_neg hbz]
        exact (show J.Adj xJ ⟨u, z.2.symm, huv⟩ from hux.symm).reachable
      · let bH : {q : V // q ≠ u} := ⟨b.1, hbu⟩
        have hzAdj : (deleteVertex G u).Adj z bH := by
          change G.Adj z.1 bH.1
          change G.Adj a.1 b.1 at hab
          simpa [haEq, bH] using hab
        have hbC : bH ∈ C :=
          adj_mem_isBlock_of_uniqueCut (deleteVertex G u) ⟨v, huv.symm⟩
            hunique C hC hzC (by intro h; exact hzv (congrArg Subtype.val h)) hzAdj
        have hbzH : bH ≠ z := by intro h; exact hbz (congrArg Subtype.val h)
        simp only [f, dif_pos haz, dif_neg hbz]
        exact reach_x_to_block bH hbC hbzH b.2
    · by_cases hbz : b.1 = z.1
      · have hau : a.1 ≠ z.1 := haz
        by_cases hau' : a.1 = u
        · have haEq : a = ⟨u, huv⟩ := Subtype.ext hau'
          subst a
          simp only [f, dif_neg hau, dif_pos hbz]
          exact (show J.Adj ⟨u, z.2.symm, huv⟩ xJ from hux).reachable
        · let aH : {q : V // q ≠ u} := ⟨a.1, hau'⟩
          have haC : aH ∈ C :=
            adj_mem_isBlock_of_uniqueCut (deleteVertex G u) ⟨v, huv.symm⟩
              hunique C hC hzC (by intro h; exact hzv (congrArg Subtype.val h))
                (show (deleteVertex G u).Adj z aH by
                  change G.Adj z.1 aH.1
                  change G.Adj a.1 b.1 at hab
                  simpa [hbz, aH] using hab.symm)
          have hazH : aH ≠ z := by intro h; exact haz (congrArg Subtype.val h)
          simp only [f, dif_neg haz, dif_pos hbz]
          exact (reach_x_to_block aH haC hazH a.2).symm
      · simp only [f, dif_neg haz, dif_neg hbz]
        exact (show J.Adj ⟨a.1, haz, a.2⟩ ⟨b.1, hbz, b.2⟩ from hab).reachable
  have mapWalk {a b : {q : V // q ≠ v}} (p : K.Walk a b) :
      J.Reachable (f a) (f b) := by
    induction p with
    | nil => exact Reachable.refl _
    | @cons a b c hab p ih => exact (hf a b hab).trans ih
  change J.Connected
  rw [connected_iff_exists_forall_reachable]
  refine ⟨xJ, ?_⟩
  intro a
  let aK : {q : V // q ≠ v} := ⟨a.1, a.2.2⟩
  let xK : {q : V // q ≠ v} := ⟨x.1, hxv⟩
  obtain ⟨p⟩ := htwo.2.2 v aK xK
  have hr := mapWalk p
  have hfa : f aK = a := by
    apply Subtype.ext
    simp [f, aK, a.2.1]
  have hfx : f xK = xJ := by
    have hxz : x.1 ≠ z.1 := by
      intro h
      exact hzx (Subtype.ext h.symm)
    apply Subtype.ext
    simp [f, xK, xJ, hxz]
  exact (hfa ▸ hfx ▸ hr).symm

/-- Case 1 of the block analysis when the unique cut vertex itself
dominates the exceptional block.  Deleting `z` remains 2-connected: the
only delicate second deletion is the cut vertex, handled by the preceding
rerouting lemma.  A vertex in another block witnesses non-completeness. -/
theorem no_cut_and_local_dominator_in_block
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G)
    (u v : V) (huv : u ≠ v) (huvAdj : G.Adj u v)
    (h_deletions : ∀ x y : V, x ≠ y →
      closedNeighborhood G x ⊆ closedNeighborhood G y →
      IsomorphicToKn (deleteVertex G x) ∨
        ¬IsTwoConnected (deleteVertex G x))
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {q : V // q ≠ u}) (hC : IsBlock (deleteVertex G u) C)
    (z x r : {q : V // q ≠ u})
    (hzC : z ∈ C) (hxC : x ∈ C) (hrC : r ∈ C)
    (hzv : z.1 ≠ v) (hxv : x.1 ≠ v) (hrv : r.1 ≠ v)
    (hzx : z ≠ x) (hzr : z ≠ r)
    (hN : closedNeighborhood G z.1 ⊆ closedNeighborhood G v)
    (hux : G.Adj u x.1)
    (hrdom : ∀ t : C, (⟨r, hrC⟩ : C) ≠ t →
      ((deleteVertex G u).induce C).Adj ⟨r, hrC⟩ t) : False := by
  classical
  have hvz : v ≠ z.1 := hzv.symm
  have hdeleteTwo : IsTwoConnected (deleteVertex G z.1) := by
    have hcard : 3 ≤ Fintype.card {q : V // q ≠ z.1} := by
      let u' : {q : V // q ≠ z.1} := ⟨u, z.2.symm⟩
      let v' : {q : V // q ≠ z.1} := ⟨v, hvz⟩
      let x' : {q : V // q ≠ z.1} :=
        ⟨x.1, fun h => hzx (Subtype.ext h.symm)⟩
      have huv' : u' ≠ v' := by
        intro h
        exact huv (congrArg Subtype.val h)
      have hux' : u' ≠ x' := by
        intro h
        exact x.2 (congrArg Subtype.val h).symm
      have hvx' : v' ≠ x' := by
        intro h
        exact hxv (congrArg Subtype.val h).symm
      have hs : ({u', v', x'} : Finset {q : V // q ≠ z.1}) ⊆ Finset.univ :=
        Finset.subset_univ _
      have hc := Finset.card_le_card hs
      simpa [huv', hux', hvx'] using hc
    refine ⟨hcard, htwo.2.2 z.1, ?_⟩
    intro y
    by_cases hyv : y.1 = v
    · have hy : y = ⟨v, hvz⟩ := Subtype.ext hyv
      subst y
      have hsim := connected_avoiding_block_vertex_and_cut G htwo u v huv
        hunique C hC z x r hzC hxC hrC hzv hxv hrv hzx hzr hux hrdom
      exact (deleteTwoIso G z.1 v hvz).connected_iff.mpr hsim
    · exact delete_dominated_then_other_connected G htwo z.1 v y.1
        hzv (Ne.symm y.2) (Ne.symm hyv) hN
  let H := deleteVertex G u
  let vc : {q : V // q ≠ u} := ⟨v, huv.symm⟩
  obtain ⟨C₁, C₂, hC₁, hC₂, hC₁C₂, _, _⟩ :=
    exists_two_blocks_of_cutVertex H vc hunique.1
  obtain ⟨D, hD, hCD⟩ : ∃ D : Set {q : V // q ≠ u},
      IsBlock H D ∧ C ≠ D := by
    by_cases hCC₁ : C = C₁
    · exact ⟨C₂, hC₂, fun h => hC₁C₂ (hCC₁.symm.trans h)⟩
    · exact ⟨C₁, hC₁, hCC₁⟩
  obtain ⟨y, hyD, hyv, _⟩ :=
    exists_u_neighbor_in_block G htwo u v huv hunique D hD
  have hnxy : ¬H.Adj x y :=
    not_adj_of_mem_distinct_blocks H vc hunique C D hC hD hCD hxC hyD
      (by intro h; exact hxv (congrArg Subtype.val h))
      (by intro h; exact hyv (congrArg Subtype.val h))
  have hyz : y.1 ≠ z.1 := by
    intro h
    have hyEqz : y = z := Subtype.ext h
    have hzD : z ∈ D := by simpa [hyEqz] using hyD
    exact hCD (isBlock_eq_of_two_common H C D hC hD vc z
      (uniqueCut_mem_isBlock H vc hunique C hC)
      (uniqueCut_mem_isBlock H vc hunique D hD) hzC hzD
      (by intro h'; exact hzv (congrArg Subtype.val h').symm))
  have hxzBase : x.1 ≠ z.1 := by
    intro h
    exact hzx (Subtype.ext h.symm)
  have hxy : x.1 ≠ y.1 := by
    intro h
    have hEq : x = y := Subtype.ext h
    have hxD : x ∈ D := by simpa [hEq] using hyD
    exact hCD (isBlock_eq_of_two_common H C D hC hD vc x
      (uniqueCut_mem_isBlock H vc hunique C hC)
      (uniqueCut_mem_isBlock H vc hunique D hD) hxC hxD
      (by intro h'; exact hxv (congrArg Subtype.val h').symm))
  have hdeleteNoncomplete : ¬IsomorphicToKn (deleteVertex G z.1) := by
    intro hcomplete
    have hadj := adj_of_isomorphicToKn (deleteVertex G z.1) hcomplete
      (a := (⟨x.1, hxzBase⟩ : {q : V // q ≠ z.1}))
      (b := ⟨y.1, hyz⟩) (by
        intro h
        exact hxy (congrArg
          (fun q : {q : V // q ≠ z.1} => q.1) h))
    exact hnxy hadj
  rcases h_deletions z.1 v hzv hN with hcomplete | hnotTwo
  · exact hdeleteNoncomplete hcomplete
  · exact hnotTwo hdeleteTwo

/-- The deletion contradiction using the two-replacement rerouting lemma.
It differs from `no_global_and_local_dominator_in_block` only in the one
double deletion in which the global dominator is itself removed. -/
theorem no_global_with_block_replacements
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h_two_connected : IsTwoConnected G)
    (u v : V) (huv : u ≠ v) (huvAdj : G.Adj u v)
    (h_deletions : ∀ x y : V, x ≠ y →
      closedNeighborhood G x ⊆ closedNeighborhood G y →
      IsomorphicToKn (deleteVertex G x) ∨ ¬IsTwoConnected (deleteVertex G x))
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u}) (hC : IsBlock (deleteVertex G u) C)
    (z w rz rw : {x : V // x ≠ u})
    (hzC : z ∈ C) (hwC : w ∈ C) (hrzC : rz ∈ C) (hrwC : rw ∈ C)
    (hzv : z.1 ≠ v) (hwv : w.1 ≠ v) (hzw : z ≠ w)
    (hzrz : z ≠ rz) (hwrz : w ≠ rz) (hzrw : z ≠ rw) (hwrw : w ≠ rw)
    (hN : closedNeighborhood G z.1 ⊆ closedNeighborhood G w.1)
    (hzmap : ∀ t : C,
      ((deleteVertex G u).induce C).Adj ⟨z, hzC⟩ t →
        rz = t.1 ∨ ((deleteVertex G u).induce C).Adj ⟨rz, hrzC⟩ t)
    (hwmap : ∀ t : C,
      ((deleteVertex G u).induce C).Adj ⟨w, hwC⟩ t →
        rw = t.1 ∨ ((deleteVertex G u).induce C).Adj ⟨rw, hrwC⟩ t)
    (hcross : rz = rw ∨ (deleteVertex G u).Adj rz rw) : False := by
  classical
  have hzwBase : w.1 ≠ z.1 := by intro h; exact hzw (Subtype.ext h.symm)
  have hdeleteTwo : IsTwoConnected (deleteVertex G z.1) := by
    have hcard : 3 ≤ Fintype.card {x : V // x ≠ z.1} := by
      let u' : {x : V // x ≠ z.1} := ⟨u, z.2.symm⟩
      let w' : {x : V // x ≠ z.1} := ⟨w.1, hzwBase⟩
      let r' : {x : V // x ≠ z.1} :=
        ⟨rz.1, by intro h; exact hzrz (Subtype.ext h.symm)⟩
      have huw' : u' ≠ w' := by
        intro h; exact w.2 (congrArg Subtype.val h).symm
      have hur' : u' ≠ r' := by
        intro h; exact rz.2 (congrArg Subtype.val h).symm
      have hwr' : w' ≠ r' := by
        intro h
        exact hwrz (Subtype.ext
          (congrArg (fun q : {x : V // x ≠ z.1} => q.1) h))
      have hsub : ({u', w', r'} : Finset {x : V // x ≠ z.1}) ⊆ Finset.univ :=
        Finset.subset_univ _
      have hc := Finset.card_le_card hsub
      simpa [huw', hur', hwr'] using hc
    refine ⟨hcard, h_two_connected.2.2 z.1, ?_⟩
    intro y
    by_cases hyw : y.1 = w.1
    · have hy : y = ⟨w.1, hzwBase⟩ := Subtype.ext hyw
      subst y
      have hsim := connected_avoiding_two_of_block_replacements G u v huv
        huvAdj hunique C hC z w rz rw hzC hwC hrzC hrwC hzv hwv hzw
          hzrz hwrz hzrw hwrw hzmap hwmap hcross
      exact (deleteTwoIso G z.1 w.1 hzwBase).connected_iff.mpr hsim
    · exact delete_dominated_then_other_connected G h_two_connected
        z.1 w.1 y.1 (fun h => hzw (Subtype.ext h))
        (Ne.symm y.2) (Ne.symm hyw) hN
  let H := deleteVertex G u
  let vc : {x : V // x ≠ u} := ⟨v, huv.symm⟩
  obtain ⟨C₁, C₂, hC₁, hC₂, hC₁C₂, _, _⟩ :=
    exists_two_blocks_of_cutVertex H vc hunique.1
  obtain ⟨D, hD, hCD⟩ : ∃ D : Set {x : V // x ≠ u},
      IsBlock H D ∧ C ≠ D := by
    by_cases hCC₁ : C = C₁
    · exact ⟨C₂, hC₂, fun h => hC₁C₂ (hCC₁.symm.trans h)⟩
    · exact ⟨C₁, hC₁, hCC₁⟩
  obtain ⟨y, hyD, hyv, _⟩ :=
    exists_u_neighbor_in_block G h_two_connected u v huv hunique D hD
  have hwy : ¬H.Adj w y :=
    not_adj_of_mem_distinct_blocks H vc hunique C D hC hD hCD hwC hyD
      (by intro h; exact hwv (congrArg Subtype.val h))
      (by intro h; exact hyv (congrArg Subtype.val h))
  have hyz : y.1 ≠ z.1 := by
    intro h
    have hyEqz : y = z := Subtype.ext h
    have hzD : z ∈ D := by simpa [hyEqz] using hyD
    exact hCD (isBlock_eq_of_two_common H C D hC hD vc z
      (uniqueCut_mem_isBlock H vc hunique C hC)
      (uniqueCut_mem_isBlock H vc hunique D hD) hzC hzD
      (by intro h; exact hzv (congrArg Subtype.val h).symm))
  have hdeleteNoncomplete : ¬IsomorphicToKn (deleteVertex G z.1) := by
    intro hcomplete
    have hadj := adj_of_isomorphicToKn (deleteVertex G z.1) hcomplete
      (a := (⟨w.1, hzwBase⟩ : {x : V // x ≠ z.1}))
      (b := ⟨y.1, hyz⟩) (by
        intro h
        have hval : w.1 = y.1 :=
          congrArg (fun q : {x : V // x ≠ z.1} => q.1) h
        have hwyEq : w = y := Subtype.ext hval
        subst y
        exact hCD (isBlock_eq_of_two_common H C D hC hD vc w
          (uniqueCut_mem_isBlock H vc hunique C hC)
          (uniqueCut_mem_isBlock H vc hunique D hD) hwC hyD
          (by intro hvc; exact hwv (congrArg Subtype.val hvc).symm)))
    exact hwy hadj
  rcases h_deletions z.1 w.1 (fun h => hzw (Subtype.ext h)) hN with
    hcomplete | hnotTwo
  · exact hdeleteNoncomplete hcomplete
  · exact hnotTwo hdeleteTwo

/-- One global domination relation is enough for the deletion contradiction
when a second block-dominating vertex remains available to reroute the sole
exceptional double deletion. -/
theorem no_global_and_local_dominator_in_block
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h_two_connected : IsTwoConnected G)
    (u v : V) (huv : u ≠ v) (huvAdj : G.Adj u v)
    (h_deletions : ∀ x y : V, x ≠ y →
      closedNeighborhood G x ⊆ closedNeighborhood G y →
      IsomorphicToKn (deleteVertex G x) ∨
        ¬IsTwoConnected (deleteVertex G x))
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u}) (hC : IsBlock (deleteVertex G u) C)
    (z w r : {x : V // x ≠ u})
    (hzC : z ∈ C) (hwC : w ∈ C) (hrC : r ∈ C)
    (hzv : z.1 ≠ v) (hwv : w.1 ≠ v)
    (hzw : z ≠ w) (hzr : z ≠ r) (hwr : w ≠ r)
    (hN : closedNeighborhood G z.1 ⊆ closedNeighborhood G w.1)
    (hrdom : ∀ t : C, (⟨r, hrC⟩ : C) ≠ t →
      ((deleteVertex G u).induce C).Adj ⟨r, hrC⟩ t) : False := by
  classical
  have hzwBase : w.1 ≠ z.1 := by
    intro h
    exact hzw (Subtype.ext h.symm)
  have hdeleteTwo : IsTwoConnected (deleteVertex G z.1) := by
    have hcard : 3 ≤ Fintype.card {x : V // x ≠ z.1} := by
      let u' : {x : V // x ≠ z.1} := ⟨u, z.2.symm⟩
      let w' : {x : V // x ≠ z.1} := ⟨w.1, hzwBase⟩
      let r' : {x : V // x ≠ z.1} := ⟨r.1, by
        intro h; exact hzr (Subtype.ext h.symm)⟩
      have huw' : u' ≠ w' := by
        intro h; exact w.2 (congrArg Subtype.val h).symm
      have hur' : u' ≠ r' := by
        intro h; exact r.2 (congrArg Subtype.val h).symm
      have hwr' : w' ≠ r' := by
        intro h
        have hval : w.1 = r.1 :=
          congrArg (fun t : {x : V // x ≠ z.1} => t.1) h
        exact hwr (Subtype.ext hval)
      have hsub : ({u', w', r'} : Finset {x : V // x ≠ z.1}) ⊆
          Finset.univ := Finset.subset_univ _
      have hc := Finset.card_le_card hsub
      simpa [huw', hur', hwr'] using hc
    refine ⟨hcard, h_two_connected.2.2 z.1, ?_⟩
    intro y
    by_cases hyw : y.1 = w.1
    · have hy : y = ⟨w.1, hzwBase⟩ := Subtype.ext hyw
      subst y
      have hsim := connected_avoiding_two_of_block_dominator G u v huv
        huvAdj hunique C hC z w r hzC hwC hrC hzv hwv hzw hzr hwr hrdom
      exact (deleteTwoIso G z.1 w.1 hzwBase).connected_iff.mpr hsim
    · exact delete_dominated_then_other_connected G h_two_connected
        z.1 w.1 y.1 (fun h => hzw (Subtype.ext h))
        (Ne.symm y.2) (Ne.symm hyw) hN
  let H := deleteVertex G u
  let vc : {x : V // x ≠ u} := ⟨v, huv.symm⟩
  have hcut : IsCutVertex H vc := hunique.1
  obtain ⟨C₁, C₂, hC₁, hC₂, hC₁C₂, _, _⟩ :=
    exists_two_blocks_of_cutVertex H vc hcut
  obtain ⟨D, hD, hCD⟩ : ∃ D : Set {x : V // x ≠ u},
      IsBlock H D ∧ C ≠ D := by
    by_cases hCC₁ : C = C₁
    · exact ⟨C₂, hC₂, fun h => hC₁C₂ (hCC₁.symm.trans h)⟩
    · exact ⟨C₁, hC₁, hCC₁⟩
  obtain ⟨y, hyD, hyv, _⟩ :=
    exists_u_neighbor_in_block G h_two_connected u v huv hunique D hD
  have hwy : ¬H.Adj w y :=
    not_adj_of_mem_distinct_blocks H vc hunique C D hC hD hCD
      hwC hyD (by
        intro h
        exact hwv (congrArg Subtype.val h)) (by
        intro h
        exact hyv (congrArg Subtype.val h))
  have hyz : y.1 ≠ z.1 := by
    intro h
    have hyEqz : y = z := Subtype.ext h
    have hzD : z ∈ D := by simpa [hyEqz] using hyD
    exact hCD (isBlock_eq_of_two_common H C D hC hD vc z
      (uniqueCut_mem_isBlock H vc hunique C hC)
      (uniqueCut_mem_isBlock H vc hunique D hD) hzC hzD
      (by intro h; exact hzv (congrArg Subtype.val h).symm))
  have hdeleteNoncomplete : ¬IsomorphicToKn (deleteVertex G z.1) := by
    intro hcomplete
    have hadj := adj_of_isomorphicToKn (deleteVertex G z.1) hcomplete
      (a := (⟨w.1, hzwBase⟩ : {x : V // x ≠ z.1}))
      (b := ⟨y.1, hyz⟩) (by
        intro h
        have hval : w.1 = y.1 :=
          congrArg (fun t : {x : V // x ≠ z.1} => t.1) h
        have : w = y := Subtype.ext hval
        subst y
        exact hCD (isBlock_eq_of_two_common H C D hC hD vc w
          (uniqueCut_mem_isBlock H vc hunique C hC)
          (uniqueCut_mem_isBlock H vc hunique D hD) hwC hyD
          (by intro hvc; exact hwv (congrArg Subtype.val hvc).symm)))
    exact hwy hadj
  rcases h_deletions z.1 w.1 (fun h => hzw (Subtype.ext h)) hN with
    hcomplete | hnotTwo
  · exact hdeleteNoncomplete hcomplete
  · exact hnotTwo hdeleteTwo

/-- The repeated contradiction in the block part of BKLPS Lemma 9.
If a non-cut vertex of one block is dominated by two distinct vertices of
that block, then its deletion is 2-connected.  A vertex in a second block
shows that the deletion is not complete, contradicting the terminal
deletion hypothesis. -/
theorem no_two_global_dominators_in_block
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h_two_connected : IsTwoConnected G)
    (u v : V) (huv : u ≠ v)
    (h_deletions : ∀ x y : V, x ≠ y →
      closedNeighborhood G x ⊆ closedNeighborhood G y →
      IsomorphicToKn (deleteVertex G x) ∨
        ¬IsTwoConnected (deleteVertex G x))
    (hunique : IsUniqueCutVertex (deleteVertex G u) ⟨v, huv.symm⟩)
    (C : Set {x : V // x ≠ u}) (hC : IsBlock (deleteVertex G u) C)
    (z w₁ w₂ : {x : V // x ≠ u})
    (hzC : z ∈ C) (hw₁C : w₁ ∈ C) (hw₂C : w₂ ∈ C)
    (hzv : z.1 ≠ v) (hzw₁ : z ≠ w₁) (hzw₂ : z ≠ w₂)
    (hw₁w₂ : w₁ ≠ w₂)
    (hN₁ : closedNeighborhood G z.1 ⊆ closedNeighborhood G w₁.1)
    (hN₂ : closedNeighborhood G z.1 ⊆ closedNeighborhood G w₂.1) : False := by
  classical
  let H := deleteVertex G u
  let vc : {x : V // x ≠ u} := ⟨v, huv.symm⟩
  have hcut : IsCutVertex H vc := hunique.1
  obtain ⟨C₁, C₂, hC₁, hC₂, hC₁C₂, hvcC₁, hvcC₂⟩ :=
    exists_two_blocks_of_cutVertex H vc hcut
  obtain ⟨D, hD, hCD⟩ : ∃ D : Set {x : V // x ≠ u},
      IsBlock H D ∧ C ≠ D := by
    by_cases hCC₁ : C = C₁
    · exact ⟨C₂, hC₂, fun h => hC₁C₂ (hCC₁.symm.trans h)⟩
    · exact ⟨C₁, hC₁, hCC₁⟩
  obtain ⟨y, hyD, hyv, huy⟩ :=
    exists_u_neighbor_in_block G h_two_connected u v huv hunique D hD
  let w : {x : V // x ≠ u} := if w₁.1 = v then w₂ else w₁
  have hwC : w ∈ C := by
    by_cases h : w₁.1 = v <;> simp [w, h, hw₁C, hw₂C]
  have hwv : w.1 ≠ v := by
    by_cases h : w₁.1 = v
    · simp only [w, if_pos h]
      intro hw₂v
      apply hw₁w₂
      apply Subtype.ext
      exact h.trans hw₂v.symm
    · simpa [w, h]
  have hwz : w.1 ≠ z.1 := by
    by_cases h : w₁.1 = v
    · simp only [w, if_pos h]
      intro heq
      apply hzw₂
      apply Subtype.ext
      exact heq.symm
    · simp only [w, if_neg h]
      intro heq
      apply hzw₁
      apply Subtype.ext
      exact heq.symm
  have hwy : w ≠ y := by
    intro h
    apply hCD
    apply isBlock_eq_of_two_common H C D hC hD vc w
    · exact uniqueCut_mem_isBlock H vc hunique C hC
    · exact uniqueCut_mem_isBlock H vc hunique D hD
    · exact hwC
    · simpa [h] using hyD
    · intro heq
      exact hwv (congrArg Subtype.val heq).symm
  have hnwy : ¬H.Adj w y :=
    not_adj_of_mem_distinct_blocks H vc hunique C D hC hD hCD
      hwC hyD (by
        intro h
        exact hwv (congrArg Subtype.val h)) (by
        intro h
        exact hyv (congrArg Subtype.val h))
  have hdeleteTwo : IsTwoConnected (deleteVertex G z.1) := by
    apply delete_two_dominated_twoConnected G h_two_connected z.1 w₁.1 w₂.1 u
    · intro h; exact hzw₁ (Subtype.ext h)
    · intro h; exact hzw₂ (Subtype.ext h)
    · intro h; exact hw₁w₂ (Subtype.ext h)
    · exact z.2.symm
    · exact w₁.2.symm
    · exact w₂.2.symm
    · exact hN₁
    · exact hN₂
  have hyz : y.1 ≠ z.1 := by
    intro h
    apply hCD
    apply isBlock_eq_of_two_common H C D hC hD vc z
    · exact uniqueCut_mem_isBlock H vc hunique C hC
    · exact uniqueCut_mem_isBlock H vc hunique D hD
    · exact hzC
    · have hyz' : y = z := Subtype.ext h
      simpa [hyz'] using hyD
    · intro heq
      exact hzv (congrArg Subtype.val heq).symm
  have hdeleteNoncomplete : ¬IsomorphicToKn (deleteVertex G z.1) := by
    intro hcomplete
    have hadj := adj_of_isomorphicToKn (deleteVertex G z.1) hcomplete
      (a := (⟨w.1, hwz⟩ : {x : V // x ≠ z.1}))
      (b := ⟨y.1, hyz⟩) (by
        intro h
        have hval : w.1 = y.1 :=
          congrArg (fun t : {x : V // x ≠ z.1} => t.1) h
        exact hwy (Subtype.ext hval))
    exact hnwy hadj
  rcases h_deletions z.1 w₁.1
      (fun h => hzw₁ (Subtype.ext h)) hN₁ with hcomplete | hnotTwo
  · exact hdeleteNoncomplete hcomplete
  · exact hnotTwo hdeleteTwo

end

end BKLPS.External
