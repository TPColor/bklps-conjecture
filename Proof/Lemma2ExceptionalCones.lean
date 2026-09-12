import Proof.ExternalResults.AdjoinVertex
import Proof.ExternalResults.GraphIsomorphismInvariants

/-!
Relabeling the extremal attachment patterns in Exceptional Deletion.

Suppose `G-u ≃g K_m^2`.  Extend this labeling by sending `u` to the last
vertex.  If `u` is adjacent precisely to the nonzero canonical vertices,
then the old degree-two vertex keeps exactly its two clique neighbors and
the old clique together with `u` becomes a clique.  An edge-by-edge check
therefore identifies `G` with `K_(m+1)^2`.

For the complementary cone `K_m^(m-2)=K_m-e`, the same extended labeling
shows that either of the attachment patterns surviving the numerical part
of Lemma 2 makes `G` complete or another exceptional cone.  In each proof,
edges with neither endpoint `u` are handled by the deletion isomorphism;
edges incident with `u` reduce exactly to the attachment hypothesis.  The
contradiction with `IsUnexceptional G` is what rules out equality in the
delicate terminal subcases of Lemma 2.
-/

namespace BKLPS

open SimpleGraph
open External

noncomputable section

universe u

/-- If deleting `u` gives `K_m^2` and `u` is adjacent to exactly the
nonzero canonical vertices, adjoining `u` simply enlarges the old clique.
Thus the resulting graph is `K_(m+1)^2`. -/
theorem isExceptional_of_delete_low_attachment
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (m : ℕ) (hm : 3 ≤ m)
    (hcard : Fintype.card V = m + 1)
    (e : deleteVertex G u ≃g Knt m 2)
    (hattach : ∀ x : V, (hx : x ≠ u) →
      (G.Adj u x ↔ (e ⟨x, hx⟩).val ≠ 0)) :
    IsExceptional G := by
  letI : NeZero m := ⟨by omega⟩
  let E : V ≃ Fin (m + 1) := adjoinDeletedEquiv u e.toEquiv
  right
  left
  unfold IsomorphicToKnt
  rw [hcard]
  refine ⟨{ toEquiv := E, map_rel_iff' := ?_ }⟩
  intro x y
  by_cases hxu : x = u
  · subst x
    by_cases hyu : y = u
    · subst y
      simp
    · rw [show E u = Fin.last m by
          exact adjoinDeletedEquiv_apply_self u e.toEquiv,
        show E y = Fin.castSucc (e ⟨y, hyu⟩) by
          exact adjoinDeletedEquiv_apply_ne u y hyu e.toEquiv]
      rw [hattach y hyu]
      have hlastNe : Fin.last m ≠ Fin.castSucc (e ⟨y, hyu⟩) := by
        intro h
        have hv := congrArg Fin.val h
        simp [Fin.last] at hv
        omega
      have hm0 : m ≠ 0 := by omega
      have hm2 : ¬m ≤ 2 := by omega
      simp only [Knt, hlastNe, true_and, Fin.val_last, Fin.val_castSucc,
        hm0, not_false_eq_true, hm2, and_false, or_false]
      simp [hlastNe, hm0]
  · by_cases hyu : y = u
    · subst y
      rw [show E u = Fin.last m by
          exact adjoinDeletedEquiv_apply_self u e.toEquiv,
        show E x = Fin.castSucc (e ⟨x, hxu⟩) by
          exact adjoinDeletedEquiv_apply_ne u x hxu e.toEquiv]
      rw [G.adj_comm, hattach x hxu]
      have hcastNe : Fin.castSucc (e ⟨x, hxu⟩) ≠ Fin.last m := by
        intro h
        have hv := congrArg Fin.val h
        simp [Fin.last] at hv
        omega
      have hm0 : m ≠ 0 := by omega
      have hm2 : ¬m ≤ 2 := by omega
      simp only [Knt, hcastNe, true_and, Fin.val_last, Fin.val_castSucc,
        hm0, not_false_eq_true, hm2, and_false, or_false]
      simp [hcastNe, hm0]
    · rw [show E x = Fin.castSucc (e ⟨x, hxu⟩) by
          exact adjoinDeletedEquiv_apply_ne u x hxu e.toEquiv,
        show E y = Fin.castSucc (e ⟨y, hyu⟩) by
          exact adjoinDeletedEquiv_apply_ne u y hyu e.toEquiv]
      have hcast :
          (Knt (m + 1) 2).Adj (Fin.castSucc (e ⟨x, hxu⟩))
              (Fin.castSucc (e ⟨y, hyu⟩)) ↔
            (Knt m 2).Adj (e ⟨x, hxu⟩) (e ⟨y, hyu⟩) := by
        simp only [Knt, Fin.castSucc_inj, Fin.val_castSucc]
        constructor
        · rintro ⟨hne, hrest⟩
          exact ⟨fun h => hne (congrArg Fin.castSucc h), hrest⟩
        · rintro ⟨hne, hrest⟩
          exact ⟨fun h => hne ((Fin.castSucc_injective m) h), hrest⟩
      rw [hcast]
      simpa [deleteVertex] using e.map_rel_iff

private theorem highAdjRelabel (m : ℕ) (hm : 3 ≤ m)
    (c : Fin m) (hc : c.val = m - 1) (x y : Fin m) :
    (Knt (m + 1) (m - 1)).Adj
        (if x = c then Fin.last m else Fin.castSucc x)
        (if y = c then Fin.last m else Fin.castSucc y) ↔
      (Knt m (m - 2)).Adj x y := by
  letI : NeZero m := ⟨by omega⟩
  have hc0 : c ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [hc] at hv
    omega
  have hbound (z : Fin m) (hz : z ≠ c) : z.val ≤ m - 2 := by
    have hlt := z.isLt
    by_contra h
    have hzval : z.val = m - 1 := by omega
    apply hz
    apply Fin.ext
    omega
  by_cases hx : x = c
  · subst x
    by_cases hy : y = c
    · subst y
      simp
    · have hyb := hbound y hy
      by_cases hy0 : y = 0
      · subst y
        simp [Knt, hc, hc0, Fin.last]
        omega
      · have hlastY : Fin.last m ≠ Fin.castSucc y := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
          omega
        have hcy : c ≠ y := Ne.symm hy
        have hm0 : m ≠ 0 := by omega
        simp [Knt, hc, hc0, hy, hcy, hy0, Fin.last, hyb,
          hlastY, hm0]
        simpa [Fin.last] using hlastY
  · have hxb := hbound x hx
    by_cases hy : y = c
    · subst y
      by_cases hx0 : x = 0
      · subst x
        simp [Knt, hc, hc0, Fin.last]
        omega
      · have hcastXLast : Fin.castSucc x ≠ Fin.last m := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
          omega
        have hcx : c ≠ x := Ne.symm hx
        have hm0 : m ≠ 0 := by omega
        simp [Knt, hc, hc0, hx, hcx, hx0, Fin.last, hxb,
          hcastXLast, hm0]
        simpa [Fin.last] using hcastXLast
    · have hyb := hbound y hy
      by_cases hx0 : x = 0
      · subst x
        by_cases hy0 : y = 0
        · subst y; simp
        · have hzeroCast : (0 : Fin (m + 1)) ≠ Fin.castSucc y := by
            intro h
            apply hy0
            apply Fin.ext
            simpa using congrArg Fin.val h.symm
          simp [Knt, hx, hy, hy0, hyb, hzeroCast]
          exact ⟨fun _ => Ne.symm hy0, fun _ => by omega⟩
      · by_cases hy0 : y = 0
        · subst y
          have hxTop : x.val ≤ m - 1 := by omega
          simp [Knt, hx, hy, hx0, hxb, hxTop]
        · simp [Knt, hx, hy, hx0, hy0, hxb, hyb]

/-- Adding a universal vertex to `K_m^(m-2)` produces
`K_(m+1)^(m-1)`. -/
theorem isExceptional_of_delete_high_dominating
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (m : ℕ) (hm : 3 ≤ m)
    (hcard : Fintype.card V = m + 1)
    (hdom : ∀ x : V, x ≠ u → G.Adj u x)
    (hdelete : Nonempty (deleteVertex G u ≃g Knt m (m - 2))) :
    IsExceptional G := by
  rcases hdelete with ⟨e⟩
  let base : V ≃ Fin (m + 1) := adjoinDeletedEquiv u e.toEquiv
  let c : Fin m := ⟨m - 1, by omega⟩
  let a : Fin (m + 1) := Fin.castSucc c
  let b : Fin (m + 1) := Fin.last m
  let p : Equiv.Perm (Fin (m + 1)) := Equiv.swap a b
  let E : V ≃ Fin (m + 1) := base.trans p
  have ha0 : a ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [a, c] at this
    omega
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b, c] at this
    omega
  have hEself : E u = a := by
    simp only [E, base, p, Equiv.trans_apply,
      adjoinDeletedEquiv_apply_self]
    exact Equiv.swap_apply_right a b
  have hEold (x : V) (hx : x ≠ u) :
      E x = if e ⟨x, hx⟩ = c then b
        else Fin.castSucc (e ⟨x, hx⟩) := by
    simp only [E, base, p, Equiv.trans_apply,
      adjoinDeletedEquiv_apply_ne u x hx e.toEquiv]
    change (Equiv.swap a b) (Fin.castSucc (e ⟨x, hx⟩)) = _
    by_cases hlast : e ⟨x, hx⟩ = c
    · have heq : Fin.castSucc (e ⟨x, hx⟩) = a := by simp [hlast, a]
      rw [heq, Equiv.swap_apply_left]
      simp [hlast]
    · have hcastNeA : Fin.castSucc (e ⟨x, hx⟩) ≠ a := by
        intro h
        apply hlast
        apply Fin.ext
        have hv := congrArg Fin.val h
        simpa [a, c] using hv
      have hcastNeB : Fin.castSucc (e ⟨x, hx⟩) ≠ b := by
        intro h
        have hv := congrArg Fin.val h
        simp [b] at hv
        omega
      rw [Equiv.swap_apply_of_ne_of_ne hcastNeA hcastNeB]
      simp [hlast]
  right
  right
  unfold IsomorphicToKnt
  rw [hcard]
  have hparam : m + 1 - 2 = m - 1 := by omega
  rw [hparam]
  refine ⟨{ toEquiv := E, map_rel_iff' := ?_ }⟩
  intro x y
  by_cases hxu : x = u
  · subst x
    by_cases hyu : y = u
    · subst y
      simp
    · have hEy := hEold y hyu
      rw [hEself, hEy]
      have hay : (if e ⟨y, hyu⟩ = c then b
          else Fin.castSucc (e ⟨y, hyu⟩)) ≠ a := by
        split_ifs with h
        · exact hab.symm
        · intro heq
          apply h
          apply Fin.ext
          have hv := congrArg Fin.val heq
          simpa [a] using hv
      constructor
      · intro _
        exact hdom y hyu
      · intro _
        change a ≠ (if e ⟨y, hyu⟩ = c then b else
            Fin.castSucc (e ⟨y, hyu⟩)) ∧ _
        refine ⟨hay.symm, ?_⟩
        let q : Fin (m + 1) := if e ⟨y, hyu⟩ = c then b
          else Fin.castSucc (e ⟨y, hyu⟩)
        by_cases hq0 : q.val = 0
        · right; right
          exact ⟨by simpa [q] using hq0, by simp [a, c]⟩
        · left
          exact ⟨fun h => ha0 (Fin.ext h), hq0⟩
  · by_cases hyu : y = u
    · subst y
      have hEx := hEold x hxu
      rw [hEself, hEx]
      have hxa : (if e ⟨x, hxu⟩ = c then b
          else Fin.castSucc (e ⟨x, hxu⟩)) ≠ a := by
        split_ifs with h
        · exact hab.symm
        · intro heq
          apply h
          apply Fin.ext
          have hv := congrArg Fin.val heq
          simpa [a] using hv
      constructor
      · intro _
        exact (hdom x hxu).symm
      · intro _
        change (if e ⟨x, hxu⟩ = c then b else
            Fin.castSucc (e ⟨x, hxu⟩)) ≠ a ∧ _
        refine ⟨hxa, ?_⟩
        let q : Fin (m + 1) := if e ⟨x, hxu⟩ = c then b
          else Fin.castSucc (e ⟨x, hxu⟩)
        by_cases hq0 : q.val = 0
        · right; left
          exact ⟨by simpa [q] using hq0, by simp [a, c]⟩
        · left
          exact ⟨hq0, fun h => ha0 (Fin.ext h)⟩
    · have hEx := hEold x hxu
      have hEy := hEold y hyu
      rw [hEx, hEy]
      have hold :
          (Knt m (m - 2)).Adj (e ⟨x, hxu⟩) (e ⟨y, hyu⟩) ↔
            (deleteVertex G u).Adj ⟨x, hxu⟩ ⟨y, hyu⟩ :=
        e.map_rel_iff
      change _ ↔ (deleteVertex G u).Adj ⟨x, hxu⟩ ⟨y, hyu⟩
      rw [← hold]
      exact highAdjRelabel m hm c rfl (e ⟨x, hxu⟩) (e ⟨y, hyu⟩)

end

end BKLPS
