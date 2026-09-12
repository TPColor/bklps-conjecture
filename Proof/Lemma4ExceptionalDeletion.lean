import Proof.ExternalResults.GraphIsomorphismInvariants
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Fin.Basic

/-!
Deleting a vertex from each BKLPS exceptional family.

For a complete graph, `Fin.succAbove` gives an explicit relabeling of the
remaining vertices and the deletion is again complete.  For `K_n^t`, the
proof first treats deletion of the distinguished vertex `0`, which leaves a
clique.  Deleting a clique vertex instead relabels the remaining graph as a
smaller cone; depending on whether the deleted vertex belonged to the
special neighborhood, its parameter is `t` or `t-1`.

These canonical calculations are transported across an arbitrary graph
isomorphism using `deleteVertexIso`.  The resulting theorem used in Lemma 4
says: if a graph of order at least six is exceptional and a 2-connected
one-vertex deletion is unexceptional, a contradiction follows.  Indeed,
the complete family always deletes to a complete graph, while in either
cone family 2-connectivity excludes the parameter endpoints that could
otherwise evade the smaller exceptional families.  Thus an exceptional
block extension cannot have the unexceptional block as its deletion.
-/

namespace BKLPS

open SimpleGraph
open External

noncomputable section

universe u

variable {W : Type u} [Fintype W] [DecidableEq W]

/-- Deleting any vertex from a complete graph leaves a complete graph. -/
def deleteCompleteIso (n : ℕ) (a : Fin (n + 1)) :
    deleteVertex (completeGraph (Fin (n + 1))) a ≃g completeGraph (Fin n) where
  toEquiv := (finSuccAboveEquiv a).symm
  map_rel_iff' := by
    intro x y
    change ((finSuccAboveEquiv a).symm x ≠ (finSuccAboveEquiv a).symm y) ↔ x.1 ≠ y.1
    constructor
    · intro hxy hval
      exact hxy (congrArg _ (Subtype.ext hval))
    · intro hxy h
      exact hxy (congrArg Subtype.val ((finSuccAboveEquiv a).symm.injective h))

/-- A nonempty complete graph remains exceptional after any one-vertex
deletion. -/
theorem deleteComplete_isExceptional (m : ℕ) (hm : 1 ≤ m) (a : Fin m) :
    IsExceptional (deleteVertex (completeGraph (Fin m)) a) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hcard : Fintype.card {x : Fin (n + 1) // x ≠ a} = n := by simp
  left
  unfold IsomorphicToKn
  rw [hcard]
  exact ⟨deleteCompleteIso n a⟩

/-- Deleting the distinguished vertex `0` from `K_(n+1)^t` leaves `K_n`. -/
def deleteKntZeroIso (n t : ℕ) :
    deleteVertex (Knt (n + 1) t) (0 : Fin (n + 1)) ≃g
      completeGraph (Fin n) where
  toEquiv := (finSuccAboveEquiv (0 : Fin (n + 1))).symm
  map_rel_iff' := by
    intro a b
    change ((finSuccAboveEquiv (0 : Fin (n + 1))).symm a ≠
        (finSuccAboveEquiv (0 : Fin (n + 1))).symm b) ↔
      (a.1 ≠ b.1 ∧
        ((a.1.val ≠ 0 ∧ b.1.val ≠ 0) ∨
         (a.1.val = 0 ∧ b.1.val ≤ t) ∨
         (b.1.val = 0 ∧ a.1.val ≤ t)))
    constructor
    · intro hab
      refine ⟨?_, Or.inl ⟨(fun h => a.2 (Fin.ext h)),
        (fun h => b.2 (Fin.ext h))⟩⟩
      intro h
      exact hab (congrArg _ (Subtype.ext h))
    · rintro ⟨hab, _⟩ h
      have habSub : a = b :=
        (finSuccAboveEquiv (0 : Fin (n + 1))).symm.injective h
      exact hab (congrArg Subtype.val habSub)

/-- Deleting an old nonneighbor of `0` from `K_(n+1)^2` leaves `K_n^2`. -/
def deleteKntTwoFarIso (n : ℕ) (a : Fin (n + 1)) (ha : 2 < a.val) :
    deleteVertex (Knt (n + 1) 2) a ≃g Knt n 2 := by
  letI : NeZero n := ⟨by omega⟩
  let e : Fin n ≃ {x : Fin (n + 1) // x ≠ a} := finSuccAboveEquiv a
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    simp at ha
  have he0 : (e (0 : Fin n)).1 = (0 : Fin (n + 1)) := by
    simpa [e, finSuccAboveEquiv] using Fin.succAbove_ne_zero_zero ha0
  have hzero (i : Fin n) : (e i).1.val = 0 ↔ i.val = 0 := by
    constructor
    · intro h
      have hei : e i = e (0 : Fin n) := by
        apply Subtype.ext
        apply Fin.ext
        simpa [he0] using h
      exact congrArg Fin.val (e.injective hei)
    · intro h
      have hi : i = 0 := Fin.ext h
      subst i
      exact congrArg Fin.val he0
  have hnezero (i : Fin n) : (e i).1.val ≠ 0 ↔ i.val ≠ 0 :=
    not_congr (hzero i)
  let two : Fin n := ⟨2, by omega⟩
  have heTwo : (e two).1.val = 2 := by
    change (a.succAbove two).val = 2
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · exact ha
  have hbound (i : Fin n) : (e i).1.val ≤ 2 ↔ i.val ≤ 2 := by
    constructor
    · intro h
      have hs : a.succAbove i ≤ a.succAbove two := by
        change (a.succAbove i).val ≤ (a.succAbove two).val
        rw [show (a.succAbove two).val = 2 by exact heTwo]
        exact h
      have hit : i ≤ two := (a.succAboveOrderEmb.le_iff_le).mp hs
      exact hit
    · intro h
      have hit : i ≤ two := h
      have hs := a.succAboveOrderEmb.monotone hit
      change (a.succAbove i).val ≤ 2
      rw [← show (a.succAbove two).val = 2 by exact heTwo]
      exact hs
  have hne (i j : Fin n) : (e i).1 ≠ (e j).1 ↔ i ≠ j := by
    constructor
    · intro h hij
      exact h (congrArg Subtype.val (congrArg e hij))
    · intro hij h
      exact hij (e.injective (Subtype.ext h))
  exact
    { toEquiv := e.symm
      map_rel_iff' := by
        intro x y
        obtain ⟨i, rfl⟩ := e.surjective x
        obtain ⟨j, rfl⟩ := e.surjective y
        simp only [e.symm_apply_apply]
        change (Knt n 2).Adj i j ↔
          (Knt (n + 1) 2).Adj (e i).1 (e j).1
        simp only [Knt]
        rw [hne]
        rw [hnezero, hnezero, hzero, hzero, hbound, hbound] }

/-- Deleting an ordinary old vertex from `K_(n+1)^(n-1)` leaves
`K_n^(n-2)`.  The sole old nonneighbor (the last vertex) is excluded here. -/
def deleteKntHighOldIso (n : ℕ) (hn : 2 ≤ n)
    (a : Fin (n + 1)) (ha0 : a ≠ 0) (haLast : a ≠ Fin.last n) :
    deleteVertex (Knt (n + 1) (n - 1)) a ≃g Knt n (n - 2) := by
  letI : NeZero n := ⟨by omega⟩
  let e : Fin n ≃ {x : Fin (n + 1) // x ≠ a} := finSuccAboveEquiv a
  have he0 : (e (0 : Fin n)).1 = (0 : Fin (n + 1)) := by
    simpa [e, finSuccAboveEquiv] using Fin.succAbove_ne_zero_zero ha0
  have hzero (i : Fin n) : (e i).1.val = 0 ↔ i.val = 0 := by
    constructor
    · intro h
      have hei : e i = e (0 : Fin n) := by
        apply Subtype.ext
        apply Fin.ext
        simpa [he0] using h
      exact congrArg Fin.val (e.injective hei)
    · intro h
      have hi : i = 0 := Fin.ext h
      subst i
      exact congrArg Fin.val he0
  have hnezero (i : Fin n) : (e i).1.val ≠ 0 ↔ i.val ≠ 0 :=
    not_congr (hzero i)
  have haValLast : a.val ≠ n := by
    intro h
    apply haLast
    apply Fin.ext
    exact h
  have haBound : a.val ≤ n - 1 := by
    have := a.isLt
    omega
  have hbound (i : Fin n) :
      (e i).1.val ≤ n - 1 ↔ i.val ≤ n - 2 := by
    have haLt := a.isLt
    have hiLt := i.isLt
    have hzeroVal : (0 : Fin (n + 1)).val = 0 := rfl
    have hlastVal : (Fin.last n).val = n := rfl
    have hcastVal : i.castSucc.val = i.val := rfl
    have hsuccVal : i.succ.val = i.val + 1 := rfl
    change (a.succAbove i).val ≤ n - 1 ↔ i.val ≤ n - 2
    unfold Fin.succAbove
    split_ifs <;> dsimp <;> omega
  have hne (i j : Fin n) : (e i).1 ≠ (e j).1 ↔ i ≠ j := by
    constructor
    · intro h hij
      exact h (congrArg Subtype.val (congrArg e hij))
    · intro hij h
      exact hij (e.injective (Subtype.ext h))
  exact
    { toEquiv := e.symm
      map_rel_iff' := by
        intro x y
        obtain ⟨i, rfl⟩ := e.surjective x
        obtain ⟨j, rfl⟩ := e.surjective y
        simp only [e.symm_apply_apply]
        change (Knt n (n - 2)).Adj i j ↔
          (Knt (n + 1) (n - 1)).Adj (e i).1 (e j).1
        simp only [Knt]
        rw [hne]
        rw [hnezero, hnezero, hzero, hzero, hbound, hbound] }

/-- Deleting the unique old nonneighbor of `0` from
`K_(n+1)^(n-1)` leaves a complete graph. -/
def deleteKntHighLastIso (n : ℕ) :
    deleteVertex (Knt (n + 1) (n - 1)) (Fin.last n) ≃g
      completeGraph (Fin n) where
  toEquiv := (finSuccAboveEquiv (Fin.last n)).symm
  map_rel_iff' := by
    intro a b
    let e := (finSuccAboveEquiv (Fin.last n)).symm
    change (e a ≠ e b) ↔
      (a.1 ≠ b.1 ∧
        ((a.1.val ≠ 0 ∧ b.1.val ≠ 0) ∨
         (a.1.val = 0 ∧ b.1.val ≤ n - 1) ∨
         (b.1.val = 0 ∧ a.1.val ≤ n - 1)))
    have aval (x : {z : Fin (n + 1) // z ≠ Fin.last n}) : x.1.val ≤ n - 1 := by
      have hxlt := x.1.isLt
      have hxlast : x.1.val ≠ n := by
        intro h
        apply x.2
        apply Fin.ext
        exact h
      omega
    constructor
    · intro hab
      have habVal : a.1 ≠ b.1 := by
        intro h
        exact hab (congrArg e (Subtype.ext h))
      refine ⟨habVal, ?_⟩
      by_cases ha0 : a.1.val = 0
      · exact Or.inr (Or.inl ⟨ha0, aval b⟩)
      · by_cases hb0 : b.1.val = 0
        · exact Or.inr (Or.inr ⟨hb0, aval a⟩)
        · exact Or.inl ⟨ha0, hb0⟩
    · rintro ⟨hab, _⟩ he
      have hsub : a = b := e.injective he
      exact hab (congrArg Subtype.val hsub)

/-- Deleting vertex `1` or `2` from `K_(n+1)^2` leaves the distinguished
vertex with only one neighbor, so the deletion is not 2-connected. -/
theorem deleteKntTwoNear_notTwoConnected (n : ℕ) (hn : 4 ≤ n)
    (a : Fin (n + 1)) (haPos : 0 < a.val) (haTwo : a.val ≤ 2) :
    ¬IsTwoConnected (deleteVertex (Knt (n + 1) 2) a) := by
  have bad (a b : Fin (n + 1))
      (haPos : 0 < a.val) (haTwo : a.val ≤ 2)
      (hbPos : 0 < b.val) (hbTwo : b.val ≤ 2) (hab : b ≠ a)
      (hcover : ∀ x : Fin (n + 1), 0 < x.val → x.val ≤ 2 → x = a ∨ x = b) :
      ¬IsTwoConnected (deleteVertex (Knt (n + 1) 2) a) := by
    let z : {x : Fin (n + 1) // x ≠ a} := ⟨0, by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega⟩
    let c : {x : Fin (n + 1) // x ≠ a} := ⟨⟨3, by omega⟩, by
      intro h
      have hval : (3 : ℕ) = a.val := congrArg Fin.val h
      omega⟩
    intro htwo
    have hdel := htwo.2.2 ⟨b, hab⟩
    let z' : {x : {x : Fin (n + 1) // x ≠ a} // x ≠ ⟨b, hab⟩} :=
      ⟨z, by
        intro h
        have := congrArg (fun x => x.1.val) h
        simp [z] at this
        omega⟩
    let c' : {x : {x : Fin (n + 1) // x ≠ a} // x ≠ ⟨b, hab⟩} :=
      ⟨c, by
        intro h
        have := congrArg (fun x => x.1.val) h
        simp [c] at this
        omega⟩
    have hzc : z' ≠ c' := by
      intro h
      have := congrArg (fun x => x.1.1.val) h
      simp [z', c', z, c] at this
    obtain ⟨p⟩ := hdel z' c'
    let x := p.snd
    have hzx : ((deleteVertex (Knt (n + 1) 2) a).induce
        {w | w ≠ (⟨b, hab⟩ : {x : Fin (n + 1) // x ≠ a})}).Adj z' x :=
      p.adj_snd (p.not_nil_of_ne hzc)
    have hAdj : (Knt (n + 1) 2).Adj (0 : Fin (n + 1)) x.1.1 := hzx
    have hxPos : 0 < x.1.1.val := by
      rcases hAdj with ⟨hne, hcases⟩
      by_contra h
      have hxval : x.1.1.val = 0 := Nat.eq_zero_of_not_pos h
      have hx0 : x.1.1 = 0 := Fin.ext (by simpa using hxval)
      exact hne hx0.symm
    have hxTwo : x.1.1.val ≤ 2 := by
      rcases hAdj.2 with h | h | h
      · exact False.elim (h.1 rfl)
      · exact h.2
      · exact False.elim (by omega)
    rcases hcover x.1.1 hxPos hxTwo with hxa | hxb
    · exact x.1.2 hxa
    · apply x.2
      apply Subtype.ext
      exact hxb
  have haCases : a.val = 1 ∨ a.val = 2 := by omega
  rcases haCases with haOne | haTwoEq
  · let b : Fin (n + 1) := ⟨2, by omega⟩
    apply bad a b haPos haTwo (by simp [b]) (by simp [b])
    · intro h
      have := congrArg Fin.val h
      simp [b] at this
      omega
    · intro x hxPos hxTwo
      by_cases hx : x.val = 1
      · left
        apply Fin.ext
        omega
      · right
        apply Fin.ext
        simp [b]
        omega
  · let b : Fin (n + 1) := ⟨1, by omega⟩
    apply bad a b haPos haTwo (by simp [b]) (by simp [b])
    · intro h
      have := congrArg Fin.val h
      simp [b] at this
      omega
    · intro x hxPos hxTwo
      by_cases hx : x.val = 2
      · left
        apply Fin.ext
        omega
      · right
        apply Fin.ext
        simp [b]
        omega

/-- For order at least five, a 2-connected vertex-deletion of `K_m^2` is
again one of the three exceptional graphs.  The two deletions that would
break this conclusion are exactly the non-2-connected near deletions above. -/
theorem deleteKntTwo_twoConnected_isExceptional (m : ℕ) (hm : 5 ≤ m)
    (a : Fin m) (htwo : IsTwoConnected (deleteVertex (Knt m 2) a)) :
    IsExceptional (deleteVertex (Knt m 2) a) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hcard : Fintype.card {x : Fin (n + 1) // x ≠ a} = n := by simp
  by_cases ha0 : a.val = 0
  · have ha : a = 0 := Fin.ext ha0
    subst a
    left
    unfold IsomorphicToKn
    rw [hcard]
    exact ⟨deleteKntZeroIso n 2⟩
  · by_cases haTwo : a.val ≤ 2
    · have haPos : 0 < a.val := Nat.pos_of_ne_zero ha0
      exact False.elim
        (deleteKntTwoNear_notTwoConnected n (by omega) a haPos haTwo htwo)
    · right
      left
      unfold IsomorphicToKnt
      rw [hcard]
      exact ⟨deleteKntTwoFarIso n a (by omega)⟩

/-- For order at least five, every vertex-deletion of `K_m^(m-2)` is
exceptional: deleting `0` or its sole old nonneighbor gives a complete graph,
and every other deletion gives `K_(m-1)^((m-1)-2)`. -/
theorem deleteKntHigh_isExceptional (m : ℕ) (hm : 5 ≤ m) (a : Fin m) :
    IsExceptional (deleteVertex (Knt m (m - 2)) a) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hcard : Fintype.card {x : Fin (n + 1) // x ≠ a} = n := by simp
  have hparam : n + 1 - 2 = n - 1 := by omega
  rw [hparam]
  by_cases ha0 : a = 0
  · subst a
    left
    unfold IsomorphicToKn
    rw [hcard]
    exact ⟨deleteKntZeroIso n (n - 1)⟩
  · by_cases haLast : a = Fin.last n
    · subst a
      left
      unfold IsomorphicToKn
      rw [hcard]
      exact ⟨deleteKntHighLastIso n⟩
    · right
      right
      unfold IsomorphicToKnt
      rw [hcard]
      exact ⟨deleteKntHighOldIso n (by omega) a ha0 haLast⟩

/-- The deletion classification in label-free form.  This is the exact
contrapositive mechanism used in the proof of Lemma 4: an exceptional graph
of order at least five cannot have a 2-connected unexceptional deletion. -/
theorem exceptional_of_twoConnected_delete_isExceptional
    (K : SimpleGraph W) (x : W) (hcard : 5 ≤ Fintype.card W)
    (hexceptional : IsExceptional K)
    (htwo : IsTwoConnected (deleteVertex K x)) :
    IsExceptional (deleteVertex K x) := by
  rcases hexceptional with hcomplete | htwoFamily | hhighFamily
  · rcases hcomplete with ⟨e⟩
    let dIso := deleteVertexIso e x
    have hcanon : IsExceptional
        (deleteVertex (completeGraph (Fin (Fintype.card W))) (e x)) :=
      deleteComplete_isExceptional (Fintype.card W) (by omega) (e x)
    exact (isoIsExceptional dIso).mpr hcanon
  · rcases htwoFamily with ⟨e⟩
    let dIso := deleteVertexIso e x
    have hcanonTwo : IsTwoConnected
        (deleteVertex (Knt (Fintype.card W) 2) (e x)) :=
      (isoIsTwoConnected dIso).mp htwo
    have hcanon := deleteKntTwo_twoConnected_isExceptional
      (Fintype.card W) hcard (e x) hcanonTwo
    exact (isoIsExceptional dIso).mpr hcanon
  · rcases hhighFamily with ⟨e⟩
    let dIso := deleteVertexIso e x
    have hcanon := deleteKntHigh_isExceptional
      (Fintype.card W) hcard (e x)
    exact (isoIsExceptional dIso).mpr hcanon

end

end BKLPS
