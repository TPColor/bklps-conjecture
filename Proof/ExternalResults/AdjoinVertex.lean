import Proof.Definitions
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Relabeling a graph after one distinguished vertex has been removed.

The equivalence `vertexEquivOptionDelete u` separates `u` from the subtype
of all other vertices.  Given a labeling of that subtype by `Fin m`, the
composite `adjoinDeletedEquiv` labels the original graph by `Fin (m+1)`,
sending every old vertex through `Fin.castSucc` and sending `u` to
`Fin.last m`.  The two evaluation lemmas record these formulas explicitly.

This is the bookkeeping needed in Exceptional Deletion: an isomorphism
`G-u ≃g K_m^t` is extended to the whole vertex set, after which the assumed
attachment pattern of `u` can be checked edge by edge against `K_(m+1)^t`.
-/

namespace BKLPS.External

noncomputable section

universe u

/-- Splitting a finite vertex type at a distinguished vertex. -/
def vertexEquivOptionDelete {V : Type u} [DecidableEq V] (u : V) :
    V ≃ Option {x : V // x ≠ u} where
  toFun x := if h : x = u then none else some ⟨x, h⟩
  invFun x := match x with
    | none => u
    | some x => x.1
  left_inv x := by by_cases h : x = u <;> simp [h]
  right_inv x := by
    cases x with
    | none => simp
    | some x => simp [x.2]

@[simp] theorem vertexEquivOptionDelete_apply_self
    {V : Type u} [DecidableEq V] (u : V) :
    vertexEquivOptionDelete u u = none := by
  simp [vertexEquivOptionDelete]

@[simp] theorem vertexEquivOptionDelete_apply_ne
    {V : Type u} [DecidableEq V] (u x : V) (h : x ≠ u) :
    vertexEquivOptionDelete u x = some ⟨x, h⟩ := by
  simp [vertexEquivOptionDelete, h]

/-- Relabel a vertex and its deletion separately, putting the distinguished
vertex last. -/
def adjoinDeletedEquiv
    {V : Type u} [DecidableEq V] {m : ℕ} (u : V)
    (e : {x : V // x ≠ u} ≃ Fin m) : V ≃ Fin (m + 1) :=
  (vertexEquivOptionDelete u).trans
    ((Equiv.optionCongr e).trans finSuccEquivLast.symm)

@[simp] theorem adjoinDeletedEquiv_apply_self
    {V : Type u} [DecidableEq V] {m : ℕ} (u : V)
    (e : {x : V // x ≠ u} ≃ Fin m) :
    adjoinDeletedEquiv u e u = Fin.last m := by
  simp [adjoinDeletedEquiv]

@[simp] theorem adjoinDeletedEquiv_apply_ne
    {V : Type u} [DecidableEq V] {m : ℕ} (u x : V) (hx : x ≠ u)
    (e : {x : V // x ≠ u} ≃ Fin m) :
    adjoinDeletedEquiv u e x = Fin.castSucc (e ⟨x, hx⟩) := by
  simp [adjoinDeletedEquiv, hx]

end

end BKLPS.External
