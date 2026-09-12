import Proof.Definitions
import Proof.Theorem1
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Data.Sym.Card
import Proof.Lemma7Proof1
import Proof.Lemma7Proof2
import Proof.Lemma7Proof3

/-!
Main route of the sharpness construction.

Start with a clique `Q` of order `n-2`, choose distinct `a,b∈Q`, and add
new vertices `x,y` and exactly the edges `ax`, `by`, and `xy`.  The proof
first verifies directly that this graph is 2-connected and avoids the three
exceptional families.

Its diameter is two and its only nonedges are the pairs from `x` to
`Q\{a}` and from `y` to `Q\{b}`, hence
`W(G_n)=(n²+3n-12)/2`.  Splitting the Szeged sum into the five edge classes
inside `Q\{a,b}`, incident with `a` or `b`, the edge `ab`, the edges `ax,by`,
and the edge `xy` gives `Sz(G_n)=(n²+7n-12)/2`.  Their difference is `2n`.
-/

namespace BKLPS

open SimpleGraph

noncomputable section

/-- **Lemma 7 (sharpness).** For every `n ≥ 10`, an unexceptional
2-connected graph of order `n` attains `η(G)=2n`. -/
theorem lemma7 (n : ℕ) (h_order : n ≥ 10) :
    ∃ G : SimpleGraph (Fin n),
      IsUnexceptional G ∧ IsTwoConnected G ∧
        szegedWienerGap G = (2 * n : ℤ) := by
  /- This is the finishing calculation from the informal proof.  The first
  proof unit verifies that the clique-plus-`ax,by,xy` construction is
  2-connected and unexceptional.  The second computes

      W(Gₙ) = (n² + 3n - 12) / 2,

  and the third partitions the edges into the manuscript's five classes and
  computes

      Sz(Gₙ) = (n² + 7n - 12) / 2.

  Their difference is therefore exactly `2n`. -/
  have h_structure := lemma7Proof1 n h_order
  have h_wiener :
      (wienerIndex (sharpnessGraph n) : ℤ) =
        ((n : ℤ) ^ 2 + 3 * n - 12) / 2 :=
    lemma7Proof2 n h_order
  have h_szeged :
      (szegedIndex (sharpnessGraph n) : ℤ) =
        ((n : ℤ) ^ 2 + 7 * n - 12) / 2 :=
    lemma7SzegedIndex n h_order
  refine ⟨sharpnessGraph n, h_structure.2, h_structure.1, ?_⟩
  unfold szegedWienerGap
  rw [h_szeged, h_wiener]
  omega

end

end BKLPS
