import Proof.Definitions
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring.RingNF
import Proof.ExternalResults.GraphIsomorphismInvariants
import Proof.Theorem1Proof1

/-!
Main route of the manuscript proof of Theorem 1.

For `G = K_n^t`, let `z` be the vertex of degree `t`, put
`A = N_G(z)`, and put `B = V(G) \ (A ∪ {z})`.  Thus `|A| = t` and
`|B| = n-t-1`.  The Wiener-index computation separates pairs inside
`A ∪ B`, pairs `za`, and pairs `zb`, giving

`W(G) = choose (n-1) 2 + t + 2(n-t-1)`.

The Szeged-index computation separates edges inside `A` or `B`, edges from
`A` to `B`, and edges from `z` to `A`.  Their respective closer-vertex
products are `1`, `2`, and `n-t`, so

`Sz(G) = choose t 2 + choose (n-t-1) 2 + 2t(n-t-1) + t(n-t)`.

Subtracting gives `η(K_n^t)=2(t-1)(n-t-1)`.  Replacing `t` by `n-t`
exchanges the two factors and proves the complementary formula.
-/

namespace BKLPS

noncomputable section

/-- **Theorem 1.** If `t ≥ 1` and `t ≤ n-1`, then both `K_n^t` and `K_n^(n-t)`
have Szeged--Wiener gap `2(t-1)(n-t-1)`. -/
theorem theorem1 (n t : ℕ) (h_lower : t ≥ 1) (h_upper : t ≤ n - 1) :
    szegedWienerGap (Knt n t) =
        2 * ((t : ℤ) - 1) * ((n : ℤ) - t - 1) ∧
      szegedWienerGap (Knt n (n - t)) =
        2 * ((t : ℤ) - 1) * ((n : ℤ) - t - 1) := by
  /- The edge-class computation is needed only for `K_n^t`.  For the
  complementary parameter, apply that same computation with `n-t`; the two
  factors exchange places, so commutativity gives the stated common value. -/
  have hfirst := theorem1Proof1 n t h_lower h_upper
  have ht_le_n : t ≤ n := by omega
  have hcomplement_lower : n - t ≥ 1 := by omega
  have hcomplement_upper : n - t ≤ n - 1 := by omega
  have hsecond := theorem1Proof1 n (n - t) hcomplement_lower hcomplement_upper
  rw [Nat.cast_sub ht_le_n] at hsecond
  constructor
  · exact hfirst
  · ring_nf at hsecond ⊢
    exact hsecond

/-- Theorem 1 transported from the canonical model `K_n^t` to any graph
isomorphic to it. -/
theorem theorem1OfIsomorphicToKnt
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : ℕ)
    (h_lower : t ≥ 1) (h_upper : t ≤ Fintype.card V - 1)
    (h_iso : IsomorphicToKnt G t) :
    szegedWienerGap G =
      2 * ((t : ℤ) - 1) * ((Fintype.card V : ℤ) - t - 1) := by
  rcases h_iso with ⟨e⟩
  rw [← External.isoSzegedWienerGap e]
  exact theorem1Proof1 (Fintype.card V) t h_lower h_upper

end

end BKLPS
