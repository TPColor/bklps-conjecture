import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Definitions for the BKLPS conjecture

This file formalizes the notation used by Bonamy--Knor--Lužar--Pinlou--
Škrekovski in *On the difference between the Szeged and the Wiener index*.
Graphs are finite and simple, as they are in the paper.

The manuscript definitions come first and are the definitions used by every
theorem: closer-vertex counts, the Wiener and Szeged indices, their
integer-valued gap, open and closed neighborhoods, deletion, 2-connectivity,
blocks, the cone graph `K_n^t`, and the exceptional families.  Definitions
needed only to state the imported BKLPS arguments are kept in the later
`BKLPS-only definitions` section.  Thus, where the manuscript and BKLPS use
the same mathematical object, there is one preferred Lean definition rather
than parallel encodings joined later by conversion lemmas.

The pair-gap language at the end makes the standard double count literal:
good edges for an unordered pair minus its distance sum to
`szegedWienerGap`, and vertex contributions sum to twice that gap.  The block
extension and cross-block definitions then reproduce exactly the quantities
appearing in the terminal cases of Theorems 3 and 6.
-/

open scoped BigOperators

namespace BKLPS

open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Definitions from the informal proof

These are the definitions and conventions used in Lily Zhang and Evan Li's manuscript
When the manuscript and BKLPS use essentially the same definition, this is the
preferred version used throughout the formalization.
-/

/-- The order of a finite graph. -/
def graphOrder (_G : SimpleGraph V) : ℕ :=
  Fintype.card V

/-- The set of vertices strictly closer to `a` than to `b`.

This is the set counted by the paper's notation `n_ab(a)`.
-/
def closerVertices (G : SimpleGraph V) (a b : V) : Finset V :=
  Finset.univ.filter fun x => G.dist x a < G.dist x b

/-- `n_ab(a)`: the number of vertices strictly closer to `a` than to `b`. -/
def closerCount (G : SimpleGraph V) (a b : V) : ℕ :=
  (closerVertices G a b).card

/-- The contribution `n_ab(a) * n_ab(b)` of an unordered pair `{a,b}`.

The function is defined on `Sym2 V` because edges of a simple graph are
unordered pairs.
-/
def szegedContribution (G : SimpleGraph V) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun a b => closerCount G a b * closerCount G b a, by
    intro a b
    simp only [mul_comm]⟩

/-- The Wiener index `W(G)`, the sum of distances over all unordered pairs of
vertices.  Diagonal pairs may be included because their distance is zero. -/
def wienerIndex (G : SimpleGraph V) : ℕ :=
  ∑ p : Sym2 V,
    Sym2.lift ⟨G.dist, fun a b => SimpleGraph.dist_comm (G := G) (u := a) (v := b)⟩ p

/-- The Szeged index `Sz(G) = ∑_{ab ∈ E} n_ab(a) n_ab(b)`. -/
def szegedIndex (G : SimpleGraph V) : ℕ := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  exact ∑ e : G.edgeSet, szegedContribution G e.1

/-- The Szeged--Wiener gap `η(G) = Sz(G) - W(G)`.

It is integer-valued here so that the displayed subtraction has its ordinary
mathematical meaning rather than truncated natural-number subtraction.
-/
def szegedWienerGap (G : SimpleGraph V) : ℤ :=
  (szegedIndex G : ℤ) - wienerIndex G

/-- The open neighborhood `N_G(u)` used in the manuscript. -/
def openNeighborhood (G : SimpleGraph V) (u : V) : Finset V := by
  classical
  letI : Fintype (G.neighborSet u) := Fintype.ofFinite _
  exact G.neighborFinset u

/-- The closed neighborhood `N_G[u] = N_G(u) ∪ {u}`. -/
def closedNeighborhood (G : SimpleGraph V) (u : V) : Finset V :=
  insert u (openNeighborhood G u)

/-- Vertex deletion `G - u`, represented as the induced graph on the vertices
different from `u`. -/
def deleteVertex (G : SimpleGraph V) (u : V) : SimpleGraph {v : V // v ≠ u} :=
  G.induce {v : V | v ≠ u}

/-- Decidable adjacency is inherited by induced graphs. -/
instance instDecidableRelInduce (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V) :
    DecidableRel (G.induce S).Adj := by
  intro a b
  exact inferInstanceAs (Decidable (G.Adj a.1 b.1))

/-- Decidable adjacency is inherited by vertex deletion. -/
instance instDecidableRelDeleteVertex (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    DecidableRel (deleteVertex G u).Adj := by
  intro a b
  exact inferInstanceAs (Decidable (G.Adj a.1 b.1))

/-- A cut vertex of a connected graph: deleting it disconnects the graph.
The order condition handles the conventional one-vertex edge case. -/
def IsCutVertex (G : SimpleGraph V) (u : V) : Prop :=
  Fintype.card V ≥ 2 ∧ G.Connected ∧ ¬(deleteVertex G u).Connected

/-- A graph has no cut vertex. -/
def HasNoCutVertex (G : SimpleGraph V) : Prop :=
  ∀ u : V, ¬IsCutVertex G u

/-- A finite simple graph is 2-connected when it has at least three vertices
and deleting any one vertex leaves a connected graph. -/
def IsTwoConnected (G : SimpleGraph V) : Prop :=
  Fintype.card V ≥ 3 ∧
    G.Connected ∧
      ∀ v : V, (G.induce {w : V | w ≠ v}).Connected

/-- A block is a maximal connected subgraph with no cut vertex.  We identify
an induced subgraph with its vertex set, which is harmless for blocks. -/
def IsBlock (G : SimpleGraph V) (B : Set V) : Prop :=
  by
    classical
    exact Maximal (fun S : Set V =>
      letI : Fintype S := Fintype.ofFinite S
      (G.induce S).Connected ∧ HasNoCutVertex (G.induce S)) B

/-- A vertex is the unique cut vertex of a graph. -/
def IsUniqueCutVertex (G : SimpleGraph V) (u : V) : Prop :=
  IsCutVertex G u ∧ ∀ v : V, IsCutVertex G v → v = u

/-- The paper's graph `K_n^t`: start with `K_(n-1)` and add one new vertex
adjacent to exactly `t` old vertices.

Vertex `0` is the new vertex; its neighbors are `1, ..., t`.  The conjecture
only uses this definition with `n ≥ 10` and `t ∈ {2, n - 2}`.
-/
def Knt (n t : ℕ) : SimpleGraph (Fin n) where
  Adj u v :=
    u ≠ v ∧
      ((u.val ≠ 0 ∧ v.val ≠ 0) ∨
        (u.val = 0 ∧ v.val ≤ t) ∨
        (v.val = 0 ∧ u.val ≤ t))
  symm u v h := by
    rcases h with ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless u h := h.1 rfl

/-- The canonical `K_n^t` graph has decidable adjacency. -/
instance instDecidableRelKnt (n t : ℕ) : DecidableRel (Knt n t).Adj := by
  intro u v
  exact inferInstanceAs (Decidable
    (u ≠ v ∧ ((u.val ≠ 0 ∧ v.val ≠ 0) ∨
      (u.val = 0 ∧ v.val ≤ t) ∨ (v.val = 0 ∧ u.val ≤ t))))

/-- `G` is isomorphic to the complete graph of its order. -/
def IsomorphicToKn (G : SimpleGraph V) : Prop :=
  Nonempty (G ≃g (completeGraph (Fin (Fintype.card V))))

/-- `G` is isomorphic to the paper's `K_n^t`, where `n` is the order of `G`. -/
def IsomorphicToKnt (G : SimpleGraph V) (t : ℕ) : Prop :=
  Nonempty (G ≃g Knt (Fintype.card V) t)

/-- The manuscript's `n`-exceptional graphs: `K_n`, `K_n^2`, and
`K_n^(n-2)`.  Here `n` is inferred as the graph's order. -/
def IsExceptional (G : SimpleGraph V) : Prop :=
  IsomorphicToKn G ∨
    IsomorphicToKnt G 2 ∨
      IsomorphicToKnt G (Fintype.card V - 2)

/-- A graph is `n`-unexceptional when it is not one of the three exceptional
graphs of its order. -/
def IsUnexceptional (G : SimpleGraph V) : Prop :=
  ¬IsExceptional G

/-- The cycle `C_n`. -/
def Cn (n : ℕ) : SimpleGraph (Fin n) :=
  cycleGraph n

/-- `G` is isomorphic to the cycle `C_n`. -/
def IsomorphicToCn (G : SimpleGraph V) (n : ℕ) : Prop :=
  Nonempty (G ≃g Cn n)

/-- Whether an unordered edge is `{a,b}`-good in the sense of the informal
proof.  Both possible orientations of the edge are included literally. -/
def IsGoodEdgeFor (G : SimpleGraph V) (a b : V) : Sym2 V → Prop :=
  Sym2.lift ⟨fun x y =>
    G.Adj x y ∧
      ((G.dist a x < G.dist a y ∧ G.dist b y < G.dist b x) ∨
        (G.dist a y < G.dist a x ∧ G.dist b x < G.dist b y)), by
    intro x y
    apply propext
    constructor
    · rintro ⟨hxy, h | h⟩
      · exact ⟨hxy.symm, Or.inr h⟩
      · exact ⟨hxy.symm, Or.inl h⟩
    · rintro ⟨hyx, h | h⟩
      · exact ⟨hyx.symm, Or.inr h⟩
      · exact ⟨hyx.symm, Or.inl h⟩⟩

/-- The finset of `{a,b}`-good edges. -/
def goodEdgeFinset (G : SimpleGraph V) (a b : V) : Finset (Sym2 V) :=
  by
    classical
    letI : Fintype G.edgeSet := Fintype.ofFinite _
    exact G.edgeFinset.filter (IsGoodEdgeFor G a b)

/-- `g_G(a,b)`, the number of `{a,b}`-good edges. -/
def goodEdgeCount (G : SimpleGraph V) (a b : V) : ℕ :=
  (goodEdgeFinset G a b).card

/-- The pair contribution `η_G(a,b) = g_G(a,b) - d_G(a,b)`. -/
def pairGap (G : SimpleGraph V) (a b : V) : ℤ :=
  (goodEdgeCount G a b : ℤ) - G.dist a b

/-- The contribution `c_G(a) = ∑_b η_G(a,b)` of a vertex. -/
def vertexContribution (G : SimpleGraph V) (a : V) : ℤ :=
  ∑ b : V, pairGap G a b

/-! ## Technical unordered-pair representations

The manuscript writes `g_G(a,b)` and `η_G(a,b)` with two vertex arguments,
although both quantities depend only on the unordered pair `{a,b}`.  The two
lifts below make that fact explicit when applying finite double-counting
identities.  They introduce no new mathematical notion.
-/

/-- `g_G(a,b)` regarded as a function of the unordered pair `{a,b}`. -/
def goodEdgeCountOnPair (G : SimpleGraph V) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun a b => goodEdgeCount G a b, by
    intro a b
    classical
    apply congrArg Finset.card
    unfold goodEdgeFinset
    apply Finset.filter_congr
    intro e _
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp only [IsGoodEdgeFor, Sym2.lift_mk]
        aesop⟩

/-- `η_G(a,b)` regarded as a function of the unordered pair `{a,b}`. -/
def pairGapOnPair (G : SimpleGraph V) : Sym2 V → ℤ :=
  Sym2.lift ⟨fun a b => pairGap G a b, by
    intro a b
    change (goodEdgeCount G a b : ℤ) - G.dist a b =
      (goodEdgeCount G b a : ℤ) - G.dist b a
    rw [show goodEdgeCount G a b = goodEdgeCount G b a by
      change goodEdgeCountOnPair G s(a, b) = goodEdgeCountOnPair G s(b, a)
      rw [Sym2.eq_swap]]
    rw [SimpleGraph.dist_comm]⟩

/-! ## BKLPS-only definitions

No separate BKLPS-only definition is currently needed: every BKLPS notion used
by the manuscript agrees with a manuscript definition above.  External BKLPS
results live in `Proof/ExternalResults` and use these preferred definitions.
-/

end

end BKLPS
