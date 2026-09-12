import Proof.Definitions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.Fintype.Perm

/-!
Executable finite-graph infrastructure.  Mathlib's mathematical graph
distance is intentionally noncomputable, so finite checks repeatedly enlarge
the set of vertices which can reach a fixed target.  The lemmas below identify
the first successful stage with `SimpleGraph.dist` on connected graphs.

After at most `|V|-1` stages every vertex reachable from the target has been
found, because a shortest path is simple.  This produces `finiteDist`; the
closer counts, Wiener index, Szeged index, and gap are then finite executable
sums.  For connected graphs the file proves each executable quantity equal
to the corresponding manuscript definition.

Graphs on `Fin n` are encoded by finite sets of ordered representatives of
unordered edges.  `codedGraph_graphCode` proves that encoding and decoding
are inverse on simple graphs.  Boolean tests for connectedness after every
deletion, exceptional-family isomorphism, and graph isomorphism are connected
to their propositions by soundness lemmas.  Consequently every later
`native_decide` closes an ordinary finite proposition whose result is
transported back to `szegedWienerGap`; no executable surrogate appears in a
public theorem statement.
-/

namespace BKLPS.External

open SimpleGraph
open scoped BigOperators

noncomputable section Proofs

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- After `k` stages, the vertices from which the target `b` can be reached
by a walk of length at most `k`.  Keeping the whole frontier makes native
evaluation share the preceding stage instead of enumerating all walks. -/
def reachableTo (G : SimpleGraph V) [DecidableRel G.Adj] (b : V) : ℕ → Finset V
  | 0 => {b}
  | k + 1 =>
      let previous := reachableTo G b k
      previous ∪ (Finset.univ.filter fun x =>
        ∃ y ∈ previous, G.Adj x y)

theorem mem_reachableTo_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) (k : ℕ) :
    a ∈ reachableTo G b k ↔ ∃ p : G.Walk a b, p.length ≤ k := by
  induction k generalizing a with
  | zero =>
      constructor
      · intro ha
        have hab : a = b := by simpa [reachableTo] using ha
        subst b
        exact ⟨Walk.nil, by simp⟩
      · rintro ⟨p, hp⟩
        have hlen : p.length = 0 := Nat.eq_zero_of_le_zero hp
        have hab : a = b := Walk.eq_of_length_eq_zero hlen
        simpa [reachableTo, hab]
  | succ k ih =>
      simp only [reachableTo, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro (ha | ⟨y, hy, hay⟩)
        · obtain ⟨p, hp⟩ := (ih a).mp ha
          exact ⟨p, hp.trans (Nat.le_succ k)⟩
        · obtain ⟨q, hq⟩ := (ih y).mp hy
          exact ⟨Walk.cons hay q, by simpa using Nat.succ_le_succ hq⟩
      · rintro ⟨p, hp⟩
        cases p with
        | nil =>
            left
            exact (ih _).mpr ⟨Walk.nil, Nat.zero_le _⟩
        | cons hay q =>
            right
            refine ⟨_, (ih _).mpr ⟨q, ?_⟩, hay⟩
            simpa [Walk.length_cons] using hp

/-- The stages below `|V|` at which `a` has reached `b`. -/
def realizedWalkLengths (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) : Finset ℕ :=
  (Finset.range (Fintype.card V)).filter fun k =>
    a ∈ reachableTo G b k

/-- Executable graph distance, with value zero when there is no path. -/
def finiteDist (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) : ℕ :=
  if h : (realizedWalkLengths G a b).Nonempty then
    (realizedWalkLengths G a b).min' h
  else 0

theorem finiteDist_eq_dist (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (a b : V) : finiteDist G a b = G.dist a b := by
  have hreach : G.Reachable a b := hconn a b
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  have hpath := Walk.isPath_of_length_eq_dist p hp
  have hlt : G.dist a b < Fintype.card V := by
    rw [← hp]
    exact hpath.length_lt
  have hmem : G.dist a b ∈ realizedWalkLengths G a b := by
    simp only [realizedWalkLengths, Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt, (mem_reachableTo_iff G a b _).mpr ⟨p, hp.le⟩⟩
  have hnonempty : (realizedWalkLengths G a b).Nonempty := ⟨_, hmem⟩
  rw [finiteDist, dif_pos hnonempty]
  apply Nat.le_antisymm
  · exact Finset.min'_le _ _ hmem
  · have hminmem := Finset.min'_mem (realizedWalkLengths G a b) hnonempty
    simp only [realizedWalkLengths, Finset.mem_filter, Finset.mem_range] at hminmem
    obtain ⟨q, hq⟩ := (mem_reachableTo_iff G a b _).mp hminmem.2
    exact (G.dist_le q).trans hq

theorem finiteDist_comm (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    finiteDist G a b = finiteDist G b a := by
  have hsets : realizedWalkLengths G a b = realizedWalkLengths G b a := by
    ext k
    simp only [realizedWalkLengths, Finset.mem_filter, Finset.mem_range,
      and_congr_right_iff]
    intro _hk
    rw [mem_reachableTo_iff, mem_reachableTo_iff]
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨p.reverse, by simpa using hp⟩
    · rintro ⟨p, hp⟩
      exact ⟨p.reverse, by simpa using hp⟩
  simp [finiteDist, hsets]

/-- Executable version of `closerCount`. -/
def finiteCloserCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) : ℕ :=
  ((Finset.univ : Finset V).filter fun x => finiteDist G x a < finiteDist G x b).card

theorem finiteCloserCount_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (a b : V) :
    finiteCloserCount G a b = closerCount G a b := by
  unfold finiteCloserCount closerCount closerVertices
  congr 1
  ext x
  simp [finiteDist_eq_dist G hconn]

/-- Executable Wiener index. -/
def finiteWienerIndex (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ∑ p : Sym2 V,
    Sym2.lift ⟨finiteDist G, finiteDist_comm G⟩ p

/-- Executable Szeged index, summed directly over `edgeFinset`. -/
def finiteSzegedIndex (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ∑ e ∈ G.edgeFinset,
    Sym2.lift ⟨fun a b => finiteCloserCount G a b * finiteCloserCount G b a,
      fun a b => by simp [mul_comm]⟩ e

/-- Executable Szeged--Wiener gap. -/
def finiteGap (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ :=
  (finiteSzegedIndex G : ℤ) - finiteWienerIndex G

theorem finiteWienerIndex_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) : finiteWienerIndex G = wienerIndex G := by
  unfold finiteWienerIndex wienerIndex
  apply Finset.sum_congr rfl
  intro p _
  induction p using Sym2.inductionOn with
  | _ a b => simp [finiteDist_eq_dist G hconn]

theorem finiteSzegedIndex_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) : finiteSzegedIndex G = szegedIndex G := by
  unfold szegedIndex
  rw [← Finset.sum_subtype G.edgeFinset (fun e => SimpleGraph.mem_edgeFinset)]
  unfold finiteSzegedIndex
  apply Finset.sum_congr rfl
  intro p _
  induction p using Sym2.inductionOn with
  | _ a b => simp [szegedContribution, finiteCloserCount_eq G hconn]

theorem finiteGap_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) : finiteGap G = szegedWienerGap G := by
  simp [finiteGap, szegedWienerGap, finiteSzegedIndex_eq G hconn,
    finiteWienerIndex_eq G hconn]

end Proofs

section Codes

/-- Executable connectedness test using the bounded-reachability sets above. -/
def connectedBool {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] : Bool :=
  decide (0 < Fintype.card W) &&
    decide (∀ a b : W, a ∈ reachableTo G b (Fintype.card W - 1))

theorem connectedBool_eq_true {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    connectedBool G = true ↔ G.Connected := by
  constructor
  · intro h
    rw [connectedBool, Bool.and_eq_true] at h
    letI : Nonempty W := Fintype.card_pos_iff.mp (of_decide_eq_true h.1)
    refine ⟨?_⟩
    intro a b
    have hab : a ∈ reachableTo G b (Fintype.card W - 1) :=
      (of_decide_eq_true h.2) a b
    obtain ⟨p, _hp⟩ := (mem_reachableTo_iff G a b _).mp hab
    exact ⟨p⟩
  · intro h
    rw [connectedBool, Bool.and_eq_true]
    constructor
    · exact decide_eq_true (Fintype.card_pos_iff.mpr h.nonempty)
    · apply decide_eq_true
      intro a b
      obtain ⟨p, hp⟩ := (h a b).exists_walk_length_eq_dist
      have hpath := Walk.isPath_of_length_eq_dist p hp
      apply (mem_reachableTo_iff G a b _).mpr
      refine ⟨p, ?_⟩
      have hlt : p.length < Fintype.card W := hpath.length_lt
      omega

/-- One canonical representative `(a,b)` with `a < b` of an unordered
edge on `Fin n`. -/
abbrev OrderedEdge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- The simple graph represented by a finset of canonical ordered edges. -/
def codedGraph {n : ℕ} (E : Finset (OrderedEdge n)) : SimpleGraph (Fin n) where
  Adj a b :=
    (∃ h : a < b, (⟨(a, b), h⟩ : OrderedEdge n) ∈ E) ∨
      ∃ h : b < a, (⟨(b, a), h⟩ : OrderedEdge n) ∈ E
  symm a b := by aesop
  loopless a := by simp

instance {n : ℕ} (E : Finset (OrderedEdge n)) :
    DecidableRel (codedGraph E).Adj := by
  intro a b
  unfold codedGraph
  infer_instance

/-- Extract the canonical edge code of a graph with decidable adjacency. -/
def graphCode {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Finset (OrderedEdge n) :=
  (Finset.univ : Finset (OrderedEdge n)).filter fun p => G.Adj p.1.1 p.1.2

theorem codedGraph_graphCode {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : codedGraph (graphCode G) = G := by
  ext a b
  simp only [codedGraph, graphCode, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro (⟨_, hab⟩ | ⟨_, hba⟩)
    · exact hab
    · exact hba.symm
  · intro hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact Or.inl ⟨hlt, hab⟩
    · exact False.elim (hab.ne heq)
    · exact Or.inr ⟨hgt, hab.symm⟩

/-- Executable test for the manuscript's definition of 2-connectivity. -/
def isTwoConnectedBool {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Bool := by
  exact decide (Fintype.card (Fin n) ≥ 3) && connectedBool G &&
    decide (∀ v : Fin n, connectedBool (G.induce {w : Fin n | w ≠ v}) = true)

theorem isTwoConnectedBool_eq_true {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : isTwoConnectedBool G = true ↔ IsTwoConnected G := by
  simp [isTwoConnectedBool, IsTwoConnected, connectedBool_eq_true, and_assoc]

/-- Executable search over all relabelings of `Fin n`. -/
def isomorphicBool {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] : Bool :=
  decide (∃ e : Fin n ≃ Fin n,
    ∀ a b : Fin n, G.Adj a b ↔ H.Adj (e a) (e b))

theorem isomorphicBool_eq_true_imp {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : isomorphicBool G H = true) : Nonempty (G ≃g H) := by
  have hex : ∃ e : Fin n ≃ Fin n,
      ∀ a b : Fin n, G.Adj a b ↔ H.Adj (e a) (e b) := by
    exact of_decide_eq_true h
  obtain ⟨e, hmap⟩ := hex
  refine ⟨{
    toEquiv := e
    map_rel_iff' := ?_ }⟩
  intro a b
  exact (hmap a b).symm

/-- Executable recognition of the three exceptional families at order `n`. -/
def isExceptionalBool {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Bool :=
  isomorphicBool G (completeGraph (Fin n)) ||
    isomorphicBool G (Knt n 2) || isomorphicBool G (Knt n (n - 2))

theorem isExceptionalBool_eq_true_imp {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h : isExceptionalBool G = true) : IsExceptional G := by
  unfold isExceptionalBool at h
  rw [Bool.or_eq_true, Bool.or_eq_true] at h
  unfold IsExceptional IsomorphicToKn IsomorphicToKnt
  rw [show Fintype.card (Fin n) = n by simp]
  rcases h with (ha | hb) | hc
  · exact Or.inl (isomorphicBool_eq_true_imp G (completeGraph (Fin n)) ha)
  · exact Or.inr (Or.inl (isomorphicBool_eq_true_imp G (Knt n 2) hb))
  · exact Or.inr (Or.inr
      (isomorphicBool_eq_true_imp G (Knt n (n - 2)) hc))

end Codes

end BKLPS.External
