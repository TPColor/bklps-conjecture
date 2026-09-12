import Proof.ExternalResults.FiniteGraphCheck
import Proof.ExternalResults.GraphIsomorphismInvariants
import Proof.ExternalResults.AdjoinVertex
import Proof.ExternalResults.BlockStructure

/-! Small, independently checked labeling certificates for finite graphs.
The generator supplies only natural numbers. Every accepted row is checked
for bijectivity and preservation of every adjacency. -/

namespace BKLPS.External.OrderTenCertificate

open SimpleGraph

def reachNext {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (front : Finset V) : Finset V :=
  front ∪ (Finset.univ.filter fun x => ∃ y ∈ front, G.Adj x y)

def fastDistAux {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) : Nat → Nat → Finset V → Nat
  | remaining, distance, front =>
      if a ∈ front then distance
      else match remaining with
        | 0 => 0
        | k + 1 => fastDistAux G a k (distance + 1) (reachNext G front)

def fastDist {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) : Nat :=
  fastDistAux G a (Fintype.card V - 1) 0 {b}

theorem fastDist_eq_finiteDist {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    fastDist G a b = finiteDist G a b := by
  classical
  by_cases h : (realizedWalkLengths G a b).Nonempty
  · let d := (realizedWalkLengths G a b).min' h
    have hdmem : d ∈ realizedWalkLengths G a b := Finset.min'_mem _ h
    have hdlt : d < Fintype.card V := by
      exact Finset.mem_range.mp (Finset.mem_filter.mp hdmem).1
    have haux : ∀ (remaining distance : Nat), distance ≤ d →
        d ≤ distance + remaining →
        fastDistAux G a remaining distance (reachableTo G b distance) = d := by
      intro remaining
      induction remaining with
      | zero =>
          intro distance hdle hroom
          by_cases ha : a ∈ reachableTo G b distance
          · have heq : distance = d := by omega
            simpa [fastDistAux, ha] using heq
          · have heq : distance = d := by omega
            exact False.elim (ha (by simpa [heq] using (Finset.mem_filter.mp hdmem).2))
      | succ remaining ih =>
          intro distance hdle hroom
          by_cases ha : a ∈ reachableTo G b distance
          · have hlt : distance < Fintype.card V := by omega
            have hmem : distance ∈ realizedWalkLengths G a b := by
              simp [realizedWalkLengths, hlt, ha]
            have hmin : d ≤ distance := Finset.min'_le _ _ hmem
            have heq : distance = d := by omega
            simpa [fastDistAux, ha] using heq
          · have hne : distance ≠ d := by
              intro heq
              apply ha
              have hmemd := (Finset.mem_filter.mp hdmem).2
              simpa [heq] using hmemd
            simp only [fastDistAux, ha]
            rw [show reachNext G (reachableTo G b distance) =
                reachableTo G b (distance + 1) by simp [reachNext, reachableTo]]
            have hdist : distance + 1 ≤ d := by omega
            have hroom' : d ≤ (distance + 1) + remaining := by omega
            exact ih (distance + 1) hdist hroom'
    have hzero : reachableTo G b 0 = ({b} : Finset V) := by simp [reachableTo]
    simpa [fastDist, finiteDist, d, h, hzero] using
      haux (Fintype.card V - 1) 0 (by omega) (by omega)
  · have hnoMem : ∀ k, k < Fintype.card V → a ∉ reachableTo G b k := by
      intro k hk ha
      apply h
      refine ⟨k, ?_⟩
      simp [realizedWalkLengths, hk, ha]
    have hcardpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨a⟩
    have haux : ∀ (remaining distance : Nat), distance + remaining ≤ Fintype.card V - 1 →
        fastDistAux G a remaining distance (reachableTo G b distance) = 0 := by
      intro remaining
      induction remaining with
      | zero =>
          intro distance hroom
          have hlt : distance < Fintype.card V := by omega
          simp [fastDistAux, hnoMem distance hlt]
      | succ remaining ih =>
          intro distance hroom
          have hlt : distance < Fintype.card V := by omega
          simp only [fastDistAux, hnoMem distance hlt]
          rw [show reachNext G (reachableTo G b distance) =
              reachableTo G b (distance + 1) by simp [reachNext, reachableTo]]
          apply ih (distance + 1)
          omega
    have hzero : reachableTo G b 0 = ({b} : Finset V) := by simp [reachableTo]
    simpa [fastDist, finiteDist, h, hzero] using
      haux (Fintype.card V - 1) 0 (by omega)

theorem fastDist_comm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    fastDist G a b = fastDist G b a := by
  rw [fastDist_eq_finiteDist, fastDist_eq_finiteDist, finiteDist_comm]

/-! Evaluate each distance and closer count once per graph. The arrays are
only a cache of the executable quantities in `FiniteGraphCheck`. -/
def cachedGap {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℤ :=
  let d := Vector.ofFn fun a : Fin n => Vector.ofFn fun b : Fin n => fastDist G a b
  let c := Vector.ofFn fun a : Fin n => Vector.ofFn fun b : Fin n =>
    (Finset.univ.filter fun x : Fin n => d[x.val][a.val] < d[x.val][b.val]).card
  (∑ e ∈ G.edgeFinset, Sym2.lift
    ⟨fun a b : Fin n => c[a.val][b.val] * c[b.val][a.val], fun a b => Nat.mul_comm _ _⟩ e : Nat) -
    (∑ p : Sym2 (Fin n), Sym2.lift ⟨fun a b : Fin n => d[a.val][b.val], by
      intro a b
      simp only [d, Vector.getElem_ofFn]
      exact fastDist_comm G a b⟩ p : Nat)

theorem cachedGap_eq {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    : cachedGap G = finiteGap G := by
  unfold cachedGap finiteGap finiteSzegedIndex finiteWienerIndex
  dsimp only
  have hd (a b : Fin n) :
        (Vector.ofFn (fun a : Fin n => Vector.ofFn (fun b : Fin n => fastDist G a b)))[a.val][b.val] =
        finiteDist G a b := by
    rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
    rw [fastDist_eq_finiteDist]
  have hc (a b : Fin n) :
      (Vector.ofFn (fun a : Fin n => Vector.ofFn (fun b : Fin n =>
        (Finset.univ.filter fun x : Fin n =>
          (Vector.ofFn (fun a : Fin n => Vector.ofFn (fun b : Fin n => fastDist G a b)))[x.val][a.val] <
          (Vector.ofFn (fun a : Fin n => Vector.ofFn (fun b : Fin n => fastDist G a b)))[x.val][b.val]).card)))[a.val][b.val] =
        finiteCloserCount G a b := by
    unfold finiteCloserCount
    rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hd x a, hd x b]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      simp only [Sym2.lift_mk]
      rw [hc a b, hc b a]
  · congr 1
    apply Finset.sum_congr rfl
    intro p hp
    induction p using Sym2.inductionOn with
    | _ a b =>
      simp only [Sym2.lift_mk]
      rw [hd a b]

def graph (n g : Nat) : SimpleGraph (Fin n) :=
  codedGraph (Finset.univ.filter fun e : OrderedEdge n =>
    g.testBit (e.1.2.val * (e.1.2.val - 1) / 2 + e.1.1.val))

instance (n g : Nat) : DecidableRel (graph n g).Adj := by
  unfold graph
  infer_instance

def key {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Nat :=
  ∑ e : OrderedEdge n, if G.Adj e.1.1 e.1.2 then
    2 ^ (e.1.2.val * (e.1.2.val - 1) / 2 + e.1.1.val) else 0

def labeling {n : Nat} [NeZero n] (p : Nat) (i : Fin n) : Fin n :=
  ⟨p / n ^ i.val % n, Nat.mod_lt _ (NeZero.pos n)⟩

def checkIso {n : Nat} [NeZero n]
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (p : Nat) : Bool :=
  decide (Function.Injective (labeling (n := n) p)) &&
    decide (∀ a b, G.Adj a b ↔ H.Adj (labeling p a) (labeling p b))

theorem checkIso_sound {n : Nat} [NeZero n]
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (p : Nat) (h : checkIso G H p = true) : Nonempty (G ≃g H) := by
  simp only [checkIso, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨{ toEquiv := Equiv.ofBijective (labeling p)
              ((Fintype.bijective_iff_injective_and_card _).mpr ⟨h.1, rfl⟩)
           map_rel_iff' := fun {a b} => (h.2 a b).symm }⟩

def recognizedKey {n : Nat} [NeZero n] (k : Nat) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (reps : List Nat) (table : List (Nat × Nat × Nat)) : Bool :=
  match table with
  | [] => false
  | (g, r, p) :: rest =>
    if g < k then recognizedKey k G reps rest
    else if k < g then false
    else decide (r ∈ reps) && checkIso G (graph n r) p

def recognized {n : Nat} [NeZero n] (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (reps : List Nat) (table : List (Nat × Nat × Nat)) : Bool :=
  recognizedKey (key G) G reps table

theorem recognized_sound {n : Nat} [NeZero n] (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (reps : List Nat) (table : List (Nat × Nat × Nat))
    (h : recognized G reps table = true) :
    ∃ r ∈ reps, Nonempty (G ≃g graph n r) := by
  unfold recognized at h
  have aux : ∀ (k : Nat) (xs : List (Nat × Nat × Nat)),
      recognizedKey k G reps xs = true →
      ∃ r ∈ reps, Nonempty (G ≃g graph n r) := by
    intro k xs
    induction xs with
    | nil => intro h0; simp [recognizedKey] at h0
    | cons row rest ih =>
      intro h0
      rcases row with ⟨g, r, p⟩
      by_cases h₁ : g < k
      · apply ih
        simpa [recognizedKey, h₁] using h0
      · by_cases h₂ : k < g
        · exfalso
          simpa [recognizedKey, h₁, h₂] using h0
        · have heq : g = k := by omega
          have hparts : decide (r ∈ reps) = true ∧ checkIso G (graph n r) p = true := by
            simpa [recognizedKey, h₁, h₂, heq] using h0
          have hr : r ∈ reps := of_decide_eq_true hparts.1
          exact ⟨r, hr, checkIso_sound G (graph n r) p hparts.2⟩
  exact aux (key G) table h

def optionExtension {n : Nat} (H : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    SimpleGraph (Option (Fin n)) where
  Adj a b := match a, b with
    | some a, some b => H.Adj a b
    | none, some b => b ∈ S
    | some a, none => a ∈ S
    | none, none => False
  symm := by intro a b; cases a <;> cases b <;> simp_all [H.adj_comm]
  loopless := by intro a; cases a <;> simp

instance {n : Nat} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (S : Finset (Fin n)) : DecidableRel (optionExtension H S).Adj := by
  intro a b
  cases a <;> cases b <;> dsimp [optionExtension] <;> infer_instance

def extension {n : Nat} (H : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    SimpleGraph (Fin (n+1)) :=
  (optionExtension H S).comap finSuccEquivLast

instance {n : Nat} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (S : Finset (Fin n)) : DecidableRel (extension H S).Adj := by
  unfold extension
  infer_instance

def dominatedAttachment (n r : Nat) (S : Finset (Fin n)) : Bool :=
  decide (∃ v : Fin n, v ∈ S ∧ ∀ w : Fin n, w ∈ S →
    w = v ∨ (graph n r).Adj v w)

/-- A two-connected extension has at least two attachment vertices. -/
theorem extension_card_ge_two_of_twoConnected
    {n : Nat} {H : SimpleGraph (Fin n)} {S : Finset (Fin n)}
    (h : IsTwoConnected (extension H S)) : 2 ≤ S.card := by
  obtain ⟨a, b, hab, ha, hb⟩ :=
    BKLPS.External.exists_two_neighbors_of_twoConnected (extension H S) h (Fin.last n)
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl
    · have haS : a ∈ S := by
        simpa [extension, optionExtension] using ha
      have hbS : b ∈ S := by
        simpa [extension, optionExtension] using hb
      by_contra hcard
      have hlt : S.card < 2 := Nat.lt_of_not_ge hcard
      have hle : S.card ≤ 1 := Nat.le_of_lt_succ (by simpa using hlt)
      have heq : a = b := Finset.card_le_one.mp hle a haS b hbS
      have hab' : a ≠ b := by
        intro habab
        exact hab (congrArg Fin.castSucc habab)
      exact hab' heq
    · exact False.elim ((extension H S).loopless _ hb)
  · exact False.elim ((extension H S).loopless _ ha)

/-- Any labeling of a vertex deletion extends to one of the finitely many
attachment sets checked by the certificate. -/
theorem exists_extension_iso {V : Type*} [Fintype V] [DecidableEq V]
    {n : Nat} (G : SimpleGraph V) (u v : V) (hvu : v ≠ u)
    (hsub : closedNeighborhood G u ⊆ closedNeighborhood G v)
    (r : Nat) (e : deleteVertex G u ≃g graph n r) :
    ∃ S : Finset (Fin n), dominatedAttachment n r S = true ∧
      Nonempty (G ≃g extension (graph n r) S) := by
  classical
  let S := Finset.univ.filter fun i => G.Adj u (e.symm i).1
  let vv : Fin n := e.toEquiv ⟨v, hvu⟩
  have huv : G.Adj u v := by
    have hu : u ∈ closedNeighborhood G u := by simp [closedNeighborhood]
    have hv := hsub hu
    simp only [closedNeighborhood, Finset.mem_insert] at hv
    rcases hv with huv | huv
    · exact False.elim (hvu huv.symm)
    · have hrev : G.Adj v u := by simpa [openNeighborhood] using huv
      exact hrev.symm
  have hdom : dominatedAttachment n r S = true := by
    apply decide_eq_true
    refine ⟨vv, ?_, ?_⟩
    · simpa [S, vv] using huv
    · intro w hw
      by_cases hwv : w = vv
      · exact Or.inl hwv
      · right
        rw [← e.toEquiv.apply_symm_apply w]
        apply e.map_rel_iff.mpr
        change G.Adj v (e.toEquiv.symm w).1
        have hwG : G.Adj u (e.toEquiv.symm w).1 := by simpa [S] using hw
        have hwmem : (e.toEquiv.symm w).1 ∈ closedNeighborhood G u := by
          simp [closedNeighborhood, openNeighborhood, hwG, hwG.symm]
        have hvw := hsub hwmem
        have hne : (e.toEquiv.symm w).1 ≠ v := by
          intro h
          apply hwv
          change w = e.toEquiv ⟨v, hvu⟩
          rw [← e.toEquiv.apply_symm_apply w]
          exact congrArg e.toEquiv (Subtype.ext h)
        simp only [closedNeighborhood, Finset.mem_insert] at hvw
        rcases hvw with hv_eq | hv_adj
        · exact False.elim (hne hv_eq)
        · simpa [openNeighborhood] using hv_adj
  refine ⟨S, hdom, ⟨{ toEquiv := adjoinDeletedEquiv u e.toEquiv, map_rel_iff' := ?_ }⟩⟩
  intro a b
  change (optionExtension (graph n r) S).Adj
    (finSuccEquivLast (adjoinDeletedEquiv u e.toEquiv a))
    (finSuccEquivLast (adjoinDeletedEquiv u e.toEquiv b)) ↔ G.Adj a b
  simp only [adjoinDeletedEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  by_cases ha : a = u <;> by_cases hb : b = u
  · subst a; subst b
    simp [vertexEquivOptionDelete, optionExtension]
  · subst a
    simp [vertexEquivOptionDelete, hb, optionExtension, S]
  · subst b
    simp [vertexEquivOptionDelete, ha, optionExtension, S, G.adj_comm]
  · simpa [vertexEquivOptionDelete, ha, hb, optionExtension] using
      (e.map_rel_iff (a := ⟨a, ha⟩) (b := ⟨b, hb⟩))

end BKLPS.External.OrderTenCertificate
