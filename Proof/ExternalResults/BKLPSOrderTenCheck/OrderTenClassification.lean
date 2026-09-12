import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteChecks
import Proof.Theorem6Proof1
import Proof.ExternalResults.BKLPSLemma10

/-! Exhaustive classification below the `2n` threshold, from order five
through order ten. Only the initial 1024 edge sets and the attachments to
the short representative lists are enumerated. Structural lemmas prove
that these extensions cover every possible counterexample. -/

namespace BKLPS.External.OrderTenCertificate

open SimpleGraph

set_option maxHeartbeats 0

universe u

def Covers (n : Nat) (reps : List Nat) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    Fintype.card V = n → IsTwoConnected G →
    szegedWienerGap G < (2 * n : ℤ) →
    ∃ r ∈ reps, Nonempty (G ≃g graph n r)

private theorem covers5 : Covers.{u} 5 reps5 := by
  intro V _ _ G hcard htwo hgap
  classical
  let K := G.overFin hcard
  let e := G.overFinIso hcard
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hKtwo := (isoIsTwoConnected e).mp htwo
  have hKgap : szegedWienerGap K < (10 : ℤ) := by
    rw [isoSzegedWienerGap e]
    simpa using hgap
  let C := codedGraph (graphCode K)
  have hKC : Nonempty (K ≃g C) := by
    rw [show C = K by exact codedGraph_graphCode K]
    exact ⟨SimpleGraph.Iso.refl⟩
  obtain ⟨eKC⟩ := hKC
  have htwoCode : IsTwoConnected C := (isoIsTwoConnected eKC).mp hKtwo
  have htwoBool : isTwoConnectedBool C = true :=
    (isTwoConnectedBool_eq_true C).mpr htwoCode
  have hc := baseCheck (graphCode K)
  have hrecognize := hc htwoBool
    (by
      have hconnCode : C.Connected := htwoCode.2.1
      rw [cachedGap_eq, finiteGap_eq _ hconnCode]
      exact (by
        calc
          szegedWienerGap C = szegedWienerGap K := isoSzegedWienerGap eKC
          _ < 10 := hKgap))
  obtain ⟨r, hr, ⟨f⟩⟩ := recognized_sound C reps5 table5 hrecognize
  exact ⟨r, hr, ⟨f.comp (eKC.comp e)⟩⟩

private theorem coversExceptional {n : Nat} [NeZero n]
    (reps : List Nat) (table : List (Nat × Nat × Nat))
    (hc : exceptionalCheck n reps table = true)
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hcard : Fintype.card V = n) (hexc : IsExceptional G) :
    ∃ r ∈ reps, Nonempty (G ≃g graph n r) := by
  simp only [exceptionalCheck, Bool.and_eq_true] at hc
  rcases hexc with h | h | h
  · unfold IsomorphicToKn at h
    rw [hcard] at h
    obtain ⟨e⟩ := h
    obtain ⟨r, hr, ⟨f⟩⟩ := recognized_sound _ reps table hc.1.1
    exact ⟨r, hr, ⟨f.comp e⟩⟩
  · unfold IsomorphicToKnt at h
    rw [hcard] at h
    obtain ⟨e⟩ := h
    obtain ⟨r, hr, ⟨f⟩⟩ := recognized_sound _ reps table hc.1.2
    exact ⟨r, hr, ⟨f.comp e⟩⟩
  · unfold IsomorphicToKnt at h
    rw [hcard] at h
    obtain ⟨e⟩ := h
    obtain ⟨r, hr, ⟨f⟩⟩ := recognized_sound _ reps table hc.2
    exact ⟨r, hr, ⟨f.comp e⟩⟩

/-- Low-gap graphs must be exceptional or have a dominated deletion that
is 2-connected, noncomplete, and itself below the smaller threshold. -/
lemma coversStep (n : Nat) (hn : 5 ≤ n)
    (previous next : List Nat) (table : List (Nat × Nat × Nat))
    (hprevious : Covers.{u} n previous)
    (hstep : stepCheck n previous next table = true)
    (hsubset : ∀ S : Finset (Fin n), S ∈ allFinsetsFin n)
    (hexc : exceptionalCheck (n+1) next table = true) :
    Covers.{u} (n+1) next := by
  intro V _ _ G hcard htwo hgap
  classical
  by_cases hun : IsUnexceptional G
  · have hnoncomplete : ¬IsomorphicToKn G := fun h => hun (Or.inl h)
    have hnotC5 : ¬IsomorphicToCn G 5 := by
      rintro ⟨e⟩
      have hfive : Fintype.card V = 5 := by simpa [Cn] using e.card_eq
      omega
    by_cases hno : ∀ x y : V, x ≠ y →
        ¬(closedNeighborhood G x ⊆ closedNeighborhood G y)
    · have hlarge := (bklpsLemma10 G htwo hnoncomplete hnotC5 hno).2
      rw [hcard] at hlarge
      omega
    have hexists : ∃ x y : V, x ≠ y ∧
        closedNeighborhood G x ⊆ closedNeighborhood G y := by
      push_neg at hno
      exact hno
    by_cases hgood : ∃ x y : V, x ≠ y ∧
        closedNeighborhood G x ⊆ closedNeighborhood G y ∧
        IsTwoConnected (deleteVertex G x) ∧ ¬IsomorphicToKn (deleteVertex G x)
    · obtain ⟨x, y, hxy, hsub, hdelTwo, hdelNoncomplete⟩ := hgood
      have hdelCard : Fintype.card {z : V // z ≠ x} = n := by
        simp [hcard]
      have hdelta := bklpsLemma7 G x y htwo hxy hsub hdelTwo hdelNoncomplete
      have hdelGap : szegedWienerGap (deleteVertex G x) < (2*n : ℤ) := by
        push_cast at hgap
        omega
      obtain ⟨r, hr, ⟨e⟩⟩ := hprevious (deleteVertex G x) hdelCard hdelTwo hdelGap
      obtain ⟨S, hdom, ⟨f⟩⟩ := exists_extension_iso G x y hxy.symm hsub r e
      have hFtwo := (isoIsTwoConnected f).mp htwo
      have hFgap : cachedGap (extension (graph n r) S) < (2*(n+1) : ℤ) := by
        rw [cachedGap_eq, finiteGap_eq _ hFtwo.2.1, isoSzegedWienerGap f]
        exact hgap
      have hchecked := (List.all_eq_true.mp hstep) r hr
      have hSmem : S ∈ allFinsetsFin n := hsubset S
      have hcheckedS := of_decide_eq_true
        ((List.all_eq_true.mp hchecked) S hSmem)
      have hScard : 2 ≤ S.card := extension_card_ge_two_of_twoConnected hFtwo
      have hrecognized := hcheckedS hScard hdom hFgap
      obtain ⟨s, hs, ⟨g⟩⟩ := recognized_sound _ next table hrecognized
      exact ⟨s, hs, ⟨g.comp f⟩⟩
    · have hdeletions : ∀ x y : V, x ≠ y →
          closedNeighborhood G x ⊆ closedNeighborhood G y →
          IsomorphicToKn (deleteVertex G x) ∨ ¬IsTwoConnected (deleteVertex G x) := by
        intro x y hxy hsub
        by_cases hc : IsomorphicToKn (deleteVertex G x)
        · exact Or.inl hc
        · exact Or.inr fun ht => hgood ⟨x, y, hxy, hsub, ht, hc⟩
      obtain ⟨x, y, hxy, hsub⟩ := hexists
      have hlarge := BKLPS.theorem6Proof1OfFive (n+1) G hcard (by omega)
        hun htwo x y hxy hsub hdeletions
      rw [hcard] at hlarge
      omega
  · exact coversExceptional next table hexc G hcard (Classical.not_not.mp hun)

private theorem covers10 : Covers.{u} 10 reps10 := by
  have h6 : Covers.{u} 6 reps6 :=
    coversStep 5 (by omega) reps5 reps6 table6 covers5 check6.1
      (by
        intro S
        obtain ⟨m, hm⟩ := subsetComplete5 S
        exact List.mem_map.mpr ⟨m.val, by simp [m.isLt], hm⟩) check6.2
  have h7 : Covers.{u} 7 reps7 :=
    coversStep 6 (by omega) reps6 reps7 table7 h6 check7.1
      (by
        intro S
        obtain ⟨m, hm⟩ := subsetComplete6 S
        exact List.mem_map.mpr ⟨m.val, by simp [m.isLt], hm⟩) check7.2
  have h8 : Covers.{u} 8 reps8 :=
    coversStep 7 (by omega) reps7 reps8 table8 h7 check8.1
      (by
        intro S
        obtain ⟨m, hm⟩ := subsetComplete7 S
        exact List.mem_map.mpr ⟨m.val, by simp [m.isLt], hm⟩) check8.2
  have h9 : Covers.{u} 9 reps9 :=
    coversStep 8 (by omega) reps8 reps9 table9 h8 check9.1
      (by
        intro S
        obtain ⟨m, hm⟩ := subsetComplete8 S
        exact List.mem_map.mpr ⟨m.val, by simp [m.isLt], hm⟩) check9.2
  exact @coversStep 9 (by omega) reps9 reps10 table10 h9 check10.1
    (by
      intro (S : Finset (Fin 9))
      obtain ⟨m, hm⟩ := subsetComplete9 S
      exact List.mem_map.mpr ⟨m.val, by simp [m.isLt], hm⟩) check10.2

private theorem reps10_exceptional (r : Nat) (hr : r ∈ reps10) :
    IsExceptional (graph 10 r) := by
  simp only [reps10, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · right; left
    exact checkIso_sound _ (Knt 10 2) 987654321 (by native_decide)
  · right; right
    exact checkIso_sound _ (Knt 10 8) 9087654321 (by native_decide)
  · left
    exact checkIso_sound _ (completeGraph (Fin 10)) 9876543210 (by native_decide)

/-- Every 2-connected graph of order ten below gap twenty is exceptional. -/
theorem orderTenBound {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hcard : Fintype.card V = 10)
    (htwo : IsTwoConnected G) (hun : IsUnexceptional G) :
    szegedWienerGap G ≥ (20 : ℤ) := by
  by_contra h
  have hsmall : szegedWienerGap G < (2*10 : ℤ) := by omega
  obtain ⟨r, hr, ⟨e⟩⟩ := covers10 G hcard htwo hsmall
  exact hun ((isoIsExceptional e).mpr (reps10_exceptional r hr))

end BKLPS.External.OrderTenCertificate
