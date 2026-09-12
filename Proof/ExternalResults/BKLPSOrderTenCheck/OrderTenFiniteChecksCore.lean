import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenCertificate
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenCertificateData

/-! Executable checks, separated from the structural proof so the computed
results are cached in their own module. -/
namespace BKLPS.External.OrderTenCertificate

open SimpleGraph

def subsetMask (n m : Nat) : Finset (Fin n) :=
  Finset.univ.filter fun i => m.testBit i.val

def allFinsetsFin (n : Nat) : List (Finset (Fin n)) :=
  (List.range (2 ^ n)).map (subsetMask n)

def edgeMask5 (m : Nat) : Finset (OrderedEdge 5) :=
  Finset.univ.filter fun e =>
    m.testBit (e.1.2.val * (e.1.2.val - 1) / 2 + e.1.1.val)

def allEdgeSets5 : List (Finset (OrderedEdge 5)) :=
  (List.range 1024).map edgeMask5

def stepCheckOne (n r : Nat) (next : List Nat)
    (table : List (Nat × Nat × Nat)) : Bool :=
  (allFinsetsFin n).all fun S => decide (
    2 ≤ S.card →
    dominatedAttachment n r S = true →
    cachedGap (extension (graph n r) S) < (2 * (n+1) : ℤ) →
    recognized (extension (graph n r) S) next table = true)

def stepCheck (n : Nat) (previous next : List Nat)
    (table : List (Nat × Nat × Nat)) : Bool :=
  previous.all fun r => stepCheckOne n r next table

def exceptionalCheck (n : Nat) [NeZero n] (reps : List Nat)
    (table : List (Nat × Nat × Nat)) : Bool :=
  recognized (completeGraph (Fin n)) reps table &&
    recognized (Knt n 2) reps table && recognized (Knt n (n-2)) reps table

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
set_option compiler.maxRecInlineIfReduce 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
set_option compiler.maxRecInlineIfReduce 0 in
set_option compiler.extract_closed false in
theorem edgeComplete5 : ∀ E : Finset (OrderedEdge 5),
    ∃ m : Fin 1024, edgeMask5 m.val = E := by native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
set_option compiler.maxRecInlineIfReduce 0 in
set_option compiler.extract_closed false in
theorem subsetComplete5 : ∀ S : Finset (Fin 5),
    ∃ m : Fin 32, subsetMask 5 m.val = S := by native_decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
set_option compiler.maxRecInlineIfReduce 0 in
set_option compiler.extract_closed false in
theorem subsetComplete6 : ∀ S : Finset (Fin 6),
    ∃ m : Fin 64, subsetMask 6 m.val = S := by native_decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
set_option compiler.maxRecInlineIfReduce 0 in
set_option compiler.extract_closed false in
theorem subsetComplete7 : ∀ S : Finset (Fin 7),
    ∃ m : Fin 128, subsetMask 7 m.val = S := by native_decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
set_option compiler.maxRecInlineIfReduce 0 in
set_option compiler.extract_closed false in
theorem subsetComplete8 : ∀ S : Finset (Fin 8),
    ∃ m : Fin 256, subsetMask 8 m.val = S := by native_decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
set_option compiler.maxRecInlineIfReduce 0 in
set_option compiler.extract_closed false in
theorem subsetComplete9 : ∀ S : Finset (Fin 9),
    ∃ m : Fin 512, subsetMask 9 m.val = S := by native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
set_option compiler.maxRecInlineIfReduce 0 in
set_option compiler.extract_closed false in
theorem baseCheckList :
    allEdgeSets5.all (fun E => decide (
      isTwoConnectedBool (codedGraph E) = true →
      cachedGap (codedGraph E) < (10 : ℤ) →
      recognized (codedGraph E) reps5 table5 = true)) = true := by
  native_decide

theorem baseCheck :
    ∀ E : Finset (OrderedEdge 5),
      isTwoConnectedBool (codedGraph E) = true →
      cachedGap (codedGraph E) < (10 : ℤ) →
      recognized (codedGraph E) reps5 table5 = true := by
  intro E htwo hgap
  obtain ⟨m, hm⟩ := edgeComplete5 E
  have hall := List.all_eq_true.mp baseCheckList
  have hmem : E ∈ allEdgeSets5 := by
    rw [← hm]
    exact List.mem_map.mpr ⟨m.val, by simp [m.isLt], rfl⟩
  simpa [hm] using of_decide_eq_true (hall _ hmem) htwo hgap


end BKLPS.External.OrderTenCertificate
