import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteChecksCore
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep5Rep0
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep5Rep1
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep5Rep2
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep5Rep3
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep5Rep4
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep5Rep5
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep6Rep0
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep6Rep1
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep6Rep2
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep6Rep3
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep6Rep4
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep6Rep5
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep6Rep6
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep6Rep7
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep6Rep8
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep6Rep9
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep6Rep10
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep6Rep11
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep6Rep12
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep6Rep13
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep6Rep14
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep6Rep15
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep7Rep0
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep7Rep1
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep7Rep2
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep7Rep3
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep7Rep4
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep7Rep5
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep7Rep6
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep7Rep7
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep7Rep8
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep7Rep9
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep7Rep10
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep7Rep11
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep7Rep12
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep7Rep13
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep8Rep0
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep8Rep1
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep8Rep2
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep8Rep3
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep8Rep4
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep8Rep5
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep8Rep6
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep8Rep7
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep9Rep0
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep9Rep1
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep9Rep2
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep9Rep3
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep9Rep4
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep9Rep5
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep9Rep6
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep9Rep7
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep9Rep8
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckStep9Rep9
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckExceptional6
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckExceptional7
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckExceptional8
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckExceptional9
import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteCheckExceptional10

namespace BKLPS.External.OrderTenCertificate

theorem stepCheck5 : stepCheck 5 reps5 reps6 table6 = true := by
  simpa [stepCheck, reps5] using (show stepCheckOne 5 223 reps6 table6 = true ∧ stepCheckOne 5 236 reps6 table6 = true ∧ stepCheckOne 5 239 reps6 table6 = true ∧ stepCheckOne 5 255 reps6 table6 = true ∧ stepCheckOne 5 511 reps6 table6 = true ∧ stepCheckOne 5 1023 reps6 table6 = true from ⟨stepCheck5Rep0, ⟨stepCheck5Rep1, ⟨stepCheck5Rep2, ⟨stepCheck5Rep3, ⟨stepCheck5Rep4, stepCheck5Rep5⟩⟩⟩⟩⟩)

theorem stepCheck6 : stepCheck 6 reps6 reps7 table7 = true := by
  simpa [stepCheck, reps6] using (show stepCheckOne 6 3311 reps7 table7 = true ∧ stepCheckOne 6 3327 reps7 table7 = true ∧ stepCheckOne 6 3583 reps7 table7 = true ∧ stepCheckOne 6 4095 reps7 table7 = true ∧ stepCheckOne 6 5375 reps7 table7 = true ∧ stepCheckOne 6 6380 reps7 table7 = true ∧ stepCheckOne 6 6383 reps7 table7 = true ∧ stepCheckOne 6 8191 reps7 table7 = true ∧ stepCheckOne 6 9455 reps7 table7 = true ∧ stepCheckOne 6 9727 reps7 table7 = true ∧ stepCheckOne 6 11775 reps7 table7 = true ∧ stepCheckOne 6 13548 reps7 table7 = true ∧ stepCheckOne 6 13551 reps7 table7 = true ∧ stepCheckOne 6 16383 reps7 table7 = true ∧ stepCheckOne 6 19711 reps7 table7 = true ∧ stepCheckOne 6 32767 reps7 table7 = true from ⟨stepCheck6Rep0, ⟨stepCheck6Rep1, ⟨stepCheck6Rep2, ⟨stepCheck6Rep3, ⟨stepCheck6Rep4, ⟨stepCheck6Rep5, ⟨stepCheck6Rep6, ⟨stepCheck6Rep7, ⟨stepCheck6Rep8, ⟨stepCheck6Rep9, ⟨stepCheck6Rep10, ⟨stepCheck6Rep11, ⟨stepCheck6Rep12, ⟨stepCheck6Rep13, ⟨stepCheck6Rep14, stepCheck6Rep15⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

theorem stepCheck7 : stepCheck 7 reps7 reps8 table8 = true := by
  simpa [stepCheck, reps7] using (show stepCheckOne 7 107759 reps8 table8 = true ∧ stepCheckOne 7 131071 reps8 table8 = true ∧ stepCheckOne 7 167935 reps8 table8 = true ∧ stepCheckOne 7 210159 reps8 table8 = true ∧ stepCheckOne 7 238831 reps8 table8 = true ∧ stepCheckOne 7 262143 reps8 table8 = true ∧ stepCheckOne 7 511231 reps8 table8 = true ∧ stepCheckOne 7 524287 reps8 table8 = true ∧ stepCheckOne 7 566511 reps8 table8 = true ∧ stepCheckOne 7 570607 reps8 table8 = true ∧ stepCheckOne 7 636143 reps8 table8 = true ∧ stepCheckOne 7 1048575 reps8 table8 = true ∧ stepCheckOne 7 1085439 reps8 table8 = true ∧ stepCheckOne 7 2097151 reps8 table8 = true from ⟨stepCheck7Rep0, ⟨stepCheck7Rep1, ⟨stepCheck7Rep2, ⟨stepCheck7Rep3, ⟨stepCheck7Rep4, ⟨stepCheck7Rep5, ⟨stepCheck7Rep6, ⟨stepCheck7Rep7, ⟨stepCheck7Rep8, ⟨stepCheck7Rep9, ⟨stepCheck7Rep10, ⟨stepCheck7Rep11, ⟨stepCheck7Rep12, stepCheck7Rep13⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

theorem stepCheck8 : stepCheck 8 reps8 reps9 table9 = true := by
  simpa [stepCheck, reps8] using (show stepCheckOne 8 8388607 reps9 table9 = true ∧ stepCheckOne 8 66097151 reps9 table9 = true ∧ stepCheckOne 8 69772527 reps9 table9 = true ∧ stepCheckOne 8 86549743 reps9 table9 = true ∧ stepCheckOne 8 94942447 reps9 table9 = true ∧ stepCheckOne 8 134217727 reps9 table9 = true ∧ stepCheckOne 8 170439919 reps9 table9 = true ∧ stepCheckOne 8 268435455 reps9 table9 = true from ⟨stepCheck8Rep0, ⟨stepCheck8Rep1, ⟨stepCheck8Rep2, ⟨stepCheck8Rep3, ⟨stepCheck8Rep4, ⟨stepCheck8Rep5, ⟨stepCheck8Rep6, stepCheck8Rep7⟩⟩⟩⟩⟩⟩⟩)

theorem stepCheck9 : stepCheck 9 reps9 reps10 table10 = true := by
  simpa [stepCheck, reps9] using (show stepCheckOne 9 1073741823 reps10 table10 = true ∧ stepCheckOne 9 12250035439 reps10 table10 = true ∧ stepCheckOne 9 17514401791 reps10 table10 = true ∧ stepCheckOne 9 17518077167 reps10 table10 = true ∧ stepCheckOne 9 17534854383 reps10 table10 = true ∧ stepCheckOne 9 17543247087 reps10 table10 = true ∧ stepCheckOne 9 21829821679 reps10 table10 = true ∧ stepCheckOne 9 34359738367 reps10 table10 = true ∧ stepCheckOne 9 34636562431 reps10 table10 = true ∧ stepCheckOne 9 68719476735 reps10 table10 = true from ⟨stepCheck9Rep0, ⟨stepCheck9Rep1, ⟨stepCheck9Rep2, ⟨stepCheck9Rep3, ⟨stepCheck9Rep4, ⟨stepCheck9Rep5, ⟨stepCheck9Rep6, ⟨stepCheck9Rep7, ⟨stepCheck9Rep8, stepCheck9Rep9⟩⟩⟩⟩⟩⟩⟩⟩⟩)

theorem allChecks :
    (stepCheck 5 reps5 reps6 table6 = true ∧
      exceptionalCheck 6 reps6 table6 = true) ∧
    (stepCheck 6 reps6 reps7 table7 = true ∧
      exceptionalCheck 7 reps7 table7 = true) ∧
    (stepCheck 7 reps7 reps8 table8 = true ∧
      exceptionalCheck 8 reps8 table8 = true) ∧
    (stepCheck 8 reps8 reps9 table9 = true ∧
      exceptionalCheck 9 reps9 table9 = true) ∧
    (stepCheck 9 reps9 reps10 table10 = true ∧
      exceptionalCheck 10 reps10 table10 = true) := by
  exact ⟨⟨stepCheck5, exceptionalCheck6⟩,
    ⟨stepCheck6, exceptionalCheck7⟩,
    ⟨stepCheck7, exceptionalCheck8⟩,
    ⟨stepCheck8, exceptionalCheck9⟩,
    ⟨stepCheck9, exceptionalCheck10⟩⟩

theorem check6 : stepCheck 5 reps5 reps6 table6 = true ∧
    exceptionalCheck 6 reps6 table6 = true := allChecks.1
theorem check7 : stepCheck 6 reps6 reps7 table7 = true ∧
    exceptionalCheck 7 reps7 table7 = true := allChecks.2.1
theorem check8 : stepCheck 7 reps7 reps8 table8 = true ∧
    exceptionalCheck 8 reps8 table8 = true := allChecks.2.2.1
theorem check9 : stepCheck 8 reps8 reps9 table9 = true ∧
    exceptionalCheck 9 reps9 table9 = true := allChecks.2.2.2.1
theorem check10 : stepCheck 9 reps9 reps10 table10 = true ∧
    exceptionalCheck 10 reps10 table10 = true := allChecks.2.2.2.2

end BKLPS.External.OrderTenCertificate
