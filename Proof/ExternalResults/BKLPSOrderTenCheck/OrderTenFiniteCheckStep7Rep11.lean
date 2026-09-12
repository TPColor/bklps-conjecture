import Proof.ExternalResults.BKLPSOrderTenCheck.OrderTenFiniteChecksCore

namespace BKLPS.External.OrderTenCertificate

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
set_option compiler.maxRecInlineIfReduce 0 in
set_option compiler.extract_closed true in
theorem stepCheck7Rep11 : stepCheckOne 7 1048575 reps8 table8 = true := by
  native_decide

end BKLPS.External.OrderTenCertificate
