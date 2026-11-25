import OAI.Computability.BorderVNP.CellLocalFinish
import OAI.Computability.BorderVNP.CellVisitWidth
import OAI.Computability.BorderVNP.DiagonalTallyCellReports

/-! # Local subtotal word widths in the actual supplied bit layout -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit.Finish

open CellMacro.Generator DiagonalTallyCellReports

/-- The binary field for counts up to and including the cap uses exactly its bit length. -/
theorem countWidth_eq (cap : ℕ) : Nat.clog 2 (cap+1) = cap.size := by
  apply eq_of_forall_ge_iff
  intro k
  rw [Nat.size_le,Nat.clog_le_iff_le_pow (by decide)]
  omega

/-- If the common count cap is polynomially bounded, each canonical source
report has logarithmic width, independently of how many sites and reports exist. -/
theorem reportWidth_le {base gadgets cap n B j r : ℕ} {bits : List ℕ}
    (hr : 1 ≤ r) (hcap : cap ≤ B*(n+2)^j)
    (h : bits ∈ countFields base gadgets (Nat.clog 2 (cap+1))) :
    bits.length ≤ (B.size+j)*(TeamScales.logWidth r n+1) := by
  rw [countField_length _ _ _ h,countWidth_eq]
  have hc := size_of_polynomial_field hcap
  have hw := size_le_logWidth n r hr
  have hm := Nat.mul_le_mul_left j (Nat.add_le_add_right hw 1)
  have hb : B.size ≤ B.size*(TeamScales.logWidth r n+1) := Nat.le_mul_of_pos_right _ (by omega)
  rw [Nat.add_mul]
  omega

/-- For a complete cell whose report bank is the canonical sequence of count
fields, the field bound applies to every actual report passed to the printer. -/
theorem directoryReportWidth_le (D : Directory) {base gadgets cap n B j r : ℕ} (hr : 1 ≤ r)
    (hcap : cap ≤ B*(n+2)^j)
    (layout : D.reportedCounts = countFields base gadgets (Nat.clog 2 (cap+1))) :
    ∀ bits ∈ D.reportedCounts, bits.length ≤ (B.size+j)*(TeamScales.logWidth r n+1) := by
  rw [layout]
  exact fun _ h => reportWidth_le hr hcap h

end CellSparse.Packet.Emit.Finish

end BorderVNP
end Computability
end OAI
