import OAI.Computability.BorderVNP.DiagonalReceivedReportExtent
import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomParameters
import OAI.Computability.BorderVNP.PackedFinalCellSupplement
import OAI.Computability.BorderVNP.CellVisitWidth

/-! # The immutable source report fits its native private gap and word -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing Packing.CellAddresses Packing.BottomReports Packing.Inherited
open Site.Programs CellSparse DiagonalTallyCellReports RoutingISA

variable {T C D ns : ℕ} {P J : Type} [Fintype P] [Fintype J] {bits : P → ℕ} {layout : Fin T → ReportLayout}
    (R : ReceivedRows layout C) (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (owner : Fin ns → ℕ) (state : Site.Programs N)
    (host : J ↪ N.Site) (bundle : J → Bundle) (origins : Fin C → List J)
    {M E Z high table rows digitBound : ℕ}
    (bound : ReceivedBounds R N cell siteID owner state host bundle origins M E Z high table rows digitBound)
    (u : Fin T) (i : Fin (R.cells u).length)


open TeamScales
open private small_width from OAI.Computability.BorderVNP.RoutingISATypedPrivateClock

include bound in
/-- The actual tail in an immutable received source row fits the native n² gap
without running a sparse call. The private, supplied and selected report
parts fit the machine word together on that same ordinal. -/
theorem ReceivedBounds.reportGap_word {n r w : ℕ} (hn : 1≤n) (hr : 1≤r)
    (mass : M≤TeamScales.width n (1/5)) (exterior : E≤TeamScales.width n (1/4)) (word : 60*logWidth r n≤w)
    (supply : ((R.cells u).get i).supplied=suppliedSize N (fun v => (cell v).val) (R.order ⟨u,i⟩).val)
    (wires : ((R.cells u).get i).privateWires=FinalCell.privateBits N (fun v => (cell v).val)
      (fun v => (state v).program) (R.order ⟨u,i⟩).val) :
    let row := (R.cells u).get i
    row.tailWidth≤n^2 ∧ row.privateWires+row.supplied+row.tailWidth<2^w := by
  intro row
  let c := R.order ⟨u,i⟩
  let field : SparseExterior.Field := ⟨row.supplied,[],List.replicate row.tailWidth false⟩
  have tail : field.tail.length=row.tailWidth := List.length_replicate
  have cap : field.width+field.tail.length≤E :=
    (bound.fieldInputs R N cell siteID owner state host bundle origins u i field supply tail).2.1
  have packed := SignedTaskArena.report_tail_in_gap field hn cap exterior
  have hw := merged_bank_capacity N (fun v => (state v).program)
    (fun v => (cell v).val) c.val bound.incoming
  have htotal := hw.trans (Nat.mul_le_mul_left 3 (bound.expandedLoad c))
  have hM := mass.trans (small_width hn (1/5) (by norm_num))
  have hE := exterior.trans (small_width hn (1/4) (by norm_num))
  have hnWord : n<2^(logWidth r n) := Nat.size_le.mp (CellMacro.Generator.size_le_logWidth n r hr)
  have pos : 0<logWidth r n := by by_contra! h; rw [Nat.eq_zero_of_le_zero h] at hnWord; omega
  have four : 4*n<2^w := by
    have fourPower : 4*2^logWidth r n=2^(logWidth r n+2) := by rw [pow_add]; ring
    exact (Nat.mul_lt_mul_of_pos_left hnWord (by decide : 0<4)).trans_le
      (fourPower ▸ Nat.pow_le_pow_right (by decide) (show logWidth r n+2≤w by omega))
  change row.supplied+field.tail.length≤E at cap
  have wp : row.privateWires≤3*M := wires ▸ (Nat.le_add_right _ _).trans htotal
  rw [tail] at cap packed
  omega

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
