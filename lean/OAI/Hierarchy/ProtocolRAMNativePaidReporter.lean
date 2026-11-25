import OAI.Hierarchy.ProtocolRAMNativeReserveSink
import OAI.Hierarchy.ProtocolRAMCalendarVerdict
import OAI.Hierarchy.ProtocolRAMPaidWidthCore

namespace OAI
/-! # Native sequence for the priced calendar and the reserve reporter -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
variable {W q d r edges : ℕ}

/-- The checked calendar, linear positive-width aggregation, external catalyst
reconciliation, and residual route reporter are one chronological native program. -/
def paidReporter (C : Chart W q d) (flag : ℕ) (f : Sink r edges) (src : ℕ) (ss : List PaidWidths.Slice)
    (a : ReserveUse.Archive) (count n reserve : ℕ) : Procedure W :=
  (((checked C flag).seq (PaidWidths.native W edges src f.banks.width ss)).seq
    (ReserveUse.native W a f.banks count n reserve)).seq (f.native W)

def paidReporterTime (C : Chart W q d) (f : Sink r edges) (ss : List PaidWidths.Slice) (a : ReserveUse.Archive)
    (count n reserve : ℕ) := checkedCost C+PaidWidths.clock f.banks.width edges ss+ReserveUse.clock a f.banks count n reserve+f.clock

theorem paidReporter_cheap (C : Chart W q d) (flag : ℕ) (f : Sink r edges) (src : ℕ) (ss : List PaidWidths.Slice)
    (a : ReserveUse.Archive) (count n reserve : ℕ) : CheapCode (paidReporter C flag f src ss a count n reserve) :=
  @cheap_seq W _ (f.native W)
    (@cheap_seq W _ (ReserveUse.native W a f.banks count n reserve)
      (@cheap_seq W (checked C flag) (PaidWidths.native W edges src f.banks.width ss)
        (@checked_cheap W q d C flag) (@PaidWidths.cheap W edges src f.banks.width ss))
      (@ReserveUse.cheap W a f.banks count n reserve))
    (@RouteSettlement.reporter_cheap W f.source f.table f.destination edges r f.banks f.owners f.geometry)

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
