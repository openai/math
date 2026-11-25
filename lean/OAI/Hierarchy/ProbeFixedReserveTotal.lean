import OAI.Hierarchy.ProbeFixedReleasedBits
import OAI.Hierarchy.ProbeCatalystDateTotal
import OAI.Hierarchy.ProtocolRAMCalendarWhole

namespace OAI
/-! # Terminal accounting for the actual reserved and used catalyst-bit banks -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe CatalystArchive ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory CatalogueRows
open scoped BigOperators Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dest : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dest owners
local notation "fmt" => v.nativeFormats P z width
local notation "rec" => v.receipts P z width r banks src tab dest owners
local notation "sink" => P.catalogue.sink r banks src tab dest owners
local notation "G" => Columns z (2^v.W)×Fin k

/-- Each used tally is the value in the native scatter's used bank, at the
physical owner of the two radius wires printed by the terminal catalogue. -/
theorem reserve_receipt {count : ℕ} (L : OwnerLedger) (m : Memory W)
    (history : Dates C m L (v.releasedBase P z width) count width)
    (keys : G≃Fin count) (a : ReserveUse.Archive) (reserve : ℕ)
    (site : Fin (recordCount v.mesh (CatalystArchive.issued history))→Fin count) (archiveMem : Memory W)
    {I : Type*} [Fintype I] (core : I→List (Fin P.catalogue.rows)) (center : G→List (Fin P.catalogue.rows))
    (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ)
    (ready : Whole.Reconciliation sink a reserve site (debit v.mesh (CatalystArchive.issued history)) enum ci keys archiveMem)
    (shape : ∀u,.attempt u∈events v.mesh→L.rows (.attempt u)=(fmt u).pricedArea.occurrences)
    (widthFits : width<2^W) (admitted : Calendar.mounted C (events (C).mesh) m) :
    let charged:=fun ev=>(rec (run C (events (C).mesh) m) ev).releasedBits
    let result:=ReserveUse.output a banks reserve site (debit v.mesh (CatalystArchive.issued history)) archiveMem
    let used:=fun j : G=>RouteSettlement.actual banks.used result (keys j).val
    ((events v.mesh).map charged).sum=∑j,used j ∧ ∀j,used j≤reserve := by
  intro charged result used
  constructor
  · exact dated_total_used v.mesh (CatalystArchive.issued history) charged keys a banks reserve site archiveMem
      ready.archive ready.usedSize ready.reserveSize ready.funded ready.word
      (v.released_clock P z width r banks src tab dest owners L m history shape widthFits admitted)
  · exact dated_native_used_le v.mesh (CatalystArchive.issued history) keys a banks reserve site archiveMem
      ready.archive ready.usedSize ready.reserveSize ready.funded ready.word

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
