import OAI.Hierarchy.ProbeFixedReleasedBits
import OAI.Hierarchy.ProbeFixedPrintedRole
import OAI.Hierarchy.ProtocolRAMCatalystStripDates

namespace OAI
/-! # Every signed release in the terminal invoice is a real catalyst occurrence -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe CatalystArchive ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory PortPadding CatalogueRows.StripPorts
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dest : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "D" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
local notation "C" => v.nativeChart P z width r banks src tab dest owners
local notation "fmt" => v.nativeFormats P z width
local notation "H" => StripChart.header F (v.nativeBoards P z width)

private theorem printed_index (a : Attempt) (row : Fin (H a).rows) (port : Fin D) :
    (v.roleOccurrence P z width a row port).val = port.val + D * row.val := rfl

set_option maxHeartbeats 1000000 in
theorem dated_supply {count : ℕ} (L : OwnerLedger) (m : Memory W)
    (history : Dates C m L (v.releasedBase P z width) count width)
    (shape : ∀a,.attempt a∈events v.mesh→L.rows (.attempt a)=(fmt a).pricedArea.occurrences)
    (original : ∀a,∀ha : Event.attempt a∈events v.mesh,AttemptPorts N v.depth k (H a).rows D a (history a ha).entry)
    (room : width<2^W) (admitted : Calendar.mounted C (events (C).mesh) m) (a : Attempt) (live : .attempt a∈events v.mesh)
    (i : Fin (fmt a).pricedArea.occurrences)
    (on : ((run C (events (C).mesh) m) ((fmt a).pricedArea.direct+(fmt a).pricedArea.occurrences+i.val)).val≠0) :
    v.paidSupply z a (v.occurrencePort P z width a i).val=true := by
  have rows := (history a live).shape.trans (shape a live)
  let j := (finCongr rows).symm i
  have source := v.released_entry_word P z width r banks src tab dest owners L m history shape room admitted a live j
  have funded : 0<(history a live).entry.bits j :=
    Nat.pos_of_ne_zero fun zero => on (source.trans zero)
  have port := original a live
  cases a with
  | outer u h =>
    obtain ⟨row,c,axis,idx⟩:=port j funded
    let role : PayloadRole N k := .catalyst c axis
    let portId : Fin D := inject (Nat.le_max_left _ _) ((Fintype.equivFin (PayloadRole N k)) role)
    let entry := v.roleOccurrence P z width (.outer u h) row portId
    have numeric : i.val=portId.val + D * row.val := idx
    have atPort : i=entry := Fin.ext (numeric.trans (v.printed_index P z width (.outer u h) row portId).symm)
    rw [atPort]
    exact v.payload_supply P z width u h row role
  | inner u h s t =>
    obtain ⟨row,c,axis,idx⟩:=port j funded
    let role : PurchasedRole v.depth k := .catalyst c axis
    let portId : Fin D := inject (Nat.le_max_right _ _) ((Fintype.equivFin (PurchasedRole v.depth k)) role)
    let entry := v.roleOccurrence P z width (.inner u h s t) row portId
    have numeric : i.val=portId.val + D * row.val := idx
    have atPort : i=entry := Fin.ext (numeric.trans (v.printed_index P z width (.inner u h s t) row portId).symm)
    rw [atPort]
    exact v.purchased_supply P z width u h s t row role

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
