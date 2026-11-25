import OAI.Hierarchy.TaggedWidePathRoleCells
import OAI.Hierarchy.TaggedWideBranchEndpointPlacement
import OAI.Hierarchy.TaggedWideFundedInitialAmounts
import OAI.Hierarchy.TaggedWideFundedBoundary
import OAI.Hierarchy.TaggedWideFundedCursorRows
import OAI.Hierarchy.TaggedWireFundedContinuation

namespace OAI
/-! # The original site-bit placements of a complete signed categorical path -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets WireTelescope Tagged CalendarTape
open CoreBoard.PhysicalTerm Filter
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 4500000
set_option cleanup.letToHave false
attribute [local irreducible] Nat.pow

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (h width size : ℕ)
    (π : Equiv.Perm (Tagged.Row h)) (seed : Boot.Tape h (2^v.W))
    (age : v.wideStockHeight ≤ h) (budget : v.keepLimit*width+1 ≤ 2^h) (small : width ≤ 2^h)
    (expanse : v.wideFundedSize h width v.maxBits ≤ size) (late : v.reportHeight ≤ h)
    (room : v.ReportWordRoom h width)
local notation "reader" => v.wideSelector h width age budget small
local notation "slots" => (reader).format.slot
local notation "es" => events v.mesh
local notation "start" => v.wideOrigin h width size seed π
local notation "table" => v.widePlacement h width
local notation "ceiling" => (v.privateArena table h width).endAddress v.mesh
local notation "stock" => v.fixedTerminalStock table h width
local notation "w" => Native.wordBits h (2^v.W) Native.copies
variable (j : Path slots es start)
local notation "raw" => (reader).format.windows.header es (encode slots es start j) seed
local notation "tape" => v.wideFundedRaw h width v.maxBits raw
local notation "checkout" => v.wideSignedCheckoutAt h width size stock v.radius π.symm
  (wideRouteOrder h (2^v.W) k) tape
local notation "pathReport" => v.wide_reported_path h width size π seed age budget small expanse late room j


open ProbeStage.CoreBoard.HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical
local notation "wire" => WireTelescope.CalendarTape.Prefix.atWidth («slot»:=slots) (events:=es) (x₀:=start) (S:=siteLast h (2^v.W) k+1) (fun {_ _} path => v.wideCursorWidth h width size π seed age budget small path)
local notation "arenaRoom" => (v.wide_funded_extent h width v.maxBits).trans expanse
local notation "cap" c => HistoryRoles.ceiling v.sampler (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh c v.keepLimit (CatalystArchive.fuel v.mesh) width
variable (unitCost:ℕ)
    (replay:v.cursorReplayHeight≤h) (measure:v.wideDatedLedgerHeight≤h)
    (bounded : ∀(perm:Equiv.Perm (Fin (2^h))) (mem:Boot.Tape h (2^v.W)),
      let o:=wideRouteOrder h (2^v.W) k
      let m:=v.wideSignedMidAt h width size stock v.radius perm o mem
      let c:=v.wideSignedCheckoutAt h width size stock v.radius perm o mem
      c ceiling=0→v.DatedWireFits h width perm m c unitCost)

local notation "records" => v.widePathRoles h width size π seed age budget small expanse late room j unitCost replay measure bounded
local notation "allRecords" => fun (l : WireTelescope.CalendarTape.Path slots es start) =>v.widePathRoles h width size π seed age budget small expanse late room l
  unitCost replay measure bounded
local notation "total" => fun (c : WireTelescope.CalendarTape.Prefix.Cursor slots es start) =>v.wide_funded_continuation h width size arenaRoom π seed age budget small c.path
local notation "current" => WireTelescope.CalendarTape.Prefix.atCursor (WireTelescope.CalendarTape.Prefix.start : WireTelescope.CalendarTape.Prefix slots es start es start)
local notation "qty" => EntryOrder.sourceWidth v.sampler π v.depth (records).mark width (fuel v.mesh*width)
local notation "pin" => v.widePathCells h width size π seed age budget small expanse late room j
  unitCost replay measure bounded
local notation "head" => v.wide_cursor_head h width size arenaRoom π seed age budget small
local notation "sumWidth" => EntryOrder.source_aggregate («w»:=width) (R:=fuel v.mesh*width)
  v.sampler π v.depth (records).mark (records).order

theorem widePathRoles_first (e:Fin (records).count) : (records).bits 0 e=qty ((records).order e) := by
  apply v.wide_dated_first h width size π.symm raw (records).mark arenaRoom age budget small

theorem widePath_first_room (e:Fin (records).count) (side:Bool) :
    qty ((records).order e)≤(cap unitCost) (named v.sampler π.symm v.depth (records).mark
      (records).exclusive (records).order (e,side)) := by
  rw [←v.widePathRoles_first h width size π seed age budget small expanse late room j unitCost replay measure bounded e]
  exact (records).fits 0 e side

local notation "fit" => v.widePath_first_room h width size π seed age budget small expanse late room j
  unitCost replay measure bounded

/-- Exact placement of the time-zero state of this admitted path at the
fixed public exterior ports used by the matching equality cells. -/
theorem widePath_cells_first :
    pin current=(NamedAperture.transport (head).symm).toEmbedding.trans
      ((NamedAperture.transport (sumWidth).symm).toEmbedding.trans
        (statePlace v.sampler π.symm v.depth (records).mark (records).exclusive (records).order
          (qty ∘ (records).order) (cap unitCost) fit)) := by
  exact BranchRoles.endpoint_mapping total allRecords j 0 current (WireTelescope.CalendarTape.Prefix.boundaryIndex_zero j) _
    (funext (v.widePathRoles_first h width size π seed age budget small expanse late room j unitCost replay measure bounded))
    _ sumWidth head fit

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
