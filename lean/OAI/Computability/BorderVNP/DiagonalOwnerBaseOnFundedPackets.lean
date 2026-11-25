import OAI.Computability.BorderVNP.DiagonalSuppliedAtRosterRoutes
import OAI.Computability.BorderVNP.DiagonalOwnerBaseAtRoutes

/-! # Owner tables on the native calls of the actual funded packets -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine Routing JointHeader
open CellMacro.Generator BorderVNP.Cube

variable {R r t d link inner n w reserve axes groups cap dim tally box lanes selectors symbols : ℕ}
    {Edge Hist : Type} (id : TableEntry axes box lanes selectors symbols → ℕ)
    (G : Wiring R r t d link inner n Edge) (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (pin : Fin d → Bool) (L : WireLayout (R+1) r link)
    (headerWidth : L.header=PositiveFields.width reserve axes groups cap (R+1) dim tally)
    (code : Hist ↪ (Fin reserve → Bool))
    (args : Fin (R+1) → UnitAddresses) (fixed : Block (R+1)) (hw : 0<w)
    (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver G pub reg args pin x.val u)
    (decoder : PreparedHistoryDecoder SparseExterior.driver id G pub reg pin L headerWidth code args fixed hw size base fit B)
    (limit burst : ℕ) (privateSize : TeamScales.width n (1/2) ≤ burst)

open Crossing Packing.Inherited Packing.BottomReports Cube.Physical Cube.Physical.NativeAssignments
open DiagonalTallyCellReports RoutingISA.CompactMachine
variable {D nativeGroups : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Hist → Network D P bits} {count : Hist → ℕ}
    (core : ∀ h, CoreDirectory (N h) axes nativeGroups (count h) box lanes selectors R)

variable {id G pub reg pin L headerWidth code args fixed hw size base fit B}
    (roster : SourceRoster core d symbols) (taskBase : ℕ)

variable (routed : decoder.RosterRoutes limit burst privateSize core roster taskBase)

variable {Keys Slots : Hist → Type} {cells : Hist → ℕ}
    (directory : (h : Hist) → CellPacketGeometry.SiteWords.Directory (Keys h) (Slots h) (cells h+1))

local notation3 (prettyPrint := false) "parsedFields" => PreparedFields (Fin d → Bool) Hist (Fin ((R+1)*dim*tally) → Bool)
  (fun h : Hist => (core h).Route symbols) (CoreDirectory.Proposals core roster.charts roster.rows)
local notation3 (prettyPrint := false) "barePrefix" => (x : {ext // PositiveExterior G args pin w ext}) ×
  ((u : Fin (R+1)) → (B x u).start.Prefix id)
local notation3 (prettyPrint := false) "nativeAt(" z ")" => (u : Fin (R+1)) →
  PinStart.SparseSource id (fun t => (B ((z).1) t).start) ((z).2 u)

local notation3 (prettyPrint := false) "routeAt" => (fun h : Hist => (core h).Route symbols)
local notation3 (prettyPrint := false) "reportAt" => CoreDirectory.Proposals core roster.charts roster.rows
private abbrev nativeDomain {X : Sort*} {Y : X → Sort*} (_ : (x : X) → Y x) := X

local notation3 (prettyPrint := false) "launchedPackets" =>
  decoder.suppliedPacketsAtRoute limit burst privateSize core roster taskBase routed directory

local notation3 (prettyPrint := false) "truePlacements" =>
  (fun (f : parsedFields) (z : barePrefix) (ns : nativeAt(z)) =>
    (u : Fin (R+1)) → SavedSparsePlacement (directory f.2.1) (ns u).logicalAt)

local notation3 (prettyPrint := false) "next(" calls ")" => (fun z u => @SelectedCalls.next _ _ _ calls z u)
local notation3 (prettyPrint := false) "team(" calls ")" => supportedTeam id B limit burst privateSize (next(calls))
local notation3 (prettyPrint := false) "prep(" calls ")" =>
  (decoder.supported limit burst privateSize (next(calls)) routeAt reportAt routed).val


local notation3 (prettyPrint := false) "actualCalls(" funds ")" =>
  NativeCalls id B limit burst privateSize ((launchedPackets funds).2)

/-- The public base and owner rows on the actual calls that use the second
component of the complete funded packet submission. -/
noncomputable def PreparedHistoryDecoder.ownerBaseOnFundedPackets (funded : nativeDomain launchedPackets)
    (calls : actualCalls(funded)) :
    {a : parsedFields → Fin (R+1) → ℕ //
      PreparedOwned.OwnerTablesAt (team(calls)) (prep(calls)) (fun h => (core h).cells) roster.team a} :=
  decoder.ownerBaseAtRoutes limit burst privateSize core roster taskBase routed
    truePlacements (launchedPackets funded).1 calls

/-- Every field and every receiving team uses the very pre-call base of the
original reader on which the funded inputs were observed. -/
theorem PreparedHistoryDecoder.ownerBaseOnFundedPackets_address (funded : nativeDomain launchedPackets)
    (calls : actualCalls(funded)) (f : parsedFields) (u : Fin (R+1)) :
    (decoder.ownerBaseOnFundedPackets limit burst privateSize core roster taskBase routed directory funded calls).val f u
      = taskBase := rfl



end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
