import OAI.Computability.BorderVNP.DiagonalWriterPostRequest

/-! # Bind the selected physical owner in a native post-call proof -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM BorderVNP.Cube Evaluator Evaluator.ScheduleClock SignedTaskArena CellSparse CellSparse.Packet
open CellSparse.Packet.Source CellPacket CellPacket.Supplement DiagonalTallyAllocation SparseExterior TypedTaskBuilder

open BorderVNP.Cube.Physical BorderVNP.Cube.TeamRowClock BorderVNP.Cube.TeamRowSources
open Crossing Packing.CellAddresses Packing.Directory DiagonalTallyCellReports
open Diagonal.ExternalSew.Fragments CellPacketGeometry CellDispatch Packing.BundleDirectory
open DiagonalTallyCellReports.ReportDirectory

open TeamContraction VPVNP BurstRAM TeamContraction.ProcessorSlots BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows Scatter.Assignment FiniteEvaluator

variable {teams n w r₀ clocks pinBits link inner : ℕ} {Edge : Type} {G : Wiring teams r₀ clocks pinBits link inner n Edge}
    {col : Fin pinBits → Bool} {ext : Exterior teams r₀ link → Bool}
    {pubs : Fin (teams+1) → Arg → Word w} {regs : Fin (teams+1) → Bank w} {args : Fin (teams+1) → UnitAddresses}
    (a : SignedTaskArena.Layout)
    (nodes : (i : Fin (teams+1)) → BootedPinStart SparseExterior.driver G pubs regs args col ext i)
    (active : PinStart.JointPrefix a.id (fun i => (nodes i).start)) (agent : Fin (teams+1))

open RoutingISA.Transmission TeamContraction.ProcessorSlots TeamContraction.JointHeader
open PackedHistoryCircuit RoutingISA.CompactMachine Diagonal.Layout Routing DiagonalTallyPacketEmit TeamScales BorderVNP.Cube.Tally
set_option maxHeartbeats 3300000
set_option maxRecDepth 7500

variable {A : Type} [Fintype A] {D : LengthDeclaration a.cube.n a.cube.header.d}
    {label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d}
    {recv : A → Fin a.cube.cells} {incoming : A → ℕ}
variable {wire : WireLayout (teams+1) r₀ link} {common : List Bool}
  {publicAt : HeaderExterior wire common → Fin (teams+1) → Arg → Word w}
  {macroAt : HeaderExterior wire common → Fin (teams+1) → TeamOpcode.Macros w 8}
  {regsAt : HeaderExterior wire common → Fin (teams+1) → Bank w}
  {memAt : HeaderExterior wire common → Fin (teams+1) → Memory w}
  {F : PreparationFrame G wire a.cube D common col publicAt macroAt regsAt memAt}
  {origin : HeaderExterior wire common}
  {proto : DiagonalTallyPacketEmit.Frame} {amount : ℕ}
  {route : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) (greedyOwner teams a.cube.b a.cube.s label recv incoming)}

variable (owned : F.ReturnedOwnershipAt a origin ext proto amount route (PinStart.ownedVisits (ar:=a.cube) (fun i => (nodes i).start) active))
variable {a nodes active agent}

set_option quotPrecheck false
local notation3 (prettyPrint := false) "bound(" request "," receipt ")" =>
  (fun fit cells emission data patch row (E I P : Type) (points : Fintype P) entries layout home payload
      external supply privateWidth digits cursor seed =>
    (request).run fit cells emission data patch row E I P A points inferInstance D label recv incoming
      entries layout home payload external supply privateWidth digits cursor seed wire common publicAt macroAt regsAt memAt
      F origin proto amount route receipt)

set_option maxHeartbeats 1500000 in
/-- The report and call operands still to be read after the source replay and its
actual ownership history have already been bound. -/
def WriterPostRequest.AtOwner (request : WriterPostRequest a nodes active agent) : Prop := type_of% bound(request,owned)

set_option maxHeartbeats 1500000 in
/-- Fill in the source replay and its genuine ownership reading, preserving all
remaining dependent report and cell inputs. -/
theorem WriterPostRequest.runAtOwner (request : WriterPostRequest a nodes active agent)
  (owned : F.ReturnedOwnershipAt a origin ext proto amount route (PinStart.ownedVisits (ar:=a.cube) (fun i => (nodes i).start) active)) :
    request.AtOwner (F:=F) (origin:=origin) (label:=label) (recv:=recv) (incoming:=incoming) := bound(request,owned)

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
