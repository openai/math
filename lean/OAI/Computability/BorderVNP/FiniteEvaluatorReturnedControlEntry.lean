import OAI.Computability.BorderVNP.FiniteEvaluatorCubeReturnedHost
import OAI.Computability.BorderVNP.CubeScatterReturnedPadding

/-! # All four control stages on one recovered evaluator memory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open Scatter.Assignment DiagonalTallyPacketEmit FiniteEvaluator Evaluator
open BorderVNP.Crossing Packing CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs
open NativeIntervals HostAddress VPVNP.MotifBase

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
variable {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
variable {group : Fin ar.header.d → Fin (R+1)} {F : TeamRows.Returns (Fin (R+1)) ar w}
variable {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
variable {template : Frame} {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ} {count : ℕ}

variable {dim sites ports cellBits lenBits geometryBits J A geoOrigin m : ℕ} {P σ : Type*} [Fintype P] [Fintype σ] {bits : P → ℕ}
variable (N : Network dim P bits) (cell : N.Site → Fin ar.cells) (aux : N.Site → ℕ)
variable (siteID : N.Site ↪ Fin sites) (edgeID : N.Edge ↪ Fin ar.cables) (portID : P ↪ Fin ports)
variable (geoFields : Fields sites ar.cables ports ar.cells cellBits lenBits geometryBits σ) {x : σ → Bool}
variable {old : Fin J → Fin sites} {live : Fin A → Fin ports}
variable (il : NativeIntervals.Layout) (previous dir : ℕ → ℕ) {ord : N.CrossingEdge cell ≃ Fin m}
variable {row : Fin m ↪o Fin il.count} {label : Fin ar.cells → Label (ar.n+1) ar.header.d} {hz : ar.header.d^(ar.n+1)=il.alphabet}
variable (rows : PhysicalRows N cell il previous ord row Fin.valEmbedding label (productCode ar.n ar.header.d il.alphabet hz))
variable (interval : il.Image previous il.count dir)
variable (cap : ∀ u, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
  (crossWidth N cell ∘ ord.symm) u ≤ ar.header.blocks*(ar.h*ar.b))

include rows interval cap in
/-- The actual returned owned memory is the input of the native four-program
control suffix. Its padding and copy operands come from the same authentic
history. The signed control and stable-sort words refer to the directory
producer's memory, before the data, shared and private packet writers. -/
theorem SharedWriters.returned_control_entry (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    {q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows g group) q) (u : Fin (R+1))
    {controls broadcast width : ℕ} {rr rt : Bank w} {initial last : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory ar.n width (H u).pub (H u).macros rr initial es rt last)
    (ready : DataReady (H u).pub W.dataInput)
    (records : (DataWriter.layout (readings (H u).pub) (readings W.dataInput)).output=ar.records)
    (source : src u=readings W.sharedInput)
    (fit : il.Fits w previous) (fields : il.Fields previous) (atFrame : il.frame=readings (H u).pub 0)
    (space : HostScatter.CableColumns ar il.frame il previous) (widths : il.widths=ar.widthBase)
    (low : ∀ z<ar.publicBase, dir z=readings initial z)
    (entry : NativeEntry ar il.frame controls decl.1 R (LocalRow.powerHeaderImage ar broadcast dir) (readings initial) (readings W.dataInput))
    (fixed : CubeAllocation.HostPointers ar il.frame (readings initial))
    (rep : Represents N cell aux siteID edgeID portID geoFields x) (codes : ∀ c, (geoFields.cells c).val=c.val)
    (fieldRoom : ∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^geometryBits)
    (supplyRoom : ∀ c, suppliedSize N cell c ≤ ar.cellStride) {geometry : ℕ → ℕ}
    (header : Header il.frame geoOrigin ar.cables ar.cells J (readings initial)) (image : Image geoFields old live x geoOrigin geometry)
    (previousGeo : ∀ z, geoOrigin ≤ z → z<geoOrigin+5*ar.cables → readings initial z=geometry z)
    (start : il.frame+112 ≤ geoOrigin) (before : geoOrigin+5*ar.cables ≤ ar.header.header)
    (task : SignedTaskArena.Layout) (arena : task.cube=ar)
    {offsets control liveBase portsCount bundles bankBits : ℕ}
    (bundleOwner : Fin bundles → Fin task.cube.cells) (bundleHeader : Fin bundles → Packing.BottomReports.BundleHeader)
    (openFields : task.OpenFields u.val il.frame offsets control liveBase portsCount bundles (readings W.dataInput))
    (controlWords : ∀ j : Fin 37, readings W.dataInput (control+j.val)=task.controls j.val)
    (openRoom : task.OpenRoom il.frame offsets control liveBase portsCount bundles (2^bankBits) w)
    (bank : task.p.bundleInverse=task.p.bundlePayload+2^bankBits)
    (sort : Packing.BottomReports.BundleSort.SectionSpec openRoom.markers bundleOwner bundleHeader (readings W.dataInput) task.p.bundlePayload)
    (first : il.frame+112 ≤ control) (payload : control ≤ task.p.bundlePayload) :
    let program := task.openInputs u.val il.frame offsets control liveBase portsCount bundles bankBits bundleOwner bundleHeader
    let frame := readings (F.pub u) 0
    let mem := readings (F.output u)
    Padding.Returned ar decl.1 group u frame w mem (fun k => dir (il.widths+k)) ∧
      OpenSuffix.Ready program frame mem w ∧ OpenSuffix.Placement program ar task.before frame mem := by
  subst ar
  intro program frame mem
  have base : frame=il.frame := (congrFun (congrArg readings (handoff.pub u)) 0).trans atFrame.symm
  have room := handoff.room u
  have chunk : 0 < task.cube.h*task.cube.b := by
    by_contra! zero
    have positive := room.payload
    simp [Nat.eq_zero_of_le_zero zero] at positive
  obtain ⟨keep,host⟩ := writer.returned_host_ready N cell aux siteID edgeID portID geoFields il previous dir rows interval cap
    symbols handoff receipt u W ready records source fit fields atFrame space widths low entry fixed rep codes fieldRoom supplyRoom
    header image previousGeo start before room.alphabet chunk room.stopFit
  have pad := writer.returned_padding N cell il previous dir rows interval cap symbols handoff receipt u W ready records
    source fit fields atFrame space widths low entry fixed
  have written := keep.from_written entry.low
  change Padding.Returned task.cube decl.1 group u frame w mem _ at pad
  change CubeAllocation.HostRetention task.cube frame (readings W.dataInput) (readings W.dataInput) mem at written
  change CubeAllocation.HostReady task.cube frame mem w at host
  rw [base] at pad written host ⊢
  exact ⟨pad,task.owned_open_ready bundleOwner bundleHeader written host openFields controlWords openRoom bank sort first payload pad.header pad.fits⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
