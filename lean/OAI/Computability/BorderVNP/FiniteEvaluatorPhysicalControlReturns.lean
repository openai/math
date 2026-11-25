import OAI.Computability.BorderVNP.FiniteEvaluatorReturnedControlEntry
import OAI.Computability.BorderVNP.CubeScatterReturnedPaddingFamily
import OAI.Computability.BorderVNP.FiniteEvaluatorOwnedControlReturns

/-! # Simultaneous control returns on the genuine received evaluator state -/

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
variable (il : NativeIntervals.Layout) (previous dir : Fin (R+1) → ℕ → ℕ) {ord : N.CrossingEdge cell ≃ Fin m}
variable {row : Fin (R+1) → Fin m ↪o Fin il.count} {label : Fin ar.cells → Label (ar.n+1) ar.header.d}
variable {hz : ar.header.d^(ar.n+1)=il.alphabet}
variable (rows : ∀ u, PhysicalRows N cell il (previous u) ord (row u) Fin.valEmbedding label (productCode ar.n ar.header.d il.alphabet hz))
variable (interval : ∀ u, il.Image (previous u) il.count (dir u))
variable (cap : ∀ v, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
  (crossWidth N cell ∘ ord.symm) v ≤ ar.header.blocks*(ar.h*ar.b))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
include rows interval cap in
/-- The four deterministic stages return simultaneously from the recovered
selector and endpoint assignment exactly when both padding pins vanish at
every unused physical slot. The witness consists of the real team traces,
register banks and complete memories passed to the private report program.
Its control inputs are derived here from the earlier routing and profile
producer words on the same native execution. -/
theorem SharedWriters.controls_iff_pins (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    {q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows g group) q)
    {controls broadcast width : ℕ} {rr rt : Fin (R+1) → Bank w} {initial last : Fin (R+1) → Memory w}
    {es : Fin (R+1) → List (TeamRAM.Event w)}
    (W : ∀ u, WriterHistory ar.n width (H u).pub (H u).macros (rr u) (initial u) (es u) (rt u) (last u))
    (ready : ∀ u, DataReady (H u).pub (W u).dataInput)
    (records : ∀ u, (DataWriter.layout (readings (H u).pub) (readings (W u).dataInput)).output=ar.records)
    (source : ∀ u, src u=readings (W u).sharedInput)
    (fit : ∀ u, il.Fits w (previous u)) (fields : ∀ u, il.Fields (previous u)) (atFrame : ∀ u, il.frame=readings (H u).pub 0)
    (space : ∀ u, HostScatter.CableColumns ar il.frame il (previous u)) (widths : il.widths=ar.widthBase)
    (low : ∀ u z, z<ar.publicBase → dir u z=readings (initial u) z)
    (entry : ∀ u, NativeEntry ar il.frame controls decl.1 R (LocalRow.powerHeaderImage ar broadcast (dir u))
      (readings (initial u)) (readings (W u).dataInput))
    (fixed : ∀ u, CubeAllocation.HostPointers ar il.frame (readings (initial u)))
    (rep : Represents N cell aux siteID edgeID portID geoFields x) (codes : ∀ c, (geoFields.cells c).val=c.val)
    (fieldRoom : ∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^geometryBits)
    (supplyRoom : ∀ c, suppliedSize N cell c ≤ ar.cellStride) {geometry : Fin (R+1) → ℕ → ℕ}
    (header : ∀ u, Header il.frame geoOrigin ar.cables ar.cells J (readings (initial u)))
    (image : ∀ u, Image geoFields old live x geoOrigin (geometry u))
    (previousGeo : ∀ u z, geoOrigin ≤ z → z<geoOrigin+5*ar.cables → readings (initial u) z=geometry u z)
    (start : il.frame+112 ≤ geoOrigin) (before : geoOrigin+5*ar.cables ≤ ar.header.header)
    (task : SignedTaskArena.Layout) (arena : task.cube=ar)
    {offsets control liveBase portsCount bundles bankBits : ℕ}
    (bundleOwner : Fin bundles → Fin task.cube.cells) (bundleHeader : Fin (R+1) → Fin bundles → Packing.BottomReports.BundleHeader)
    (openFields : ∀ u, task.OpenFields u.val il.frame offsets control liveBase portsCount bundles (readings (W u).dataInput))
    (controlWords : ∀ u (j : Fin 37), readings (W u).dataInput (control+j.val)=task.controls j.val)
    (openRoom : task.OpenRoom il.frame offsets control liveBase portsCount bundles (2^bankBits) w)
    (bank : task.p.bundleInverse=task.p.bundlePayload+2^bankBits)
    (sort : ∀ u, BottomReports.BundleSort.SectionSpec openRoom.markers bundleOwner (bundleHeader u) (readings (W u).dataInput) task.p.bundlePayload)
    (first : il.frame+112 ≤ control) (payload : control ≤ task.p.bundlePayload) :
    let program := fun u : Fin (R+1) => task.openInputs u.val il.frame offsets control liveBase portsCount bundles bankBits bundleOwner (bundleHeader u)
    OpenSuffix.ControlFamily program F.pub F.macros F.finalRegs F.output
      (∀ slot ∉ Set.range (packedSlotEmbedding N cell ord label ar.header.blocks (ar.h*ar.b) cap),
        readEnd (fun z => lookup q.2 (.inl z)) (demands q.2) false slot=false ∧
        readEnd (fun z => lookup q.2 (.inl z)) (demands q.2) true slot=false) := by
  intro program
  have localData (u : Fin (R+1)) := writer.returned_control_entry N cell aux siteID edgeID portID geoFields il (previous u) (dir u)
    (rows u) (interval u) cap symbols handoff receipt u (W u) (ready u) (records u) (source u) (fit u) (fields u) (atFrame u)
    (space u) widths (low u) (entry u) (fixed u) rep codes fieldRoom supplyRoom (header u) (image u) (previousGeo u) start before
    task arena bundleOwner (bundleHeader u) (openFields u) (controlWords u) openRoom bank (sort u) first payload
  obtain ⟨banks,headers⟩ := receipt.padding_family rows interval (fun u => (localData u).1) anchor
  apply OpenSuffix.ControlFamily.of_ready (fun u => (localData u).2.1)
  exact OpenSuffix.team_returns_iff_pins (rows anchor) (interval anchor) cap program F.pub F.macros F.finalRegs F.output
    (fun u => (localData u).2.1) banks headers

end TeamContraction

end BorderVNP
end Computability
end OAI
