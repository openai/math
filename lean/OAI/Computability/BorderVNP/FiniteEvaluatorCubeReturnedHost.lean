import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOwnedOpen
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostPointers

/-! # The host cable scatter at an actual all-team owned return

The fetched signed scalar fields, reached group schedule, emitted
cell/pair directory, directed crossing ordinals and receiving banks all
refer to one chronology. Every execution of the host cable copy therefore
has its actual numerical and source-separation prerequisites at that memory.
-/

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
/-- The physical post-owned state satisfies the host program, including all
protected read addresses. The proof consumes the previously emitted geometry,
selected input labels and intervals, and the genuine native directory history. -/
theorem SharedWriters.returned_host_ready (writer : SharedWriters f g src)
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
    (radix : 0 < ar.header.d) (chunk : 0 < ar.h*ar.b) (room : ar.stop < 2^w) :
    let frame := readings (F.pub u) 0
    let mem := readings (F.output u)
    CubeAllocation.HostRetention ar frame (readings initial) (readings W.dataInput) mem ∧
      CubeAllocation.HostReady ar frame mem w := by
  intro frame mem
  have base : frame=il.frame := (congrFun (congrArg readings (handoff.pub u)) 0).trans atFrame.symm
  have entry' := atFrame ▸ entry
  have keep := writer.owned_host_retention symbols handoff receipt u W ready records source _ entry'
  have input : CubeAllocation.HostPointers ar g.frame (src u) := by
    rw [source,handoff.frame u]
    exact (show CubeAllocation.HostPointers ar (readings (H u).pub 0) (readings initial) from atFrame ▸ fixed).after_data
      W entry' ready records (handoff.room u).primary
  obtain ⟨host,packet,single,_⟩ := writer.owned_host_words symbols handoff receipt u input
  have data := writer.owned_host_columns symbols handoff receipt u W ready records source il previous dir interval fit fields
    atFrame space widths low entry (fixed 91 (by decide) _ rfl) (fixed 93 (by decide) _ rfl) (fixed 94 (by decide) _ rfl)
  have atOutput : NativeEntry ar frame controls decl.1 R (LocalRow.powerHeaderImage ar broadcast dir) (readings initial) (readings W.dataInput) := by
    rwa [base]
  exact ⟨keep,CubeAllocation.host_ready_of_retention ar frame mem w N cell aux siteID edgeID portID geoFields data rows interval cap
    keep rep codes fieldRoom supplyRoom (base ▸ header) image previousGeo (base ▸ start) before host packet single radix chunk room decl.1 atOutput⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
