import OAI.Computability.BorderVNP.DiagonalDemandFreeOwner
import OAI.Computability.BorderVNP.DiagonalExternalFragmentHostWords
import OAI.Computability.BorderVNP.CubeScatterOwnedHostColumns

/-! # The descriptor writer and the later owned interpreter read the same host cell word -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open Scatter.Assignment DiagonalTallyPacketEmit FiniteEvaluator Evaluator

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

open Crossing Packing.RoutingOutputs BorderVNP.Cube.NativeIntervals Cube.HostScatter
open Diagonal.ExternalSew.Fragments
open scoped Classical

/-- Every bank owner read while emitting the seven-word directory is the corresponding
number at the later owned return. The sender and receiver use their actual frame
arguments, including the physical pointer in word 72. -/
theorem SharedWriters.data_owner_after_owned (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    {q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows g group) q) (u : Fin (R+1))
    {width : ℕ} {r s : Bank w} {m last : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory ar.n width (H u).pub (H u).macros r m es s last)
    (ready : DataReady (H u).pub W.dataInput)
    (records : (DataWriter.layout (readings (H u).pub) (readings W.dataInput)).output=ar.records)
    (source : src u=readings W.sharedInput)
    (pointer : (hostLayout F.pub F.output u).cells=ar.hostDirectory) (c : Fin ar.cells) :
    readings W.dataInput ((DataWriter.layout (readings (H u).pub) (readings W.dataInput)).owners+2*c.val)=
      readings (F.output u) ((hostLayout F.pub F.output u).cells+2*c.val) := by
  let frame := readings (H u).pub 0
  have hframe : readings (F.pub u) 0=frame := congrFun (congrArg readings (handoff.pub u)) 0
  have low := (handoff.room u).primary
  change frame+112≤ar.header.header at low
  obtain ⟨hw,labels,weights,ownersBefore,pairs,banks,_,_⟩ := ar.writer_order
  have keep := writer.owned_data_input_static symbols handoff receipt u W ready records source
  have at72 := keep (frame+72) (by omega) (.inl (by omega)) (by change frame+72≠frame+13; omega)
    (by change frame+72≠frame+46; omega)
  have host : readings (F.output u) (frame+72)=ar.hostDirectory := by
    rw [← hframe]; exact pointer
  have origin : (DataWriter.layout (readings (H u).pub) (readings W.dataInput)).owners=ar.hostDirectory :=
    at72.symm.trans host
  rw [origin,pointer]
  have bound := c.isLt
  exact (keep _ (by omega) (.inr (by omega)) (by change _≠frame+13; omega)
    (by change _≠frame+46; omega)).symm

end TeamContraction

end BorderVNP
end Computability
end OAI
