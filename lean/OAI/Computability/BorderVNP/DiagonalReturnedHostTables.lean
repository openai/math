import OAI.Computability.BorderVNP.DiagonalPublishedHostTables
import OAI.Computability.BorderVNP.CubeScatterOwnedHostColumns

/-! # Attained chooser and writer receipts for the recovered signed host tables -/

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

/-- Transport the actual selected chooser intervals through the same descriptor writer
and owned return. The axis and owners in the returned receipts come from the
recovered assignment on those very native runs. -/
theorem SharedWriters.published_host_rows (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    {q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows g group) q) (u : Fin (R+1))
    {controls broadcast width : ℕ} {rr rt : Bank w} {initial last endMem : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory ar.n width (H u).pub (H u).macros rr initial es rt last)
    (ready : DataReady (H u).pub W.dataInput)
    (records : (DataWriter.layout (readings (H u).pub) (readings W.dataInput)).output=ar.records)
    (source : src u=readings W.sharedInput)
    {D : ℕ} {P : Type} {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin ar.cells) (edgeID : N.Edge ↪ Fin ar.cables)
    (label : Fin ar.cells → Label (ar.n+1) ar.header.d)
    (il : NativeIntervals.Layout) (hz : ar.header.d^(ar.n+1)=il.alphabet)
    (atFrame : il.frame=readings (H u).pub 0) (widths : il.widths=ar.widthBase)
    (entry : NativeEntry ar il.frame controls decl.1 R (LocalRow.powerHeaderImage ar broadcast (readings endMem))
      (readings initial) (readings W.dataInput))
    (pair : readings initial (il.frame+91)=ar.pairDirectory)
    (packetWidth : readings initial (il.frame+93)=Tally.bankWidth ar.n ar.b ar.h ar.K ar.s)
    (selectorWidth : readings initial (il.frame+94)=Tally.selectorWidth ar.n ar.K ar.h)
    (chooser : ∃ mem : Memory w,
      il.Image (readings mem) il.count (readings endMem) ∧ il.Fits w (readings mem) ∧ il.Fields (readings mem) ∧
      CableColumns ar il.frame il (readings mem) ∧ (∀ x < ar.publicBase, readings endMem x=readings initial x) ∧
      ∃ row : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin il.count,
        (∀ e, (row (NativeDemands.cableOrder N cell edgeID e)).val=(edgeID e.val).val) ∧
        PhysicalRows N cell il (readings mem) (NativeDemands.cableOrder N cell edgeID) row Fin.valEmbedding label
          (productCode ar.n ar.header.d il.alphabet hz)) :
    let frame := readings (F.pub u) 0
    CubeAllocation.HostRetention ar frame (readings initial) (readings W.dataInput) (readings (F.output u)) ∧
    NativeEntry ar frame controls (chosen ar.b ar.s q.1) R (LocalRow.powerHeaderImage ar broadcast (readings endMem))
      (readings initial) (readings W.dataInput) ∧
    ∃ before : ℕ → ℕ, ∃ row : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin il.count,
      (∀ e, (row (NativeDemands.cableOrder N cell edgeID e)).val=(edgeID e.val).val) ∧
      PhysicalRows N cell il before (NativeDemands.cableOrder N cell edgeID) row Fin.valEmbedding label
        (productCode ar.n ar.header.d il.alphabet hz) ∧ il.Image before il.count (readings endMem) ∧
      ResidentRows (hostLayout F.pub F.output u) il before (readings endMem) (readings (F.output u))
        ar.n ar.header.d ar.header.blocks ar.b ar.h ar.K ar.s := by
  intro frame
  have hf : frame=il.frame := (congrFun (congrArg readings (handoff.pub u)) 0).trans atFrame.symm
  have actualAxis : chosen ar.b ar.s q.1=decl.1 := congrArg Prod.fst receipt.observed.1
  obtain ⟨mem,interval,fit,fields,cables,low,row,aligned,geometry⟩ := chooser
  refine ⟨writer.owned_host_retention symbols handoff receipt u W ready records source _ (atFrame ▸ entry),
    hf ▸ actualAxis ▸ entry,readings mem,row,aligned,geometry,interval,?_⟩
  exact writer.owned_host_columns symbols handoff receipt u W ready records source il (readings mem) (readings endMem)
    interval fit fields atFrame cables widths low entry pair packetWidth selectorWidth

end TeamContraction

end BorderVNP
end Computability
end OAI
