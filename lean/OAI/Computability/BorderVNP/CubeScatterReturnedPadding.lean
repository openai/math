import OAI.Computability.BorderVNP.CubeScatterOwnedPaddingFrame
import OAI.Computability.BorderVNP.CubeScatterOwnedPaddingWidths
import OAI.Computability.BorderVNP.CubeScatterPaddingTableReadback

/-! # Real occupied widths, owner and packet addresses at the distributed padding guard -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open RoutingISA VPVNP.BurstRAM

/-- The allocated scalar cache, real checked owner and width tables and all
numerical startup conditions of this native guard. -/
structure Returned (ar : CubeArena.Layout) {R : ℕ} (axis : Fin (ar.n+1)) (group : Fin ar.header.d → Fin (R+1))
    (u : Fin (R+1)) (frame w : ℕ) (mem used : ℕ → ℕ) : Prop where
  layout : Layout.fromFrame frame mem = (arenaPointers ar).layout frame u.val ar.header.packetBase axis
    ar.header.d ar.header.blocks ar.b ar.h ar.K ar.s
  header : HeaderFits w frame mem
  tail : TailHeader axis group Fin.valEmbedding u (Layout.fromFrame frame mem) mem used ar.header.blocks ar.b ar.h ar.K ar.s
  fits : (Layout.fromFrame frame mem).Fits w mem

end Cube.Padding

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

variable {dim m : ℕ} {P : Type*} {bits : P → ℕ}
variable (N : Network dim P bits) (cell : N.Site → Fin ar.cells)
variable (il : NativeIntervals.Layout) (previous dir : ℕ → ℕ) {ord : N.CrossingEdge cell ≃ Fin m}
variable {row : Fin m ↪o Fin il.count} {label : Fin ar.cells → Label (ar.n+1) ar.header.d} {hz : ar.header.d^(ar.n+1)=il.alphabet}
variable (rows : PhysicalRows N cell il previous ord row Fin.valEmbedding label (productCode ar.n ar.header.d il.alphabet hz))
variable (interval : il.Image previous il.count dir)
variable (cap : ∀ u, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
  (crossWidth N cell ∘ ord.symm) u ≤ ar.header.blocks*(ar.h*ar.b))

include rows interval cap in
/-- The earlier native interval and pair producers, true boot pointers, actual
data writer and arbitrary owned traversal supply every operand and bound at
the padding instruction's true entry. -/
theorem SharedWriters.returned_padding (writer : SharedWriters f g src)
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
    (fixed : CubeAllocation.HostPointers ar il.frame (readings initial)) :
    Padding.Returned ar decl.1 group u (readings (F.pub u) 0) w (readings (F.output u)) (fun k => dir (il.widths+k)) := by
  let frame := readings (F.pub u) 0
  let mem := readings (F.output u)
  have base : frame=il.frame := (congrFun (congrArg readings (handoff.pub u)) 0).trans atFrame.symm
  have entry' := atFrame ▸ entry
  have keep := writer.owned_host_retention symbols handoff receipt u W ready records source _ entry'
  have input : CubeAllocation.HostPointers ar g.frame (src u) := by
    rw [source,handoff.frame u]
    exact (show CubeAllocation.HostPointers ar (readings (H u).pub 0) (readings initial) from atFrame ▸ fixed).after_data
      W entry' ready records (handoff.room u).primary
  have widthRead := Padding.owned_widths keep (base ▸ entry) base.symm fields interval low widths space.ordinals
  obtain ⟨layout,header,ownersWord⟩ := writer.owned_padding_frame symbols handoff receipt u input widthRead.1
  obtain ⟨host,_,_,_⟩ := writer.owned_host_words symbols handoff receipt u input
  have data := writer.owned_host_columns symbols handoff receipt u W ready records source il previous dir interval fit fields
    atFrame space widths low entry (fixed 91 (by decide) _ rfl) (fixed 93 (by decide) _ rfl) (fixed 94 (by decide) _ rfl)
  have triples := data.triples
  rw [host.pairs] at triples
  have room := handoff.room u
  let l := (Padding.arenaPointers ar).layout frame u.val ar.header.packetBase decl.1 ar.header.d ar.header.blocks ar.b ar.h ar.K ar.s
  have tail : Padding.TailHeader decl.1 group Fin.valEmbedding u l mem (fun k => dir (il.widths+k))
      ar.header.blocks ar.b ar.h ar.K ar.s := by
    refine ⟨⟨rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl⟩,rfl,ownersWord,?_,triples⟩
    intro k hk
    exact widthRead.2 k (by simpa only [l,Padding.Pointers.layout,Padding.Layout.count,pow_two,CubeArena.Layout.alphabet] using hk)
  have bounds := Padding.physicalRoom_of_arena ar frame u.val decl.1 room.alphabet room.stopFit
  have all := tail.fits_of_room room.alphabet bounds (Padding.occupied_le rows interval cap)
  exact ⟨layout,header,layout ▸ tail,layout ▸ all⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
