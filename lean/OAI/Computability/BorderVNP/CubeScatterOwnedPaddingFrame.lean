import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostPointers
import OAI.Computability.BorderVNP.CubeScatterPaddingArenaRoom

/-! # Primary and secondary padding fields on the recovered native memory -/

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

open FiniteEvaluator.CubeAllocation

/-- On the actual owned return the primary pointers, chosen power and indirect
bank words decode to the allocated padding layout. The numerical header bounds
and every symbol owner follow from the same handoff. -/
theorem SharedWriters.owned_padding_frame (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows g group) q) (u : Fin (R+1))
    (pointers : HostPointers ar g.frame (src u))
    (width : readings (F.output u) (readings (F.pub u) 0+57) = ar.widthBase) :
    let frame := readings (F.pub u) 0
    let mem := readings (F.output u)
    Padding.Layout.fromFrame frame mem = (Padding.arenaPointers ar).layout frame u.val ar.header.packetBase
      decl.1 ar.header.d ar.header.blocks ar.b ar.h ar.K ar.s ∧
    Padding.HeaderFits w frame mem ∧ ∀ j : Fin ar.header.d, mem (ar.ownerBase+j.val) = (group j).val := by
  intro frame mem
  have actual : frame = readings (H u).pub 0 := congrFun (congrArg readings (handoff.pub u)) 0
  have base : g.frame = frame := (handoff.frame u).trans actual.symm
  have room := handoff.room u
  have scanner := handoff.source u
  rw [←actual] at room scanner
  have primary := room.primary
  obtain ⟨header,labels,groupLo,ownerEnd,pairEnd,hostEnd,recordsEnd,stop⟩ := ar.writer_order
  obtain ⟨_,_,_,_,_,_,powerLo,powerHi,groupHi,teamHi,_,_,_⟩ := ar.group_order
  have bound := room.stopFit
  have scalar (j : ℕ) (hj : j < 112) (h13 : j ≠ 13) (h46 : j ≠ 46) : mem (frame+j) = src u (frame+j) :=
    writer.owned_output_static symbols handoff receipt u _ (by omega) (.inl (by omega))
      (by rw [base]; omega) (by change frame+j ≠ frame+46; omega)
  have secondary (j : ℕ) (hj : j < 13) : mem (ar.header.header+j) = src u (ar.header.header+j) :=
    writer.owned_output_static symbols handoff receipt u _ (by omega) (.inl (by omega))
      (by rw [base]; omega) (by change ar.header.header+j ≠ frame+46; omega)
  have upper (x : ℕ) (lo : ar.publicBase ≤ x) (hi : x < ar.records) : mem x = src u x :=
    writer.owned_output_static symbols handoff receipt u x hi (.inr lo)
      (by rw [base]; omega) (by change x ≠ frame+46; omega)
  obtain ⟨host,packet,single,selector⟩ := writer.owned_host_words symbols handoff receipt u pointers
  have groupWord : mem (frame+59) = ar.header.d :=
    (scalar 59 (by decide) (by decide) (by decide)).trans (actual ▸ scanner.setup.d)
  have powWord : mem (frame+62) = ar.powerBase :=
    (scalar 62 (by decide) (by decide) (by decide)).trans (actual ▸ scanner.setup.power)
  have hdr : mem (frame+63) = ar.header.header :=
    (scalar 63 (by decide) (by decide) (by decide)).trans (actual ▸ scanner.setup.header)
  have ax := (secondary 5 (by decide)).trans scanner.chosen
  have idx := decl.1.isLt
  have pow := (upper (ar.powerBase+decl.1.val) (by omega) (by omega)).trans (scanner.setup.powers decl.1.val (by omega))
  have own := (scalar 77 (by decide) (by decide) (by decide)).trans scanner.ownersBase
  have site : mem frame = u.val := by simpa using (scalar 0 (by decide) (by decide) (by decide)).trans (by simpa using scanner.teamID)
  have alpha : mem (frame+56) = ar.alphabet := host.alphabet
  have pairs : mem (frame+91) = ar.pairDirectory := host.pairs
  have singleWord : mem (frame+88) = ar.singleBank := single
  have packetWord := (secondary 8 (by decide)).trans scanner.setup.bank
  have blocks := (secondary 7 (by decide)).trans scanner.setup.blocks
  have bc : mem (frame+61) = ar.h*ar.b := host.width
  have bw : mem (frame+93) = Tally.bankWidth ar.n ar.b ar.h ar.K ar.s := host.packetWidth
  have sw : mem (frame+94) = Tally.selectorWidth ar.n ar.K ar.h := selector
  have physical := Padding.physicalRoom_of_arena ar frame u.val decl.1 room.alphabet bound
  refine ⟨?_,⟨by omega,by rw [hdr]; omega,by rw [powWord,hdr,ax]; omega,by rw [alpha]; exact physical.pairs⟩,?_⟩
  · change mem (frame+57) = ar.widthBase at width
    dsimp only [Padding.Layout.fromFrame]
    rw [groupWord,alpha,powWord,hdr,ax,pow,own,width,pairs,singleWord,packetWord,blocks,bc,bw,sw,site]
    rfl
  · intro j
    have hj := j.isLt
    exact (upper _ (by omega) (by omega)).trans (scanner.owners j)

end TeamContraction

end BorderVNP
end Computability
end OAI
