import OAI.Computability.BorderVNP.CubeScatterOwnedStaticWords
import OAI.Computability.BorderVNP.CubeHostScatterPreparedColumns
import OAI.Computability.BorderVNP.CubeRouteWriterReadback

/-! # Source rows at the physical host program after a genuine distributed return -/

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

/-- The complete returned team image retains the input of the actual data descriptor
compiler at every immutable low geometry or public table word below the records. -/
theorem SharedWriters.owned_data_input_static (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows g group) q) (u : Fin (R+1))
    {width : ℕ} {rr rt : Bank w} {initial last : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory ar.n width (H u).pub (H u).macros rr initial es rt last)
    (ready : DataReady (H u).pub W.dataInput)
    (records : (DataWriter.layout (readings (H u).pub) (readings W.dataInput)).output = ar.records)
    (source : src u = readings W.sharedInput)
    (x : ℕ) (before : x < ar.records) (extent : x < ar.header.header+13 ∨ ar.publicBase ≤ x)
    (emitter : x ≠ readings (H u).pub 0+13) (directory : x ≠ readings (H u).pub 0+46) :
    readings (F.output u) x = readings W.dataInput x := by
  have no13 : x ≠ g.frame+13 := (handoff.frame u) ▸ emitter
  have no46 : x ≠ readings (F.pub u) 0+46 := (handoff.pub u) ▸ directory
  have returned := writer.owned_output_static symbols handoff receipt u x before extent no13 no46
  have same : W.sharedInput x = W.dataInput x := by
    rw [W.dataImage ready,DataWriter.publish,Function.update_of_ne (show x ≠ ((H u).pub 0).val+13 from emitter),
      Packing.Directory.ISA.putWords_outside _ _ _ _ (.inl (records ▸ before))]
  exact returned.trans ((congrFun source x).trans (congrArg Fin.val same))

/-- At an actual owned return, the host reads exactly the true cells, widths, chosen
product labels, within-bin ordinal and packet triples from the physical geometry.
The table indices and all five dynamic host sizes refer to that team's returned RAM. -/
theorem SharedWriters.owned_host_columns (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows g group) q) (u : Fin (R+1))
    {controls broadcast width : ℕ} {rr rt : Bank w} {initial last : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory ar.n width (H u).pub (H u).macros rr initial es rt last)
    (ready : DataReady (H u).pub W.dataInput)
    (records : (DataWriter.layout (readings (H u).pub) (readings W.dataInput)).output = ar.records)
    (source : src u = readings W.sharedInput)
    (il : NativeIntervals.Layout) (before dir : ℕ → ℕ)
    (interval : il.Image before il.count dir) (fit : il.Fits w before)
    (fields : il.Fields before) (atFrame : il.frame = readings (H u).pub 0)
    (space : HostScatter.CableColumns ar il.frame il before) (widths : il.widths = ar.widthBase)
    (low : ∀ x < ar.publicBase, dir x = readings initial x)
    (entry : NativeEntry ar il.frame controls decl.1 R (LocalRow.powerHeaderImage ar broadcast dir) (readings initial) (readings W.dataInput))
    (pair : readings initial (il.frame+91) = ar.pairDirectory)
    (packetWidth : readings initial (il.frame+93) = Tally.bankWidth ar.n ar.b ar.h ar.K ar.s)
    (selWidth : readings initial (il.frame+94) = Tally.selectorWidth ar.n ar.K ar.h) :
    HostScatter.ResidentRows (HostScatter.Layout.fromFrame (readings (F.pub u) 0) (readings (F.output u)))
      il before dir (readings (F.output u)) ar.n ar.header.d ar.header.blocks ar.b ar.h ar.K ar.s := by
  let out := readings (F.output u)
  let host := HostScatter.Layout.fromFrame il.frame out
  have base : readings (F.pub u) 0 = il.frame := (congrFun (congrArg readings (handoff.pub u)) 0).trans atFrame.symm
  have gFrame : g.frame = il.frame := (handoff.frame u).trans atFrame.symm
  have primary : il.frame+112 ≤ ar.header.header := atFrame ▸ (handoff.room u).primary
  have same (x : ℕ) (hx : x < ar.records) (extents : x < ar.header.header+13 ∨ ar.publicBase ≤ x)
      (emitter : x ≠ il.frame+13) (directory : x ≠ il.frame+46) : out x = readings W.dataInput x := by
    exact writer.owned_data_input_static symbols handoff receipt u W ready records source x hx extents
      (atFrame ▸ emitter) (atFrame ▸ directory)
  have htop := ar.writer_order.1
  have original (j : ℕ) (hj : j < 112) (h13 : j ≠ 13) (h46 : j ≠ 46) :
      out (il.frame+j) = readings initial (il.frame+j) := by
    have lo := (Nat.add_lt_add_left hj _).trans_le primary
    exact (same _ (lo.trans_le (secondary_le_records ar)) (.inl (by omega)) (Nat.add_left_cancel.mt h13)
      (Nat.add_left_cancel.mt h46)).trans (entry.low _ lo)
  have beforeFrame (j : ℕ) (hj : j < 112) (h13 : j ≠ 13) (h46 : j ≠ 46) : out (il.frame+j) = before (il.frame+j) := by
    have lo : il.frame+j < ar.publicBase := by omega
    have wi := ar.group_order.2.2.2.2.1
    have oi := ar.group_order.2.2.2.2.2.1
    have unchanged := interval.outside (il.frame+j) (by rw [widths]; omega) (by rw [space.ordinals]; omega)
    exact (original j hj h13 h46).trans ((low _ lo).symm.trans unchanged)
  have ptrs := handoff.source u
  have keep (j : ℕ) (hj : j < 112) (h13 : j ≠ 13) (h46 : j ≠ 46) :
      out (il.frame+j) = src u (il.frame+j) :=
    writer.owned_output_static symbols handoff receipt u _ ((Nat.add_lt_add_left hj _).trans_le
      (primary.trans (secondary_le_records ar))) (.inl (by omega)) (gFrame ▸ Nat.add_left_cancel.mt h13)
      (base ▸ Nat.add_left_cancel.mt h46)
  have hd : out (il.frame+63) = ar.header.header := (keep 63 (by decide) (by decide) (by decide)).trans (atFrame ▸ ptrs.setup.header)
  have payload : out (il.frame+61) = ar.h*ar.b := (keep 61 (by decide) (by decide) (by decide)).trans (atFrame ▸ ptrs.setup.bc)
  have hostHeader : out (ar.header.header+7) = ar.header.blocks := by
    obtain ⟨_,_,_,_,pairEnd,hostEnd,_,_⟩ := ar.writer_order
    have group := ar.group_order
    apply (writer.owned_output_static symbols handoff receipt u _ (by omega) (.inl (by omega))
      (by rw [gFrame]; omega) (by rw [base]; omega)).trans
    exact ptrs.setup.blocks
  rw [base]
  apply HostScatter.residentRows_of_columns host space fit interval low entry primary same
  · obtain ⟨c,num,lab,alpha,_,ordinal⟩ := fields
    exact ⟨(beforeFrame 7 (by decide) (by decide) (by decide)).trans num,
      (beforeFrame 56 (by decide) (by decide) (by decide)).trans alpha,
      (beforeFrame 6 (by decide) (by decide) (by decide)).trans c,
      (beforeFrame 48 (by decide) (by decide) (by decide)).trans lab,
      (beforeFrame 58 (by decide) (by decide) (by decide)).trans ordinal,
      (original 91 (by decide) (by decide) (by decide)).trans pair⟩
  · exact ⟨by change out (out (il.frame+63)+7) = _; rw [hd,hostHeader],payload,
      (original 93 (by decide) (by decide) (by decide)).trans packetWidth,
      (original 94 (by decide) (by decide) (by decide)).trans selWidth⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
