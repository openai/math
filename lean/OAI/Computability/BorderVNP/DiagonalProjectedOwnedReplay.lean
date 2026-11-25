import OAI.Computability.BorderVNP.DiagonalSignedReferenceFrame
import OAI.Computability.BorderVNP.CubeScatterReturnedOwnedFamily

/-! # Recovering the canonical writer on a returned ownership scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open BorderVNP.Cube Physical Tally SharedRows PackedHistoryCircuit
open BorderVNP.Cube.Scatter TeamRows Scatter.Assignment

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (wire : WireLayout (R+1) r link) (ar : CubeArena.Layout) (D : Packing.Directory.Layout)
    (pp lp : ℕ → ℕ × ℕ) (owner : ℕ → Fin (R+1)) (decl : LengthDeclaration ar.n ar.header.d)
    (group : Fin ar.header.d → Fin (R+1)) (frame : ℕ) (header : List Bool) (len : header.length=wire.header)
    (pin : Fin d → Bool) (guess : Fin (R+1) → ℕ → Bool) (dst ib hb sb : Fin (R+1) → ℕ)
local notation "X" => HeaderExterior wire header
local notation "entries" => List.length (D.directory pp lp)
local notation "rows" => ar.sharedRows frame (Fin.val (Prod.fst decl)) entries
local notation "tab" => ar.table frame (entries+ar.header.d.choose 2)
local notation "row" => RouteRecords.combinedRow (D.directory pp lp) owner ar.header.blocks ar.K ar.h decl group
local notation "PL" u => G.pinLayout u (ib u) (hb u) (sb u)
local notation "BF" u => G.transferFrame u wire.header (dst u)

variable (pub : HeaderExterior wire header → Fin (R+1) → Arg → Word w) (mac : HeaderExterior wire header → Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : HeaderExterior wire header → Fin (R+1) → Bank w) (mem : HeaderExterior wire header → Fin (R+1) → Memory w)
    (epoch : ∀ x u, Returns epochPlacement (pub x u) (mac x u) (reg x u) (mem x u))
    (published : ∀ x u, Returns Packing.Directory.ISA.program (pub x u) (mac x u)
      (epoch x u).val.2.1 (epoch x u).val.2.2)
    (endReg : HeaderExterior wire header → Fin (R+1) → Bank w) (out : HeaderExterior wire header → Fin (R+1) → Memory w)
    (events : HeaderExterior wire header → Fin (R+1) → List (TeamRAM.Event w))
    (W : ∀ x u, WriterHistory ar.n (selectorWidth ar.n ar.K ar.h) (pub x u) (mac x u)
      (published x u).val.2.1 (published x u).val.2.2 (events x u) (endReg x u) (out x u))

variable {G wire ar D pp lp owner decl group frame header pin guess dst ib hb sb pub mac reg mem
  epoch published endReg out events W}

set_option maxHeartbeats 1200000 in
/-- Express a replay and its ownership scan at the fields of its selected native
writer. The team histories, last memory, assignment, and observed shared bits
are exactly the ones on which the caller reached the scan. -/
theorem PreparationFrame.WriterProjection.owned_replay
    {F : PreparationFrame G wire ar decl header pin pub mac reg mem}
    (picked : PreparationFrame.WriterProjection G wire ar D pp lp owner decl group frame header
      pin guess dst ib hb sb pub mac reg mem epoch published endReg out events W F)
    {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
    {template : DiagonalTallyPacketEmit.Frame} {eid : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ} {count : ℕ}
    (x : HeaderExterior wire header) (H : Fin (R+1) → TeamHistory w)
    (f : ReturnedDelivery G pin x.val wire F.dataDir F.privatePlacement F.livePlacement F.cellOwner
      F.origin F.stride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u)))
    (tableAt : f.table=F.tab) (rowAt : f.row=F.row) (writer : SharedWriters f F.rows (F.source x))
    (sub : ∀ u, Pins.SubstitutionAt (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))
      (F.guess u) (H u).initial)
    {q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners}
    {endRows : TeamRows.Returns (Fin (R+1)) ar w}
    (active : OwnedHandoff f F.rows (F.source x) ar decl F.group template eid count endRows)
    (seen : ObservedOwned ar decl F.group endRows owners (f.receivedRows F.rows F.group) q) :
    ∃ actual : ReturnedDelivery G pin x.val wire D pp lp owner ar.cellBank ar.cellStride H (fun u => PL u),
      actual.table=tab ∧ actual.row=row ∧ SharedWriters actual rows (fun u => readings (W x u).sharedInput) ∧
      actual.receivedRows rows group=f.receivedRows F.rows F.group ∧
      OwnedHandoff actual rows (fun u => readings (W x u).sharedInput) ar decl group template eid count endRows ∧
      ObservedOwned ar decl group endRows owners (actual.receivedRows rows group) q ∧ HEq actual f ∧
      (∀ u, Pins.SubstitutionAt (PL u) (guess u) (H u).initial) ∧
      SymbolFrame rows (readings (W x 0).sharedInput) ar.header.blocks ar.K ar.h decl group := by
  let raw := f.receivedRows F.rows F.group
  let cert (directory : Packing.Directory.Layout) (left right : ℕ → ℕ × ℕ) (cellOwner : ℕ → Fin (R+1))
      (origin stride : ℕ) (input column reference : Fin (R+1) → ℕ) (digits : Fin (R+1) → ℕ → Bool)
      (g : SharedRows.Layout) (source : Fin (R+1) → ℕ → ℕ) (allocate : Fin ar.header.d → Fin (R+1)) : Prop :=
    ∃ actual : ReturnedDelivery G pin x.val wire directory left right cellOwner origin stride H
        (fun u => G.pinLayout u (input u) (column u) (reference u)),
      actual.table=tab ∧ actual.row=row ∧ SharedWriters actual g source ∧ actual.receivedRows g allocate=raw ∧
      OwnedHandoff actual g source ar decl allocate template eid count endRows ∧
      ObservedOwned ar decl allocate endRows owners (actual.receivedRows g allocate) q ∧ HEq actual f ∧
      (∀ u, Pins.SubstitutionAt (G.pinLayout u (input u) (column u) (reference u)) (digits u) (H u).initial) ∧
      SymbolFrame g (source 0) ar.header.blocks ar.K ar.h decl allocate
  have symbols := F.frame x
  rw [picked.anchor] at symbols
  have original : cert F.dataDir F.privatePlacement F.livePlacement F.cellOwner F.origin F.stride
      F.inputBase F.columnBase F.referenceBase F.guess F.rows (F.source x) F.group :=
    ⟨f,tableAt.trans picked.table,rowAt.trans picked.slot,writer,rfl,active,seen,HEq.rfl,sub,symbols⟩
  have sourceEq : F.source x=(fun u => readings (W x u).sharedInput) := funext (picked.image x)
  rw [picked.directory,picked.privatePairs,picked.livePairs,picked.owned,picked.origin,picked.stride,
    picked.input,picked.column,picked.reference,picked.guesses,picked.shared,sourceEq,picked.groupNumber] at original
  exact original

end TeamContraction

end BorderVNP
end Computability
end OAI
