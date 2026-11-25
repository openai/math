import OAI.Computability.BorderVNP.DiagonalProjectedOwnedReplay

/-! # Report observations on the canonical writer of an actual replay -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open BorderVNP.Cube Physical Tally SharedRows PackedHistoryCircuit
open BorderVNP.Cube.Scatter TeamRows Scatter.Assignment SignedPrep

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

variable (F : PreparationFrame G wire ar decl header pin pub mac reg mem)
    (fixed : Block (R+1))
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (template : DiagonalTallyPacketEmit.Frame) (eid : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ) (count : ℕ)
    (test : HeaderExterior wire header → NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners → TeamRows.Returns (Fin (R+1)) ar w → Prop)

/-- An observation on the actual matching route and the original joint return from the owner scan. -/
abbrev PreparationFrame.ObservedReportReplay : Prop :=
  ∀ operands : SharedWords ar decl, let z := F.replay fixed operands
    ∀ (H : Fin (R+1) → TeamHistory w)
      (delivery : ReturnedDelivery G pin z.1.val wire F.dataDir F.privatePlacement F.livePlacement F.cellOwner
        F.origin F.stride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))),
      delivery.table=F.tab → delivery.row=F.row → SharedWriters delivery F.rows (F.source z.1) →
      (∀ u, (H u).pub=pub z.1 u ∧ (H u).macros=mac z.1 u ∧ (H u).history.val.2=(z.2 u).val.2) →
      (∀ u, Pins.SubstitutionAt (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))
        (F.guess u) (H u).initial) → delivery.receivedRows F.rows F.group=operands.val →
      ∀ (q : Matching ar owners decl (delivery.receivedRows F.rows F.group))
        (endRows : TeamRows.Returns (Fin (R+1)) ar w),
        OwnedHandoff delivery F.rows (F.source z.1) ar decl F.group template eid count endRows →
        ObservedOwned ar decl F.group endRows owners (delivery.receivedRows F.rows F.group) q.val →
        test z.1 q.val endRows

variable {F}
local notation3 (prettyPrint := false) "writerProjection" => PreparationFrame.WriterProjection G wire ar D pp lp owner decl group frame header
  pin guess dst ib hb sb pub mac reg mem epoch published endReg out events W F
local notation3 (prettyPrint := false) "payload(" x ")" => (fun u => readings (W x u).sharedInput)

/-- The same report observation, with the directory, registers, writer input, and symbol
frame of the physically selected writer available to its handler. -/
abbrev PreparationFrame.WriterProjection.CanonicalReportReplay (_picked : writerProjection) : Prop :=
  ∀ operands : SharedWords ar decl, let z := F.replay fixed operands
    ∀ (H : Fin (R+1) → TeamHistory w)
      (delivery : ReturnedDelivery G pin z.1.val wire D pp lp owner ar.cellBank ar.cellStride H
        (fun u => G.pinLayout u (ib u) (hb u) (sb u))),
      delivery.table=tab → delivery.row=row → SharedWriters delivery rows (payload(z.1)) →
      (∀ u, (H u).pub=pub z.1 u ∧ (H u).macros=mac z.1 u ∧ (H u).history.val.2=(z.2 u).val.2) →
      (∀ u, Pins.SubstitutionAt (G.pinLayout u (ib u) (hb u) (sb u)) (guess u) (H u).initial) →
      delivery.receivedRows rows group=operands.val →
      ∀ (q : Matching ar owners decl (delivery.receivedRows rows group))
        (endRows : TeamRows.Returns (Fin (R+1)) ar w),
        OwnedHandoff delivery rows (payload(z.1)) ar decl group template eid count endRows →
        ObservedOwned ar decl group endRows owners (delivery.receivedRows rows group) q.val →
        SymbolFrame rows ((payload(z.1)) 0) ar.header.blocks ar.K ar.h decl group →
        test z.1 q.val endRows

set_option maxHeartbeats 1800000 in
/-- Use the selected writer on precisely the original replay, matching assignment
and owner return. This single transport applies to opening, delivery and launch as
well as to the assembled report family. -/
theorem PreparationFrame.WriterProjection.observeReportReplay (picked : writerProjection)
    (checked : picked.CanonicalReportReplay fixed owners template eid count test) :
    F.ObservedReportReplay fixed owners template eid count test := by
  intro operands z H delivery tableAt rowAt writer returned substituted selected q endRows active seen
  obtain ⟨actual,tableEq,rowEq,writes,readEq,handoff,observed,_sameDelivery,pinned,symbols⟩ :=
    picked.owned_replay z.1 H delivery tableAt rowAt writer substituted active seen
  let matching : Matching ar owners decl (actual.receivedRows rows group) :=
    ⟨q.val,q.property.1,q.property.2.trans readEq.symm⟩
  exact checked operands H actual tableEq rowEq writes returned pinned (readEq.trans selected) matching
    endRows handoff observed symbols

end TeamContraction

end BorderVNP
end Computability
end OAI
