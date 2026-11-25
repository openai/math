import OAI.Computability.BorderVNP.RoutingISASignedPrepEnd

/-! # Constructing the signed local builder from the true routed writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator SignedPrep
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment
open DiagonalTallyPacketEmit DiagonalTallyCellReports BorderVNP.FiniteEvaluator
open private declaredTeam_eq from OAI.Computability.BorderVNP.CubeScatterReturnedOwnedFamily

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : Routing.WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
    {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
    {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}

variable (ar : CubeArena.Layout) (decl : LengthDeclaration ar.n ar.header.d)
    {Cell Data : Type*} [Fintype Data]
    (label : Cell → Label (ar.n+1) ar.header.d) (recv : Data → Cell) (dataWidth : Data → ℕ)
    (group : Fin ar.header.d → Fin (R+1)) (template : Frame)
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ) (count : ℕ)

local notation "owners" => greedyOwner R ar.b ar.s label recv dataWidth
set_option quotPrecheck false in
local notation "pub" => fun u : Fin (R+1) => (H u).pub
set_option quotPrecheck false in
local notation "mac" => fun u : Fin (R+1) => (H u).macros
local notation "pack" => CubeConstants.inArena template ar.stop ar.n ar.b ar.h ar.K ar.s
local notation "idBase" => CubeConstants.idBase ar.stop ar.n ar.b ar.h ar.K ar.s

variable (writer : SharedWriters f g src)
    (scheduled : group = declaredTeam ar decl label recv dataWidth R)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (banks : g.banks=ar.pairBase) (spacing : g.stride=ar.pairStride)
    (room : ∀ u, ar.ReplayRoom w (readings (H u).pub 0)) (table : ∀ u, f.table=ar.table (readings (H u).pub 0) count)
    (fp : ∀ u, g.frame=readings (H u).pub 0)
    (source : ∀ u, ar.ScannerWords (readings (H u).pub 0) u.val decl.1.val (fun x => (group x).val)
      (readings (H u).pub) (src u) decl.2)
    (installed : ∀ u, Evaluator.Returns (CubeConstants.install id) (H u).pub (H u).macros
      (H u).history.val.2.1 (H u).history.val.2.2)
    (copies : 1 ≤ ar.K) (labels : ar.header.d^(ar.n+1) ≤ 2^w)
    (packets : Physical.Owned.packetTrials ar.n ar.header.d ar.header.blocks*(ar.h*ar.s) < 2^w)
    (dyn : HeaderDecode.Layout) {p : Arg → Word w} {mc : TeamOpcode.Macros w 8}
    {reg : Bank w} {m : Memory w} {es u mu fs out final}
    (decode : Runs p mc HeaderDecode.program reg m es u mu)
    (minimum : Runs p mc CubeLengths.minimum u mu fs out final)
    (fits : HeaderDecode.Fits dyn w) (atFrame : HeaderDecode.AtFrame dyn (readings p) (readings m))
    (primary : readings p 0+63 < 2^w) (header : dyn.header+12 < 2^w) (totalsRoom : dyn.totals+dyn.a ≤ 2^w)
    (separate : dyn.dense+dyn.entries ≤ dyn.totals ∨ dyn.totals+dyn.a ≤ dyn.dense)
    (sumRoom : dyn.d*dyn.d*dyn.cap < 2^w) (radix : dyn.d = ar.header.d) (axes : dyn.a = ar.n+1)
    (bounds : CubeLengths.Fits w (readings p) (readings mu))
    (claimed : (CubeLengths.layout (readings p) (readings mu)).claimed=dyn.dense)
    (totals : (CubeLengths.layout (readings p) (readings mu)).totals=dyn.totals)
    (coords : (CubeLengths.layout (readings p) (readings mu)).coordinates=dyn.a)
    (chosen : (CubeLengths.layout (readings p) (readings mu)).chosen=decl.1.val)
    (stored : CubeLengths.StoredRows (readings mu) dyn.dense decl.2)
local notation "Raw" => f.receivedRows g group
set_option quotPrecheck false in
local notation "startRegs" => fun v : Fin (R+1) => (H v).history.val.2.1
set_option quotPrecheck false in
local notation "memory" => fun v : Fin (R+1) => (H v).history.val.2.2
set_option quotPrecheck false in
local notation:max "ownedWith" fit:arg fields:arg => writer.physicalOwnedEquiv ar decl label recv dataWidth group template id count scheduled
  symbols banks spacing room table fp source fit fields installed copies labels packets dyn decode minimum fits
  atFrame primary header totalsRoom separate sumRoom radix axes bounds claimed totals coords chosen stored

/-- Package the native ownership bijection with the true control and report operands.
The complete owned run, its recovered physical bank views, and its original tape
are produced by the word-level scheduler and scanner. -/
noncomputable def SharedWriters.deliveredBuilder
    (fit : ∀ u, CubeConstants.Fits pack w (readings (H u).pub 0) idBase id)
    (fields : ∀ u, CubeConstants.Fields pack (readings (H u).pub 0) idBase (readings (H u).history.val.2.2))
    (pinsOk : Matching ar owners decl Raw → Prop)
    (program : Matching ar owners decl Raw → Fin (R+1) → OpenSuffix.Inputs)
    (tested : ∀ a, let z := (ownedWith fit fields).symm a
      OpenSuffix.ControlFamily (program a) pub mac (fun v => (z v).val.2.1) (fun v => (z v).val.2.2) (pinsOk a))
    (data : ∀ a : Subtype pinsOk, ∀ v, let z := (ownedWith fit fields).symm a.val v
      LocalReportData ((H v).pub) ((H v).macros) z.val.2.1 z.val.2.2) :
    DeliveredBuilder ar owners decl Raw id pub mac startRegs memory := by
  refine ⟨installed,ownedWith fit fields,?_,pinsOk,program,tested,data⟩
  intro z
  unfold SharedWriters.physicalOwnedEquiv
  apply ownedEquiv_observed

/-- On this actual writer the assignment selected by the builder carries the
full original scanner receipts, including its physical cube and singleton banks. -/
theorem SharedWriters.deliveredReceipt
    (fit : ∀ u, CubeConstants.Fits pack w (readings (H u).pub 0) idBase id)
    (fields : ∀ u, CubeConstants.Fields pack (readings (H u).pub 0) idBase (readings (H u).history.val.2.2))
    (z : OwnedRuns ar pub mac
    (fun v => (installed v).val.2.1) (fun v => (installed v).val.2.2)) :
    let q := ((ownedWith fit fields) z).val
    let F := ownedHistory ar pub mac (fun v => (installed v).val.2.1) (fun v => (installed v).val.2.2) z
    ObservedOwned ar decl group F owners Raw q := by
  intro q F
  have obs : ObservedOwned ar decl (owners q.1) F owners Raw q := by
    dsimp only [q]
    unfold SharedWriters.physicalOwnedEquiv
    apply ownedEquiv_receipt
  have shape : Routed.trueDeclaration ar.b ar.s q.1=decl := ((ownedWith fit fields) z).property.1
  have equal := declaredTeam_eq (R := R) ar (Routed.trueDeclaration ar.b ar.s q.1) label recv dataWidth
    (Routed.physicalShared owners q)
  have assignment : group=owners q.1 :=
    scheduled.trans ((congrArg (fun x => declaredTeam ar x label recv dataWidth R) shape).symm.trans equal)
  exact assignment.symm ▸ obs

end TeamContraction

end BorderVNP
end Computability
end OAI
