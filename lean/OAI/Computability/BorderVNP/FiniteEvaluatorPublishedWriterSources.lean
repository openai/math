import OAI.Computability.BorderVNP.FiniteEvaluatorDeclarationReturn
import OAI.Computability.BorderVNP.FiniteEvaluatorRouteScheduleOwners
import OAI.Computability.BorderVNP.RoutingISASignedPrepRange
import OAI.Computability.BorderVNP.FiniteEvaluatorSharedCubeSource

/-! # Signed scanner and declaration data on the actual published finite schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout

open Crossing _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.GroupWeights Cube.LabelIndex Cube.Tally
open RoutingISA RoutingISA.LocalRow CubeHeaderInstall TeamContraction TeamContraction.JointHeader
open VPVNP.BurstRAM Evaluator Transmission FiniteEvaluator
open scoped Classical

variable {D w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
    {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
    (V : FieldRawLayout L S) (R header profile cells cables maxRows stride : ℕ)
    {dirLayout : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {pins : Pins.Layout}
    {pub : Arg → Word w} {slotted : Memory w} {base : ℕ}
    {I : Type*} [Fintype I] {cell : I → Fin cells} {id : I ↪ ℕ} {sizes : I → ℕ}

local notation "ar" => planArena L R header profile cells cables maxRows stride
local notation "rows" => Packing.Directory.Layout.directory dirLayout pp lp
local notation "initialRAM" => Packing.Directory.ISA.publish slotted (Fin.val (pub 0)) base rows

variable (placement : SlottedWriter (planArena L R header profile cells cables maxRows stride) dirLayout pp lp pins pub slotted base cell id sizes)
    (f : BroadcastFrame) (old : Fin 81 → Word w) (fresh gates outputs width off ell controls : ℕ)
    (mac : TeamOpcode.Macros w 8) (reg : Bank w) (G : List Bool) (claims : List (List Bool)) (pad X : ℕ)
    (rawDecl : L.Declaration)
    (table : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F)
    (taskParams : SignedTaskArena.Parameters) (origin raw subtotal : ℕ)

local notation3 (prettyPrint := false) "frame" => (pub 0).val
local notation3 (prettyPrint := false) "index" => readCode (L.dimension+1) rawDecl.1
local notation3 (prettyPrint := false) "axis" => Fin.ofNat (L.dimension+1) index
local notation3 (prettyPrint := false) "decl" =>
  (Prod.mk axis (fun (p : Sym2 (Fin L.alphabet)) (j : Fin (L.dimension+1)) => readCode ((ar).header.cap+1) (rawDecl.2 p j)))
local notation3 (prettyPrint := false) "group" => declaredTeam ar decl L.label V.recv V.dataWidth R
local notation "sch" => scheduleGroups L.dimension (selectorWidth L.dimension L.alternatives L.copies)
local notation3 (prettyPrint := false) "task" => signedPlanArena L R header profile cells cables maxRows stride table taskParams
local notation3 (prettyPrint := false) "prev" => PackedHistoryCircuit.routingExtension
  ((signedPlanArena L R header profile cells cables maxRows stride table taskParams).extension raw f.team subtotal old)
  dirLayout origin cables cells

include placement

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
/-- The complete schedule on an arbitrary raw finite declaration recovers the
decoder and all operands of the field writer on its actual returned memory.
The owner function comes from the finite packet's real labels and receiving rows. -/
theorem published_writer_sources
    (room : SignedPrep.PinnedRawInput («ar» := planArena L R header profile cells cables maxRows stride)
      (D := dirLayout) (pp := pp) (lp := lp) (pub := pub) (slotted := slotted) (base := base)
      f (PackedHistoryCircuit.routingExtension
        ((signedPlanArena L R header profile cells cables maxRows stride table taskParams).extension raw f.team subtotal old)
        dirLayout origin cables cells) fresh gates outputs width off ell controls G claims pad rawDecl R X)
    (replay : (ar).ReplayRoom w (readings pub 0))
    (number : L.Cell ≃ Fin (LabelIndex.layout frame (readings initialRAM)).cells)
    (edgeOrd : N.CrossingEdge L.cell ↪ Fin (LabelIndex.layout frame (readings initialRAM)).cableCount)
    (dataOrd : V.Operand ↪ Fin (LabelIndex.layout frame (readings initialRAM)).deliveryCount)
    (traffic : RowPlacement (networkRows N L.cell V.recv V.dataWidth)
      (fromTables (LabelIndex.layout frame (readings initialRAM)) (readings initialRAM) room.labels.endpoints)
      number (edgeOrd.sumMap dataOrd))
    (labels : L.label=meanPackedLabel N L.cell V.recv V.dataWidth
      ((List.finRange (LabelIndex.layout frame (readings initialRAM)).cells).map number.symm)
      L.dimension L.alphabet (by have h := room.alphabet; change 2 ≤ L.alphabet at h; omega))
    (space : (task).after.packed ≤ 2^w) {es out after}
    (running : Runs pub mac sch reg initialRAM es out after) :
    ∃ selected : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub mac reg initialRAM,
      let input := powerHeaderImage ar f.dst (readings selected.val.2.2)
      let owner := (ar).receivingOwner frame axis R input
      Nonempty (DeclarationReturn decl pub mac) ∧
      ∃ H : WriterHistory L.dimension (selectorWidth L.dimension L.alternatives L.copies)
          pub mac reg initialRAM es out after,
        ReturnedWriters ar dirLayout pp lp owner decl group pins H ∧
        SharedCubeWords task decl group f.team (readings pub) (readings H.sharedInput) (rows).length := by
  obtain ⟨tr,next,selected,labelRun,_,_,source,full⟩ := V.field_schedule R header profile cells cables maxRows stride placement
    f prev fresh gates outputs width off ell controls mac reg G claims pad X rawDecl room.boot room.geometry
    room.frameSpace room.copied room.alphabet room.blocks room.bank room.arena room.labels room.cells room.teamCount
    room.budget room.million room.scaled room.controlLow room.pointers room.processors room.payload room.fields
    room.rawSpace room.records number edgeOrd dataOrd traffic labels
  obtain ⟨_,H,written⟩ := full.2 running
  obtain ⟨valid,parsed⟩ := DeclarationReturn.ofWriterHistory pub mac reg initialRAM ar G claims pad rawDecl f prev
    fresh gates outputs width off ell room.boot room.geometry room.copied replay room.labels H
  have same : axis = ⟨index,valid.1⟩ := Fin.ext (Nat.mod_eq_of_lt valid.1)
  refine ⟨⟨(tr,next,selected),labelRun⟩,?_⟩
  intro input owner
  refine ⟨by rw [same]; exact parsed,H,written,?_⟩
  exact H.shared_cube_words task old dirLayout origin cables cells raw f.team subtotal fresh G.length gates outputs width
    off ell decl group written room.boot space room.frameSpace replay.axes controls f.team input source

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
