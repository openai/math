import OAI.Computability.BorderVNP.DiagonalMinimumOwnedEquiv
import OAI.Computability.BorderVNP.DiagonalReplaySignedBuilder
import OAI.Computability.BorderVNP.DiagonalSignedWriterDictionary

/-! # The signed owned scanner chosen by the checked public declaration -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment DiagonalTallyPacketEmit
open private declaredTeam_eq from OAI.Computability.BorderVNP.CubeScatterReturnedOwnedFamily
open FiniteEvaluator
open scoped BigOperators

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
    {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins}
    (task : SignedTaskArena.Layout) (decl : LengthDeclaration task.cube.n task.cube.header.d)
    {Cell Data : Type*} [Fintype Data] (label : Cell → Label (task.cube.n+1) task.cube.header.d)
    (recv : Data → Cell) (dataWidth : Data → ℕ)
    (group : Fin task.cube.header.d → Fin (R+1)) (template : Frame) (frame dataCount : ℕ)
    {src : Fin (R+1) → ℕ → ℕ} (writer : SharedWriters f (task.cube.sharedRows frame decl.1.val dataCount) src)

local notation "ar" => task.cube
local notation3 (prettyPrint := false) "g" => task.cube.sharedRows frame decl.1.val dataCount
local notation3 (prettyPrint := false) "raw" => f.receivedRows g group
local notation3 (prettyPrint := false) "own" => greedyOwner R task.cube.b task.cube.s label recv dataWidth
local notation "total" => dataCount+task.cube.header.d.choose 2
local notation3 (prettyPrint := false) "pub" => fun u : Fin (R+1) => (H u).pub
local notation3 (prettyPrint := false) "mac" => fun u : Fin (R+1) => (H u).macros

set_option maxHeartbeats 1250000 in
include writer in
/-- Every physical return determines a distributed routed assignment and
every matching assignment runs on the same installed hardware. The receive
buffers, owned endpoints and selector observations refer to this scanner's
actual execution, before any report digits are sampled. -/
theorem SharedWriters.signedOwnedAtMinimum
    (common : ∀ u, readings (H u).pub 0=frame)
    (tab : f.table=(ar).table frame total) (space : task.after.packed ≤ 2^w)
    (values : CubeConstants.valueBound task.id < 2^w)
    (room : ∀ u, (ar).ReplayRoom w (readings (H u).pub 0))
    (words : ∀ u, SharedCubeWords task decl group u.val (readings (H u).pub) (src u) dataCount)
    (scheduled : group=declaredTeam ar decl label recv dataWidth R)
    (least : decl.1=firstMinimum (fun j => ∑ pair,decl.2 pair j))
    (copies : 1≤(ar).K) (labels : (ar).header.d^((ar).n+1)≤2^w)
    (packets : Physical.Owned.packetTrials (ar).n (ar).header.d (ar).header.blocks*((ar).h*(ar).s)<2^w) :
    ∃ installed : (u : Fin (R+1)) → Returns (CubeConstants.install task.id) (H u).pub (H u).macros
        (H u).history.val.2.1 (H u).history.val.2.2,
    let regs := fun u => (installed u).val.2.1
    let mem := fun u => (installed u).val.2.2
    ∃ E : OwnedRuns ar pub mac regs mem ≃ Matching ar own decl raw,
      ∀ z, let observed := ownedHistory ar pub mac regs mem z
        OwnedHandoff f g src ar decl group template task.id total observed ∧
          ObservedOwned ar decl group observed own raw (E z).val := by
  obtain ⟨installed,loaded⟩ := writer.signedInstallFromWriterWords task decl group template frame dataCount
    common tab space values room words
  refine ⟨installed,?_⟩
  intro regs mem
  have physical u : f.table=(ar).table (readings (H u).pub 0) total := (common u).symm ▸ tab
  have handoff (z : OwnedRuns ar pub mac regs mem) : OwnedHandoff f g src ar decl group template task.id total
      (ownedHistory ar pub mac regs mem z) :=
    ⟨fun _ => rfl,fun _ => rfl,rfl,rfl,room,physical,fun u => (common u).symm,fun u => (words u).scanner,
      fun u => (loaded u).1,fun u => (loaded u).2.1,fun u => ⟨_,(installed u).property⟩⟩
  have symbols : SymbolFrame g (src 0) (ar).header.blocks (ar).K (ar).h decl group := common 0 ▸ (words 0).symbols
  let E := writer.minimumOwnedEquiv ar decl label recv dataWidth group template task.id total scheduled symbols
    rfl rfl room physical (fun u => (common u).symm) (fun u => (words u).scanner)
    (fun u => (loaded u).1) (fun u => (loaded u).2.1) installed copies labels packets least
  refine ⟨E,fun z => ⟨handoff z,?_⟩⟩
  exact writer.minimumOwnedReceipt ar decl label recv dataWidth group template task.id total scheduled symbols
    rfl rfl room physical (fun u => (common u).symm) (fun u => (words u).scanner)
    (fun u => (loaded u).1) (fun u => (loaded u).2.1) installed copies labels packets least z

include writer in
/-- Join the physically reconstructed public rows and owned histories to
the actual four controls and their certified local report/argument
producers. The resulting builder has both the source's padding predicate
and its exact immutable per-team report files. -/
theorem SharedWriters.signedReportBuilder (reports : SourceReports ar own)
    (common : ∀ u, readings (H u).pub 0=frame)
    (tab : f.table=(ar).table frame total) (space : task.after.packed ≤ 2^w)
    (values : CubeConstants.valueBound task.id < 2^w)
    (room : ∀ u, (ar).ReplayRoom w (readings (H u).pub 0))
    (words : ∀ u, SharedCubeWords task decl group u.val (readings (H u).pub) (src u) dataCount)
    (scheduled : group=declaredTeam ar decl label recv dataWidth R)
    (least : decl.1=firstMinimum (fun j => ∑ pair,decl.2 pair j)) (copies : 1≤(ar).K)
    (afterOwned : ∀ (q : Matching ar own decl raw) (F : TeamRows.Returns (Fin (R+1)) ar w),
      OwnedHandoff f g src ar decl group template task.id total F →
      ObservedOwned ar decl group F own raw q.val →
      ∃ program : Fin (R+1) → OpenSuffix.Inputs,
        OpenSuffix.ControlFamily program F.pub F.macros F.finalRegs F.output (reports.pins q.val) ∧
          (reports.pins q.val → ∀ u, ∃ v : LocalReportData (F.pub u) (F.macros u) (F.finalRegs u) (F.output u),
            SameReportCells v.cells (reports.cells q.val u))) :
    ∃ B : DeliveredBuilder ar own decl raw task.id pub mac (fun u => (H u).history.val.2.1)
      (fun u => (H u).history.val.2.2), B.matchesSource reports ∧
      ∀ q : Matching ar own decl raw,
        let endRows := ownedHistory ar pub mac (fun u => (B.constants u).val.2.1) (fun u => (B.constants u).val.2.2)
          (B.owned.symm q)
        OwnedHandoff f g src ar decl group template task.id total endRows ∧
          ObservedOwned ar decl group endRows own raw q.val := by
  classical
  have scan := task.signed_owned_scan_words (room 0)
  obtain ⟨installed,E,attained⟩ := writer.signedOwnedAtMinimum task decl label recv dataWidth group template frame dataCount
    common tab space values room words scheduled least copies scan.1 scan.2
  let regs u := (installed u).val.2.1
  let mem u := (installed u).val.2.2
  let F := ownedHistory ar pub mac regs mem
  have reached (q : Matching ar own decl raw) :
      ObservedOwned ar decl group (F (E.symm q)) own raw q.val := by
    exact Eq.mp (congrArg (fun v => ObservedOwned ar decl group (F (E.symm q)) own raw v)
      (congrArg Subtype.val (E.apply_symm_apply q))) (attained (E.symm q)).2
  choose program control cells using fun q => afterOwned q (F (E.symm q)) (attained (E.symm q)).1 (reached q)
  let passes (q : Matching ar own decl raw) := reports.pins q.val
  choose row correct using fun (q : Subtype passes) u => cells q.val q.property u
  let B : DeliveredBuilder ar own decl raw task.id pub mac (fun u => (H u).history.val.2.1)
      (fun u => (H u).history.val.2.2) :=
    { constants := installed
      owned := E
      observes z := (Routed.realizes_iff own Fin.valEmbedding ((F z).layout ar Fin.valEmbedding decl)
        (fun _ => (ar).header.packetBase) (fun _ => (ar).singleBank) (fun _ => rfl) (fun _ => rfl)
        (E z).val ((F z).observed ar decl raw)).mp (attained z).2.observed
      pins := passes
      controlsAt := program
      paths := control
      localRows := row }
  exact ⟨B,⟨fun _ => Iff.rfl,correct⟩,fun q => ⟨(attained (E.symm q)).1,reached q⟩⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
