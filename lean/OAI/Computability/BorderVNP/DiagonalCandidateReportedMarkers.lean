import OAI.Computability.BorderVNP.DiagonalCandidateOpenedMemory
import OAI.Computability.BorderVNP.DiagonalOwnedReportExtentRows
import OAI.Computability.BorderVNP.FragmentTaskRetainedRanks

/-! # Original descriptor ranks through an actual signed report return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.GroupWeights Cube.LabelIndex Cube.Tally
open CubeHeaderInstall CubeArena TeamContraction TeamContraction.JointHeader LocalRow Transmission
open VPVNP.BurstRAM
open Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical Packing.RoutingOutputs
open VPVNP.VerifierNetwork Packing.Inherited Packing.BottomReports DiagonalTallyCellReports
open DiagonalTallyAllocation ReportDirectory DiagonalResidueRAM FiniteEvaluator GeometryFrameEncoding
open scoped Classical

variable {D w R X : ℕ} {P A : Type} [Fintype P] [Fintype A] {bits : P → ℕ}
    (N : Network D P bits) (t : SignedTaskArena.Layout) (cell : N.Site → Fin t.cube.cells)
    (recv : A → Fin t.cube.cells) (size : A → ℕ) {D₀ : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w} {mem : Memory w}
    {initialBase receivingBase : ℕ} {pins : Pins.Layout} {fields : Pins.ProcessorFields pins} {f : BroadcastFrame}
    {guess : ℕ → Bool} {I : Type*} [Fintype I] {resides : I → Fin t.cube.cells} {keyID : I ↪ ℕ} {sizes : I → ℕ}
    {representative : ℕ → Fin (R+1)} {group : Fin t.cube.header.d → Fin (R+1)}
    (raw : Broadcast t.cube.n t.cube.header.d t.cube.header.cap)
local notation3 (prettyPrint := false) "dec" => Prod.mk (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1))
  (fun (p : Sym2 (Fin t.cube.header.d)) (j : Fin (t.cube.n+1)) => readCode (t.cube.header.cap+1) (raw.2 p j))
variable (site : CandidateSite (X:=X) t.cube D₀ pp lp raw representative
      (Prod.mk (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1))
        (fun (p : Sym2 (Fin t.cube.header.d)) (j : Fin (t.cube.n+1)) => readCode (t.cube.header.cap+1) (raw.2 p j)))
      group initialBase receivingBase pins fields f guess pub mac reg mem resides keyID sizes N cell recv size)
    {origin : ℕ}
local notation3 (prettyPrint := false) "frame" => (pub 0).val
local notation "table" => bases origin t.cube.cables t.cube.cells D₀.entries
local notation "ctl" => controlsBase origin t.cube.cables t.cube.cells D₀.entries (D₀.teams*D₀.sites)
variable (team : Fin (R+1)) (host : Fin D₀.entries → Fin t.cube.cells) (source : Fin D₀.entries → ReportBundle)
    {b gap : ℕ} {ownedPub : Arg → Word w} {ownedMac : TeamOpcode.Macros w 8} {ownedReg : Bank w} {out : Memory w}
local notation "prog" => t.openInputs team.val frame (Bases.ends table) ctl (Bases.livePairs table) (D₀.teams*D₀.sites)
  D₀.entries b host (ReportBundle.header ∘ source)
local notation "pre" => t.controlRows team.val frame (Bases.ends table) ctl (Bases.livePairs table) (D₀.teams*D₀.sites)
local notation "groups" => t.bundleLayout frame ctl D₀.entries

omit [Fintype P] [Fintype A] in
/-- Both markers of every descriptor are in the protected original packet
range; the very control return of this candidate retains their values. -/
theorem CandidateSite.opened_marker_bounds
    {supplied : Fin t.cube.cells → ℕ}
    (control : FrozenControlEntry t prog frame (ownedPub 0).val ctl (Bases.ends table) w supplied
      (readings site.receipt.history.dataInput) (readings out))
    (place : (privateLayout frame origin t.cube.cables t.cube.cells D₀.entries D₀.description gap).Image
      (readings site.geometry) D₀.entries (readings site.middle))
    (lo : frame+112≤receivingBase) (storage : receivingBase+7*D₀.candidates≤origin)
    (advance : Returns SignedPrep.controls ownedPub ownedMac ownedReg out)
    (dirs : SignedTaskArena.GeometryDirectories) {C : ℕ} (ranks : dirs.MarkerBounds C (readings site.geometry))
    (lower : ctl+37≤dirs.sorted+dirs.padded) (upper : dirs.sorted+2*dirs.padded≤t.cube.header.header) :
    dirs.MarkerBounds C (readings advance.val.2.2) := by
  have kept := site.opened_original_packet N t cell recv size raw team host source control place lo storage advance
  exact ranks.retained le_rfl (fun j h₁ h₂ => kept.2 j (lower.trans h₁) (h₂.trans_le upper))

section Task

open SignedTaskArena FragmentRows GeometryAdvice
variable {fresh fieldHeader gates outputs bitWidth descriptorColumn : ℕ}
local notation3 (prettyPrint := false) "tapeStart" => Allocation.dest fresh fieldHeader gates outputs bitWidth
local notation3 (prettyPrint := false) "report₀" => reportLayout t.before t.after frame ctl t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
local notation3 (prettyPrint := false) "dirs" => SignedTaskArena.GeometryDirectories.mk t.p.sorted t.p.padded t.p.stops t.p.bundlePayload t.p.bundleInverse
variable (counts : ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool)
local notation3 (prettyPrint := false) "cs₀" => directoryCells groups pre report₀ host source
  (grouped groups host source (OpenSuffix.hostImage frame (readings out))) counts

set_option maxRecDepth 7000
set_option maxHeartbeats 2200000

omit [Fintype P] [Fintype A] in
/-- On any actual returned report of this candidate, the descriptor markers
are read from the original attained geometry return and the task extent
is needed precisely at the physical rows owned by this team. -/
theorem CandidateSite.report_task_geometry
    {supplied : Fin t.cube.cells → ℕ}
    (control : FrozenControlEntry t prog frame (ownedPub 0).val ctl (Bases.ends table) w supplied
      (readings site.receipt.history.dataInput) (readings out))
    (place : (privateLayout frame origin t.cube.cables t.cube.cells D₀.entries D₀.description gap).Image
      (readings site.geometry) D₀.entries (readings site.middle))
    (lo : frame+112≤receivingBase) (storage : receivingBase+7*D₀.candidates≤origin)
    (advance : Returns SignedPrep.controls ownedPub ownedMac ownedReg out)
    {banks : CellBanks.Layout} {q : ReportCursor} {description : ℕ}
    (alloc : ReportAllocation t.before t.after banks report₀ cs₀ q) (seed : PreparedReportInput ownedPub advance.val.2.2 cs₀ q description)
    (report : Returns prepareCellReports ownedPub ownedMac advance.val.2.1 advance.val.2.2)
    (dest : origin=tapeStart) (start : frame+112 ≤ fresh) (cap : t.cube.cells≤t.p.report.cells)
    (total : t.cube.cables*3+(Packing.RoutingOutputs.count t.cube.cables t.cube.cells D₀.entries (D₀.teams*D₀.sites)+
      ((t.cube.cells+(D₀.entries+t.cube.cells))+(37+(descriptorColumn+2*t.p.padded)))) ≤ outputs)
    (cube : t.cube.header.header=Allocation.stop fresh fieldHeader gates outputs bitWidth w)
    (sorted : t.p.sorted=ctl+37+descriptorColumn) (ranks : (dirs).MarkerBounds t.cube.cells (readings site.geometry))
    (bank : banks.bankStart=t.cube.cellBank) (stride : banks.stride=t.cube.cellStride) :
    t.SparsePlacement frame ctl ∧ TaskSourceGeometry t frame (Bases.ends table) ctl (readings report.val.2.2) (some team.val) := by
  have next : origin+outputs ≤ t.cube.header.header := by
    rw [dest,cube]; dsimp only [Allocation.stop,Allocation.packed,Allocation.dense]; omega
  have afterControl : ctl+37+descriptorColumn+2*t.p.padded≤origin+outputs := by
    dsimp only [controlsBase,bases,Packing.RoutingOutputs.count] at total ⊢
    omega
  have typed := site.opened_marker_bounds N t cell recv size raw team host source control place lo storage advance dirs
    ranks (by dsimp only; omega) (by dsimp only; omega)
  have setup := t.signedReport_owned_inputs host source counts (by simpa only [control.frame] using control.ready)
    control.frame advance
  obtain ⟨tape,rfl⟩ := (reportReturnEquiv seed ownedMac advance.val.2.1).surjective report
  subst origin
  have trueFrame : readings ownedPub 0=frame := control.frame
  have built := reportReturn_task_geometry_owned alloc seed ownedMac advance.val.2.1 tape (trueFrame.symm ▸ start)
    cap total cube sorted typed trueFrame.symm bank stride setup.1 team.val setup.2
  simpa only [trueFrame] using built

end Task
end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
