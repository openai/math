import OAI.Computability.BorderVNP.DiagonalCandidateReportedMarkers
import OAI.Computability.BorderVNP.DiagonalReachedOpenFields
import OAI.Computability.BorderVNP.DiagonalCandidateStartupWords

/-! # The reached control words and typed geometry on an issued report -/

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

open SignedTaskArena FragmentRows GeometryAdvice

/-- The issued sparse compiler reads the returned report RAM. Its input
contains the same grouped rows and the untouched public marker tables
that the native opening received at this site. -/
structure IssuedGeometry (task : SignedTaskArena.Layout) (team frame offsets ctl live ports word : ℕ)
    (profile source opened reported : ℕ → ℕ) : Prop where
  /-- The grouped rows at the return of the original control scan. -/
  grouped : opened=(task.controlRows team frame offsets ctl live ports).published source
  /-- The packet body, after the fixed 37 control words, retains the profile image. -/
  body : ∀ z, ctl+37≤z → z<task.cube.header.header → opened z=profile z
  /-- The scalar frame of the actual compact task rows. -/
  fields : (task.controlRows team frame offsets ctl live ports).Fields reported
  /-- The native word width at primary word 30. -/
  wordWidth : reported (frame+30)=word
  /-- The first private call directory follows the pre-task allocation. -/
  callLimit : reported (frame+14)=task.before.limit
  /-- The actual location of the emitted task array. -/
  tasks : reported (frame+89)=(task.tasks team frame offsets ctl).tasks
  /-- The indirect pointer to the real task controls. -/
  pointer : reported (frame+92)=ctl
  /-- All scalar controls are the ones installed for this task. -/
  controls : ∀ i : Fin 37, reported (ctl+i.val)=task.controls i.val
  /-- The report address ranges fit the native sparse reservation. -/
  placement : task.SparsePlacement frame ctl
  /-- The marked sections retain their stored counts, inverses, and owner. -/
  geometry : TaskSourceGeometry task frame offsets ctl reported (some team)

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


local notation3 (prettyPrint := false) "baseRAM" => readings site.geometry

omit [Fintype P] [Fintype A] in
/-- Extract all physical control and geometry fields of a reached candidate
before launching its sparse encoder. The source is the opened host, and the
output is this very report return. -/
theorem CandidateSite.issued_report_geometry
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
    (bank : banks.bankStart=t.cube.cellBank) (stride : banks.stride=t.cube.cellStride)
    (room : t.OpenRoom frame (Bases.ends table) ctl (Bases.livePairs table) (D₀.teams*D₀.sites) D₀.entries (2^b) w)
    (original : baseRAM (frame+30)=w ∧ baseRAM (frame+14)=t.before.limit ∧ baseRAM (frame+89)=(t.tasks 0 0 0 0).tasks)
    : IssuedGeometry t team.val (ownedPub 0).val (Bases.ends table) ctl (Bases.livePairs table) (D₀.teams*D₀.sites)
      w (readings site.geometry) (grouped groups host source (OpenSuffix.hostImage frame (readings out)))
      (readings advance.val.2.2) (readings report.val.2.2) := by
  have outer := site.task_header_inputs N t cell recv size raw place lo (by omega) original
  have boot := control.writerOpenFields t host (ReportBundle.header ∘ source)
  have scalars := control.reported_fields t host (ReportBundle.header ∘ source) boot outer.1 outer.2.1 outer.2.2
    room advance report seed alloc bank
  have geometry := site.report_task_geometry N t cell recv size raw team host source counts control place lo storage
    advance alloc seed report dest start cap total cube sorted ranks bank stride
  have opened := site.opened_original_packet N t cell recv size raw team host source control place lo storage advance
  rw [control.frame]
  exact ⟨opened.1,opened.2,scalars.1,scalars.2.1,scalars.2.2.1,scalars.2.2.2.1,
    scalars.2.2.2.2.1,scalars.2.2.2.2.2,geometry.1,geometry.2⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
