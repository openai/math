import OAI.Computability.BorderVNP.DiagonalSignedCandidateCubeWords
import OAI.Computability.BorderVNP.DiagonalFrozenPaddingControls
import OAI.Computability.BorderVNP.DiagonalOpenedPacketBody
import OAI.Computability.BorderVNP.DiagonalSignedPhysicalReportData

/-! # The original emitted packet on the actual control return -/

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
/-- Before any report bits are chosen, the real control return has both the
published report-cell images and unchanged original packet words above its
control table. Those words include the sorted descriptors and their ranks. -/
theorem CandidateSite.opened_original_packet
    {supplied : Fin t.cube.cells → ℕ}
    (control : FrozenControlEntry t prog frame (ownedPub 0).val ctl (Bases.ends table) w supplied
      (readings site.receipt.history.dataInput) (readings out))
    (place : (privateLayout frame origin t.cube.cables t.cube.cells D₀.entries D₀.description gap).Image
      (readings site.geometry) D₀.entries (readings site.middle))
    (lo : frame+112≤receivingBase) (storage : receivingBase+7*D₀.candidates≤origin)
    (advance : Returns SignedPrep.controls ownedPub ownedMac ownedReg out) :
    readings advance.val.2.2=(pre).published (grouped groups host source (OpenSuffix.hostImage frame (readings out))) ∧
    ∀ j, ctl+37≤j → j<t.cube.header.header → readings advance.val.2.2 j=readings site.geometry j := by
  have image := (OpenSuffix.control_return_facts prog control.ready advance).2.2.2
  change readings advance.val.2.2=(pre).published (grouped groups host source (OpenSuffix.hostImage (ownedPub 0).val (readings out))) at image
  rw [control.frame] at image
  refine ⟨image,?_⟩
  have stable : CubeAllocation.HostRetention t.cube frame (readings site.published.val.2.2)
      (readings site.receipt.history.dataInput) (readings out) :=
    ⟨control.retained.primary,fun j below ne₁ ne₂ =>
      (control.retained.lower j below ne₁ ne₂).trans (congrArg Fin.val (site.receipt.done.low j below)),
      control.retained.tables⟩
  have start : CubeAllocation.HostRetention t.cube (readings ownedPub 0)
      (readings (Packing.Directory.ISA.publish site.middle (readings ownedPub 0) receivingBase (D₀.directory pp lp)))
      (readings site.receipt.history.dataInput) (readings out) := by
    change CubeAllocation.HostRetention t.cube (ownedPub 0).val
      (readings (Packing.Directory.ISA.publish site.middle (ownedPub 0).val receivingBase (D₀.directory pp lp)))
      (readings site.receipt.history.dataInput) (readings out)
    rw [control.frame,←site.actual]
    exact stable
  have width : receivingBase+7*(D₀.directory pp lp).length≤origin :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left 7 (D₀.directory_length_le pp lp)) _).trans storage
  intro j after below
  have head : readings ownedPub 0=(pub 0).val := control.frame
  exact opened_body_from_geometry (sa:=t) (team:=team.val) (offsets:=(Bases.ends table)) («ctl»:=ctl)
    (live:=(Bases.livePairs table)) (ports:=D₀.teams*D₀.sites) (b:=b) host (ReportBundle.header ∘ source)
    (pub:=ownedPub) (mac:=ownedMac) (s:=ownedReg) (entry:=out) (origin:=origin)
    (cables:=t.cube.cables) (cells:=t.cube.cells) (entries:=D₀.entries) (rect:=D₀.teams*D₀.sites)
    (desc:=D₀.description) (gap:=gap) (next:=receivingBase) (geometry:=site.geometry) (placed:=site.middle)
    (D₀.directory pp lp) (by simpa only [head] using place) (by simpa only [head] using lo)
    width start advance (by simpa only [head,control.frame] using control.ready)
    (by simpa only [head] using control.placement) rfl j after below

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
