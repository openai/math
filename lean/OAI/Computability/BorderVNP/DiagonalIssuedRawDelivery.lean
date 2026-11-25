import OAI.Computability.BorderVNP.DiagonalReturnedFragmentGeometry
import OAI.Computability.BorderVNP.DiagonalReturnedFragmentRawRows
import OAI.Computability.BorderVNP.DiagonalJointSparseWindow
import OAI.Computability.BorderVNP.FiniteProfilePublishedLabels

/-! # The same crossing cables and compact directory on the original team's arbitrary report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP BurstRAM TeamContraction ProcessorSlots FiniteEvaluator BorderVNP.Cube Physical
open PackedHistoryCircuit Packing Packing.RoutingOutputs Crossing CellAddresses CellAddressCircuit CellAddressPhysical
open Diagonal.ExternalSew.Fragments DiagonalTallyCellReports CompactMachine SignedTaskArena Tally

variable {R w n : ℕ} (a : SignedTaskArena.Layout) (U : Fin (R+1) → PinStart SparseExterior.driver n w)
    (u : Fin (R+1)) (p : (U u).Prefix a.id)
local notation3 (prettyPrint := false) "V" => visits a.id U p
local notation3 (prettyPrint := false) "pub" => (U u).pub
local notation3 (prettyPrint := false) "head" => ((U u).pub 0).val
local notation3 (prettyPrint := false) "out" => readings (V).reports.val.2.2
local notation3 (prettyPrint := false) "fr" => FragmentRows.Layout.fromFrame head out

variable {D sites ports axes k digits : ℕ} {P σ : Type} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (net : Network D P bits) (cell : net.Site → Fin a.cube.cells) (aux : net.Site → ℕ)
    (siteID : net.Site ↪ Fin sites) (edgeID : net.Edge ↪ Fin a.cube.cables) (portID : P ↪ Fin ports)
    (fields : Fields sites a.cube.cables ports a.cube.cells axes k digits σ) (x : σ → Bool)
    (dir : Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (origin base gap : ℕ) (profile placed : Memory w)
local notation3 (prettyPrint := false) "published" => readings (Directory.ISA.publish placed head base (dir.directory pp lp))
local notation3 (prettyPrint := false) "tables" => bases origin a.cube.cables a.cube.cells dir.entries
set_option maxHeartbeats 2200000
set_option maxRecDepth 7000

/-- The actual returned report keeps the source's three cable words, both
endpoint coordinates and all seven words at every occupied directory index.
This applies whether or not the proposed report will pass a private call. -/
theorem returned_raw_delivery
    {I : Type*} [Fintype I] {atSite : I → Fin a.cube.cells} {key : I ↪ ℕ} {widths : I → ℕ} {pins}
    (writer : SlottedWriter a.cube dir pp lp pins pub placed base atSite key widths)
    (wordTeams : dir.teams ≤ 2^w) (wordProcs : dir.processors ≤ 2^w) (wordFields : dir.fields ≤ 2^w)
    (wordLiteral : dir.literal < 2^w) (wordCells : a.cube.cells ≤ 2^w) (wordStride : a.cube.cellStride ≤ 2^w)
    {original : Fin dir.entries → Fin sites} {incoming : Fin (dir.teams*dir.sites) → Fin ports}
    (rep : Represents net cell aux siteID edgeID portID fields x) (ids : ∀ c, (fields.cells c).val=c.val)
    (fieldFit : ∀ c, guessedSize net cell c+siteSize net cell c aux+suppliedSize net cell c<2^digits)
    (image : Image fields original incoming x origin (readings profile))
    (slots : (privateLayout head origin a.cube.cables a.cube.cells dir.entries dir.description gap).Image
      (readings profile) dir.entries (readings placed))
    (header : Header head origin a.cube.cables a.cube.cells dir.entries (readings profile))
    (reserved : base+7*dir.candidates ≤ origin) (low : origin+5*a.cube.cables ≤ a.cube.header.header)
    (originFit : origin<2^w)
    {before : ℕ → ℕ} (keep : CubeAllocation.HostRetention a.cube head published before (readings (V).owned.val.2.2))
    {offsets ctl live portsCount bundles b : ℕ} (home : Fin bundles → Fin a.cube.cells)
    (payload : Fin bundles → BottomReports.BundleHeader)
    (ready : OpenSuffix.Ready (a.openInputs u.val head offsets ctl live portsCount bundles b home payload) head
      (readings (V).owned.val.2.2) w)
    (openPlace : OpenSuffix.Placement (a.openInputs u.val head offsets ctl live portsCount bundles b home payload)
      a.cube a.before head (readings (V).owned.val.2.2))
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor} {description : ℕ} (axis : Fin (a.cube.n+1))
    (seed : PreparedReportInput pub (V).controls.val.2.2 cs q description)
    (allocation : ReportAllocation a.before a.after (a.cube.cellWriter head ctl axis) l cs q) :
    CableRows net cell edgeID portID (fr).host out ∧
      (List.range (fr).count).map ((fr).row out)=dir.directory pp lp := by
  have retained := a.signed_report_words home payload (V).controls (V).reports seed keep ready openPlace allocation rfl
  have first := writer.rawStart
  have headerAfter := published_routing_header pp lp slots header first reserved
  have ends := (retained.frame_word 87 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)).trans headerAfter.ends
  have cables := (retained.frame_word 6 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)).trans headerAfter.cables
  have number := (retained.frame_word 7 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)).trans headerAfter.edges
  have count : (dir.directory pp lp).length < 2^w := by
    have le := dir.directory_length_le pp lp
    omega
  have stop : base+7*(dir.directory pp lp).length ≤ a.cube.header.header := by
    simpa only [Nat.mul_comm] using writer.rawEnd
  refine ⟨?_,(retained.returnedRows dir pp lp writer.pointers.1 first stop count
    (FiniteDiagonal.slotted_row_words writer wordTeams wordProcs wordFields wordLiteral wordCells wordStride)).1⟩
  apply CableRows.ofImage net cell edgeID portID _ _ aux siteID fields rep ids fieldFit image cables ends number
  intro z lower upper
  have early := writer.rawStart
  exact (retained.geometry z (by omega) (upper.trans_le low)).trans
    (published_cable_words pp lp slots first reserved z lower upper)

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
