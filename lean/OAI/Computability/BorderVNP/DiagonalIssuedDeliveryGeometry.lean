import OAI.Computability.BorderVNP.DiagonalIssuedRawDelivery
import OAI.Computability.BorderVNP.DiagonalPublishedRowLocations

/-! # The four original reported delivery fields on arbitrarily submitted signed prefixes -/

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
    (dir : Directory.Layout) (origin base gap : ℕ) (profile placed : Memory w)
local notation3 (prettyPrint := false) "sourcePairs" => Directory.ISA.placement (readings placed)
    (bases origin a.cube.cables a.cube.cells dir.entries).privatePairs
local notation3 (prettyPrint := false) "livePairs" => Directory.ISA.placement (readings placed)
    (bases origin a.cube.cables a.cube.cells dir.entries).livePairs
local notation3 (prettyPrint := false) "published" => readings (Directory.ISA.publish placed head base (dir.directory sourcePairs livePairs))
local notation3 (prettyPrint := false) "tables" => bases origin a.cube.cables a.cube.cells dir.entries
set_option maxHeartbeats 2200000
set_option maxRecDepth 7000

/-- Read the actual sparse submission’s cable model, literal directory list,
original arrival coordinates and the destination of each supplied bundle. The private and live pointers are always those
published on this very team's own placement result. -/
theorem returned_issued_delivery
    {I : Type*} [Fintype I] {atSite : I → Fin a.cube.cells} {key : I ↪ ℕ} {widths : I → ℕ} {pins}
    (writer : SlottedWriter a.cube dir sourcePairs livePairs pins pub placed base atSite key widths)
    (wordTeams : dir.teams ≤ 2^w) (wordProcs : dir.processors ≤ 2^w) (wordFields : dir.fields ≤ 2^w)
    (wordLiteral : dir.literal < 2^w) (wordCells : a.cube.cells ≤ 2^w) (wordStride : a.cube.cellStride ≤ 2^w)
    (original : Fin dir.entries ↪ net.Site) (livePorts : (Fin dir.teams × Fin dir.sites) ↪ P)
    (bounds : dir.DestinationBounds) (portWidth : ∀ i, bits (livePorts i)=dir.block)
    (rep : Represents net cell aux siteID edgeID portID fields x) (ids : ∀ c, (fields.cells c).val=c.val)
    (fieldFit : ∀ c, guessedSize net cell c+siteSize net cell c aux+suppliedSize net cell c<2^digits)
    (image : Image fields (siteID ∘ original) (portID ∘ livePorts ∘ finProdFinEquiv.symm) x origin (readings profile))
    (slots : (privateLayout head origin a.cube.cables a.cube.cells dir.entries dir.description gap).Image
      (readings profile) dir.entries (readings placed))
    (room : (privateLayout head origin a.cube.cables a.cube.cells dir.entries dir.description gap).Fits w (readings profile))
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
    (allocation : ReportAllocation a.before a.after (a.cube.cellWriter head ctl axis) l cs q)
    {bundles₀ : ℕ} (entry : Fin bundles₀ ↪ Fin dir.entries) (arrives : Fin bundles₀ → Fin a.cube.cells)
    (atDestination : ∀ j, cell (original (entry j))=arrives j) :
    let rows := NativeDemands.rows net cell edgeID portID dir original livePorts gap
    let receiver := NativeDemands.receiver net cell edgeID portID dir original livePorts gap bounds
    CableRows net cell edgeID portID (fr).host out ∧
      (List.range (fr).count).map ((fr).row out)=dir.directory sourcePairs livePairs ∧
      ∃ _ : Directory.RowLocations (dir.directory sourcePairs livePairs) Fin.val receiver (fun i : Fin rows.length => rows[i.val].width),
      ∀ j, (sourcePairs (entry j).val).1=(arrives j).val := by
  intro rows receiver
  obtain ⟨cables,rawRows⟩ := returned_raw_delivery a U u p net cell aux siteID edgeID portID fields x dir
    sourcePairs livePairs origin base gap profile placed writer wordTeams wordProcs wordFields wordLiteral wordCells
    wordStride rep ids fieldFit image slots header reserved low originFit keep home payload ready openPlace axis seed allocation
  have locations := NativeDemands.publishedRowLocations net cell edgeID portID dir original livePorts gap aux siteID
    fields x head origin (readings profile) (readings placed) rep ids fieldFit portWidth image slots room bounds
  refine ⟨cables,rawRows,locations,fun j => ?_⟩
  have pos := NativeDemands.publishedPrivatePlacement net cell edgeID portID dir original livePorts gap aux siteID
    fields x head origin (readings profile) (readings placed) rep ids fieldFit portWidth image slots room (entry j)
  exact (congrArg Prod.fst pos).trans (congrArg Fin.val (atDestination j))

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
