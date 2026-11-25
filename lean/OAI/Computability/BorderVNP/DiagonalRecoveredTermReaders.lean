import OAI.Computability.BorderVNP.CubePhysicalReceivedReportReaders
import OAI.Computability.BorderVNP.DiagonalEnrichedReturnedReaders
import OAI.Computability.BorderVNP.DiagonalBottomChoices
import OAI.Computability.BorderVNP.DiagonalReceivedScalarReaders
import OAI.Computability.BorderVNP.DiagonalNativeCoreDirectory

/-! # The complete operand ledger on a decoded, supported physical core -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.EnrichedTape

open Crossing Shortening Adaptive Packing Packing.DeckGrid Cover TeamContraction ExternalSew GridHosts
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PublicCapacity VPVNP BorderVNP.Cube MvPolynomial
open scoped BigOperators Classical BorderVNP.Epoch.Cube

universe u

variable {D m start T : ℕ} [NeZero D] {K E Gadget : Type} [Field K] [Field E] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {Word : ℕ → Type} [∀ t, Fintype (Word t)]
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {w : ℕ → ℕ → ℕ}
    {R r pins link k axes gridDepth a regs rw ec width s copies : ℕ}
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
    {order : Fin (tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D axes gridDepth order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (free : Fin (R+1) → Fin r → Fin a → Bool)
    {deep : S.floor+1+S.drop*T ≤ start} (count : (EnrichedOuter.fan S)^T*copies = R+1)
    {good : ∀ j, EnrichedOuter.State S start (Fin (tileCount axes gridDepth))
      (fun _ => copies*inputBlockWidth r (k+1) axes gridDepth) shape Word j → Prop}
    (M : EnrichedOuter.Machine.{0,u} deep good V w) (bottom : EnrichedOuter.Admissible good 0)
    (installed : bottom.val.pack.layout = (wiredGrid (tapeTemplate p fit pins) axes gridDepth order position).groupedRepeat
      (fun _ : Fin (tileCount axes gridDepth) => inputBlockWidth r (k+1) axes gridDepth) order copies)
    (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (hg : 0 < inputBlockWidth r (k+1) axes gridDepth)

set_option synthInstance.maxSize 4000

/-- Enumerate the true original batch numbers in the nested public history. -/
noncomputable local instance recoveredReadTeams {j : ℕ} : Fintype (Port (EnrichedOuter.fan S) (Fin copies × Unit) j) :=
  Replay.batchFinite (EnrichedOuter.fan S) (Fin copies × Unit) j


open Inherited BorderVNP.Cube.Physical DiagonalTallyCellReports ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open GridPlacement CellSparse GridBoxes BottomReports
set_option maxHeartbeats 2000000
set_option maxRecDepth 7000


open NativeLedger NativeAssignments
variable (hist : (packHistory bottom M.epoch T).Index) {cn cd blocks cb ch ck symbols : ℕ}
    (B : CoreDirectory (network p fit position free count M bottom installed hist) cn cd blocks cb ch ck R)
    (label : Fin B.cells → Label (cn+1) cd)
    (route : B.Route symbols) (work : B.Bank)
    (bank : Ports (fun _ : FreeBlock R (tileCount axes gridDepth) => inputBlockWidth r (k+1) axes gridDepth))
    {l : ReportLayout} (rc : ReceivedRows (fun _ : Fin (R+1) => l) B.cells)
    (param : PairedParameters k s ≃ Fin l.parameters) (scalar : Gadget ≃ Fin l.gadgets)
    {nn : ℕ} (origin : Fin nn ≃ Fin ((EnrichedOuter.fan S)^T) × (Fin axes → Deck (gridDepth+2)))
    {ns ne np qe qa : ℕ} (sites : (W.routedFine position).Site ↪ Fin ns)
    (edges : (W.routedFine position).Edge ↪ Fin ne) (ports : (Fin r × Fin (publicWidth (tapeTemplate p fit pins))) ↪ Fin np)
    (channels : ((Fin axes → Deck (gridDepth+2)) × Direction axes) ↪ Fin qe) (groups : Fin (tileCount axes gridDepth) ↪ Fin qa)
    (boxSlot offset : Fin nn → ℕ) (prior : Fin nn → ℕ → Bool)
local notation3 (prettyPrint := false) "net" => network p fit position free count M bottom installed hist
local notation3 (prettyPrint := false) "code" => param.toEmbedding.trans Fin.valEmbedding
local notation3 (prettyPrint := false) "slab" => fun j : Fin ((EnrichedOuter.fan S)^T) × (Fin axes → Deck (gridDepth+2)) =>
  W.seedSlab position code sites edges ports j.2
local notation3 (prettyPrint := false) "copiesAt" => fun _ : Fin ((EnrichedOuter.fan S)^T) × (Fin axes → Deck (gridDepth+2)) => copies
local notation3 (prettyPrint := false) "hidden" => W.bottomChoicesEquiv position edges slab (fun _ => rfl)
local notation3 (prettyPrint := false) "home" => originalReportCell (cell:=B.cell) p fit position free count M bottom installed hist origin
local notation3 (prettyPrint := false) "coreBundle" => fun j => W.seedCoreBundle position code sites edges ports (origin j).2
  (boxSlot j) (offset j) copies
local notation3 (prettyPrint := false) "sources" => fun c : Fin B.cells => (BundleDirectory.sourceRows home c.val).map coreBundle
local notation3 (prettyPrint := false) "wire" => rawPath net B.cell B.edgeID B.programs B.owners route.val work
local notation3 (prettyPrint := false) "team" => B.owners route.val.1
local notation3 (prettyPrint := false) "teamNumber" => SewnTape.teamNumber (EnrichedOuter.fan S) T copies R count
local notation3 (prettyPrint := false) "entry" z => tags p fit W position free count M bottom installed y hy pos hg hist (hidden z)

variable (anchor : (Fin ((EnrichedOuter.fan S)^T) × (Fin axes → Deck (gridDepth+2))) ↪
      (network p fit position free count M bottom installed hist).Site)
    (wide : ∀ j,(B.programs (anchor j)).birth.work = copies * (W.seedSlab position
      (param.toEmbedding.trans Fin.valEmbedding) sites edges ports j.2).stride)
    (birthLocal : ∀ v,(B.programs v).birth.Local) (schema : ∀ v,(B.programs v).program.Schema)
    (relative : ∀ v,(B.programs v).program.RelativeBoxes)
    (tape : Fin (R+1) → ℕ → Bool) (start : Fin (R+1) → ℕ) (cursor : Fin (R+1) → ReportCursor)
local notation3 (prettyPrint := false) "z₀" => extractBottom net B.cell B.siteID (placedSize net B.programs) B.owners slab copiesAt
  (fun _ j => retainedLocation net B.programs anchor slab copiesAt wide j) route.val work
local notation3 (prettyPrint := false) "tagtable" => numberTables param scalar (entry z₀).tags
local notation3 (prettyPrint := false) "useWords" => (entry z₀).words.number teamNumber param scalar
local notation3 (prettyPrint := false) "visits" => (t : Fin (R+1)) × Fin (rc.cells t).length
local notation3 (prettyPrint := false) "src" => fun j : visits => rc.assignedAt net B.cell B.siteID B.edgeID B.portID B.programs
  B.owners B.slot bank B.owner sources route.val work j.1 j.2
local notation3 (prettyPrint := false) "rawBank" => rc.reportSourceBank src home
local notation3 (prettyPrint := false) "rows" => rc.reportedWithTape tape start

include birthLocal schema relative in
/-- Every read of the actual assigned report is identified at once: the
ordered named unary source, each independently checked site ID count, and
the report writer's relative bit addresses on the same decoded full path. -/
noncomputable def recoveredTermReaders {w₀ order₀ : ℕ}
    (model : ∀ z,Site.Programs.TagModels net B.edgeID B.portID B.programs (entry z).tags
      (scalar.toEmbedding.trans Fin.valEmbedding) (Site.Programs.carryPred anchor (birthPredicate slab copiesAt z)))
    (passed : ∀ j : visits,(src j).Passing w₀ order₀)
    (ret : ∀ j : visits,∃ t,(src j).Returns w₀ order₀ (rows (rc.order j)) t)
    (extent : ∀ j : visits,((rc.cells j.1).get j.2).privateWires+((rc.cells j.1).get j.2).supplied =
      (src j).privateWires+(src j).boundary.length)
    (stored : ∀ j : visits, ((rc.cells j.1).get j.2).bundles = (BundleDirectory.sourceRows home (rc.order j).val).map
      (W.retainedBundle (copies:=copies) position origin code sites edges ports channels groups boxSlot offset prior))
    (hosted : ∀ j : visits, pathCellOwner label team wire (rc.order j)=j.1)
    (readBank : Fin nn → ℕ → Bool)
    (sameReport : ∀ j : Fin nn, W.retainedBundle (copies:=copies) position origin code sites edges ports channels groups
      boxSlot offset readBank j = W.retainedBundle (copies:=copies) position origin code sites edges ports channels groups
      boxSlot offset rawBank j)
    (observed : SeedReportObserved p fit W position free count M bottom installed y hy pos hg hist (hidden z₀)
      B.slot wire bank origin param sites edges ports channels groups boxSlot offset readBank) (t : Fin (R+1)) :
    rc.pathReportReaders (N := net) (cell := B.cell) (B := Nat.clog 2 (r*(2*k+1)+1))
      B.slot tagtable bank useWords label team wire hosted tape start t := by
  have grouped := W.returned_seed_rows position origin code sites edges ports channels groups boxSlot offset rc tape start
    src (fun _ => rfl) passed ret home prior (fun _ => rfl) stored
  have aligned (c : Fin B.cells) := (grouped c).trans (List.map_congr_left fun j _ => (sameReport j).symm)
  have scalarInput := rc.scalarReaders net B.cell B.siteID B.edgeID B.portID B.programs anchor slab copiesAt wide
    B.owners B.slot bank (fun z => (entry z).tags) B.owner B.owner_site birthLocal schema relative sources route.val work
    param scalar model tape start cursor passed ret extent
  exact numberedReportReaders p fit W position free count M bottom installed y hy pos hg hist (hidden z₀)
    B.slot wire bank origin label team param scalar sites edges ports channels groups boxSlot offset readBank
    rc tape start cursor hosted aligned observed scalarInput t

end Diagonal.CellEntries.EnrichedTape

end BorderVNP
end Computability
end OAI
