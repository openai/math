import OAI.Computability.BorderVNP.DiagonalSelectedIssuedExecution
import OAI.Computability.BorderVNP.DiagonalSelectedReportPass
import OAI.Computability.BorderVNP.DiagonalSelectedReturnedFinish
import OAI.Computability.BorderVNP.DiagonalOriginalPrefixRuns
import OAI.Computability.BorderVNP.DiagonalRoutedCoreReportReadback
import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomParameters

/-! # Native prefix runs of the candidate selected by the original issued cells -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.DeckGrid Packing.PhysicalEpochs Diagonal Diagonal.CellEntries
open Diagonal.ExternalSew TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter TeamScales BorderVNP.Cube.Physical.NativeAssignments BorderVNP.Cube
open Branch ResidueBox ResidueIndex ResiduePins
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option Elab.async false
set_option maxHeartbeats 2400000
attribute [local irreducible] Nat.clog
set_option maxRecDepth 7000
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K F : Type} [Field K] [Field F] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r pin link k d a regs rw ec width s copies T header work : ℕ}
    (plan : SeedPlan S (k+1) r d T copies header work) (cube : FixedCube F)
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
local notation3 (prettyPrint := false) "pins" => (pairedTableParameters (k+1) s+2)*pin
local notation3 (prettyPrint := false) "scalarIDs" => e.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "code" => (ParseTable.numberedLabelEquiv ord k s).toEmbedding.trans Fin.valEmbedding
local notation3 (prettyPrint := false) "num" => (Fintype.equivFin (scalarIDs)).toEmbedding.trans Fin.valEmbedding
local notation3 (prettyPrint := false) "axes" => Fintype.card (Cube D)
local notation3 (prettyPrint := false) "tiles" => GridHosts.tileCount axes d
local notation3 (prettyPrint := false) "G₀" => tapeTemplate p fit pins
variable {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin)) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin))) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin)) (Fintype.card (Cube D)) d order position copies).Tables K)
local notation3 (prettyPrint := false) "M" => plan.compiled.machine
local notation3 (prettyPrint := false) "mass" => initialMass (D:=D) (k+1) r d copies header
local notation3 (prettyPrint := false) "goodState" => Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape := boundary S (d+1)) (w := 60*logWidth r (k+1)) (boundaryBudget S mass)
variable (words : Boundary.Pins S (d+1) (boundary S (d+1)) (60*logWidth r (k+1)) 0 → Bool)
    (good : Boundary.Good (boundaryBudget S (initialMass (D:=D) (k+1) r d copies header)) 0 (Boundary.seedState S (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin)) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
local notation3 (prettyPrint := false) "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words) good : Admissible goodState 0)
local notation3 (prettyPrint := false) "G₁" => SewnTape.wiring p fit free pins
local notation3 (prettyPrint := false) "Hist" => (packHistory (Pack := Admissible goodState) (K := fan S) leaf (M).epoch T).Index
variable (hp : (fieldSewParams (SewnTape.wiring p fit free ((pairedTableParameters (k+1) s+2)*pin)) (Fintype.card (Cube D)) d).Valid)
    (α ξ : ℝ) (calibrated : plan.SignedLabelRows count link (cube.pred+1) α ξ)
    (lit : (UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a) = literal α (k+1))
    (hd : 0 < BorderVNP.Cube.alphabet α (k+1)) {cells : ℕ}
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells)
    (reportArena : RoutingISA.CubeArena.Layout) (dirs : RoutingISA.SignedTaskArena.GeometryDirectories)
    (bundles marked expBits reportWord headerSize body : ℕ)
local notation3 (prettyPrint := false) "params" => RoutingISA.SignedTaskArena.physicalParameters reportArena dirs
  (k+1) bundles marked (pairedTableParameters (k+1) s) expBits (Fintype.card (scalarIDs)) reportWord headerSize body
local notation3 (prettyPrint := false) "gap" => (params).privateGap

attribute [local instance] selectedBatchFinite

local notation3 (prettyPrint := false) "banks" => canonicalBank (G := G₁) hp.block (GridHosts.gridRoom G₁ Fintype.card_pos)
local notation3 (prettyPrint := false) "dir" => signedCoreDirectory plan p fit W position code sites edges ports table words
  good seeds free count Sum.inl num hp
local notation3 (prettyPrint := false) "put" => (Sum.inr : TableEntry cube.pred cube.b cube.h cube.copies cube.width → scalarIDs)



open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator CellMacro.Generator TeamContraction.JointHeader TeamContraction.ProcessorSlots
open BorderVNP.Epoch.Round

open BorderVNP.Cube.Physical BorderVNP.Cube.Physical.NativeLedger RoutingISA.CellDispatch
open RoutingISA.CompactMachine DiagonalTallyCellReports Packing.DeckGrid Packing.RoutingOutputs.NativeDemands

variable (arenaBase profileBits frame origin : ℕ)
local notation3 (prettyPrint := false) "Raw" => Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool
local notation3 (prettyPrint := false) "dim" => pairedTableParameters (k+1) s + Fintype.card (scalarIDs)
local notation3 (prettyPrint := false) "dirsOf" => fun h : Hist => dir h cube α ξ calibrated lit hd number gap
local notation3 (prettyPrint := false) "packets" => plan.signedPackets count G₀ order position W code sites edges ports table
  words good cube α ξ calibrated lit hd hp number gap
local notation3 (prettyPrint := false) "labels" => ParseTable.numberedLabelEquiv ord k s
local notation3 (prettyPrint := false) "scalars" => Fintype.equivFin (scalarIDs)
local notation3 (prettyPrint := false) "gid" => (scalars) ∘ put
local notation3 (prettyPrint := false) "seedCap" => seedBoxCapacity (k+1) r axes d (Fintype.card (Direction axes))
local notation3 (prettyPrint := false) "seedBlock" => GridHosts.inputBlockWidth r (k+1) axes d
local notation3 (prettyPrint := false) "desc" => seedDescriptionWidth (k+1) r axes d (header*logWidth r (k+1)) (BottomGridBank.bodyBudget seedCap)
local notation3 (prettyPrint := false) "deliveries" => freeDirectory R r ((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))
  link tiles seedBlock ((fan S)^T*tiles) desc
local notation3 (prettyPrint := false) "arena" =>
  (CubeArena.selectedSizes arenaBase (BorderVNP.Cube.alphabet α (k+1)) ((R+1)*exterior ξ r (k+1))
    cells ((boundary S (d+1) T).edges+4*((R+1)*CoverScale.sites (Cube D) (d+1))) (deliveries).candidates
    (R+1) r (k+1) profileBits).selected cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "theTask" => SignedTaskArena.Layout.mk arena (cube.cubeID e) params
local notation3 (prettyPrint := false) "control" =>
  RoutingOutputs.controlsBase origin (arena).cables cells (deliveries).entries ((R+1)*tiles)
local notation3 (prettyPrint := false) "networks" => EnrichedTape.network («pins» := pins) p fit position free count M leaf rfl
local notation3 (prettyPrint := false) "receipt" => plan.signedReceivedRows p fit W position code sites edges ports table
  words good seeds free count (Sum.inl : e.Entry → scalarIDs) num hp
local notation3 (prettyPrint := false) "rows" => fun (_ : Raw) (h : Hist) (v : ((dirsOf) h).Route cube.width) =>
  receipt h cube α ξ calibrated lit hd number params arenaBase profileBits (fun _ => frame) (fun _ => origin) (Subtype.val v)
/-- The team layout of the actual received report directory. -/
private abbrev issuedLayout {t c : ℕ} {L : Fin t → ReportLayout} (_ : ReceivedRows L c) := L
local notation3 (prettyPrint := false) "shape" => fun i h v => issuedLayout (rows i h v)
local notation3 (prettyPrint := false) "cellOwner" => fun h : Hist => ((dirsOf) h).owner
local notation3 (prettyPrint := false) "original" => fun h : Hist => plan.signedCellBundles p fit W position code sites edges ports table
  words good seeds free count (Sum.inl : e.Entry → scalarIDs) num hp h cube α ξ calibrated lit hd number params arenaBase profileBits
local notation3 (prettyPrint := false) "teamOf" => fun (h : Hist) (v : ((dirsOf) h).Route cube.width) (c : Fin ((dirsOf h).cells)) =>
  (dirsOf h).owners v.val.1 ((packets h).label c (chosen cube.b cube.width v.val.1))
local notation3 (prettyPrint := false) "owns" => fun (_ : Raw) h v u j => plan.signedReceivedRows_owner p fit W position
  code sites edges ports table words good seeds free count (Sum.inl : e.Entry → scalarIDs) num hp h cube α ξ calibrated
  lit hd number params arenaBase profileBits (fun _ => frame) (fun _ => origin) v.val u j
local notation3 (prettyPrint := false) "fields(" digits ")" =>
  PreparedFields Raw Hist (Fin ((R+1)*dim*digits) → Bool) (fun h => (dirsOf h).Route cube.width)
    (CoreDirectory.Proposals dirsOf shape rows)
local notation3 (prettyPrint := false) "pathOf(" h "," v ")" =>
  rawPath (networks h) (dirsOf h).cell (dirsOf h).edgeID (dirsOf h).programs (dirsOf h).owners (v).1.val (v).2
local notation3 (prettyPrint := false) "nativeMap(" i "," h "," v ")" =>
  (rows i h (v).1).physicalReportEquiv (networks h) (dirsOf h).cell (dirsOf h).siteID (dirsOf h).edgeID
    (dirsOf h).portID (dirsOf h).programs (dirsOf h).owners (dirsOf h).slot (banks i) (cellOwner h)
    (original h) (v).1.val (v).2 (rows i h (v).1).cells (fun _ => rfl)

/-- Every original issued prefix uses its own physical report assignment. The
canonical reports of the resulting candidate return at those same prefixes
at all subtotal choices and on every processor. -/
noncomputable def signedReceivedPrefixRunsOfIssuedSource
    {X₀ : Type} {w digits reserve groups capacity : ℕ}
    (teams : X₀ → Fin (R+1) → PositiveTeam (cube.cubeID e) SparseExterior.driver (k+1) w)
    (prep : JointBeforeCells teams ≃ fields(digits))
    (base : fields(digits) → Fin (R+1) → ℕ)
    (ownerTable : ∀ (f : fields(digits)) t, let start := prep.symm f
      OwnerTable (teams start.1 t).pub ((teams start.1 t).postMemory (start.2 t))
        ⟨t.val,base f t,(dirsOf f.2.1).cells⟩ (PositiveTeam.ownerWord (teamOf f.2.1 f.2.2.1)))
    (issued : ∀ f,CoreDirectory.Issued dirsOf banks cellOwner original shape rows teams prep f)
    (i : Raw) (q : Hist) (v : (dirsOf q).Route cube.width × (dirsOf q).Bank)
    (hdr : PositiveFields reserve cube.pred groups capacity (R+1) dim digits)
    (startup : Fin (R+1) → StartupArena)
    (source : ∀ (src : CoreDirectory.Proposals dirsOf shape rows i q v.1) (cc : Fin ((R+1)*dim*digits) → Bool) t,
      let start := prep.symm ⟨i,q,v.1,cc,src⟩
      OriginalPrefixRun theTask hdr gid ((dirsOf q).owners v.1.val.1) (pathOf(q,v)) frame control (params).siteWidth
        (params).bodyCap startup (rows i q v.1) t (teams start.1 t) (start.2 t) src cc) :
    let A := (CoreDirectory.preparedRoutedRows dirsOf banks cellOwner original shape rows teams prep teamOf owns
      base ownerTable issued i q v).candidate
    let same := CoreDirectory.preparedRoutedRows_source dirsOf banks cellOwner original shape rows teams prep teamOf owns
      base ownerTable issued i q v
    ∀ pubFrame : ∀ (ok : ∀ u c,c∈A.assigned u → c.Passing w (k+1)) cc t,
      frame=((A.team (canonicalReports A.assigned ok) cc t).pub 0).val,
    plan.signedReceivedPrefixRuns p fit W position params labels scalars sites edges ports table words good seeds
      free count Sum.inl hp q cube α ξ calibrated lit hd number arenaBase profileBits frame origin (banks i)
      v.1 v.2 A hdr same.1 same.2 startup gid pubFrame := by
  intro A same pubFrame
  let work := OriginalPrefixRun (gen:=SparseExterior.driver) (n:=k+1) (w:=w) theTask hdr gid
    ((dirsOf q).owners v.1.val.1) (pathOf(q,v)) frame control (params).siteWidth (params).bodyCap startup (rows i q v.1)
  have lifted := CoreDirectory.preparedRoutedRows_originalRuns dirsOf banks cellOwner original shape rows teams prep
    teamOf owns base ownerTable issued i q v same.1 same.2 work source
  exact prefixRunsOfOriginalReturns theTask hdr gid ((dirsOf q).owners v.1.val.1) (pathOf(q,v)) frame control
    (params).siteWidth (params).bodyCap startup (rows i q v.1) A
    (fun r => (nativeMap(i,q,v)).symm (reportsOfSameRows same.1 same.2 r)) lifted pubFrame

local notation3 (prettyPrint := false) "rowsAt(" fs ")" =>
  fun (_ : Raw) (h : Hist) (v : ((dirsOf) h).Route cube.width) => receipt h cube α ξ calibrated lit hd number
    params arenaBase profileBits fs (fun _ => origin) (Subtype.val v)
local notation3 (prettyPrint := false) "shapeAt(" fs ")" => fun i h v => issuedLayout (rowsAt(fs) i h v)
local notation3 (prettyPrint := false) "fieldsAt(" fs "," digits ")" =>
  PreparedFields Raw Hist (Fin ((R+1)*dim*digits) → Bool) (fun h => (dirsOf h).Route cube.width)
    (CoreDirectory.Proposals dirsOf (shapeAt(fs)) (rowsAt(fs)))
local notation3 (prettyPrint := false) "ownsAt(" fs ")" =>
  fun (_ : Raw) h v u j => plan.signedReceivedRows_owner p fit W position code sites edges ports table words
    good seeds free count (Sum.inl : e.Entry → scalarIDs) num hp h cube α ξ calibrated lit hd number params
    arenaBase profileBits fs (fun _ => origin) v.val u j
local notation3 (prettyPrint := false) "proposalAt(" fs "," i "," h "," v ")" =>
  CoreDirectory.Proposals dirsOf (shapeAt(fs)) (rowsAt(fs)) i h v
local notation3 (prettyPrint := false) "staticCells(" i "," h "," v ")" =>
  signedAssignedCells plan p fit W position code sites edges ports table words good seeds free count Sum.inl num hp
    h cube α ξ calibrated lit hd number params arenaBase profileBits (fun _ => frame) (fun _ => origin)
    (banks i) v (dirsOf h).owner

/-- The original prepared inverse already carries the ordered guarded cells.
Their complete layout and report directory agree with the common-frame source,
before any local finishing evidence is required. -/
theorem signedIssuedUsesRowsOfPhysicalFrames
    {X₀ : Type} {w digits : ℕ}
    (physicalFrames : Fin (R+1) → ℕ) (alignment : physicalFrames=fun _ => frame)
    (teams : X₀ → Fin (R+1) → PositiveTeam (cube.cubeID e) SparseExterior.driver (k+1) w)
    (prep : JointBeforeCells teams ≃ fieldsAt(physicalFrames,digits))
    (base : fieldsAt(physicalFrames,digits) → Fin (R+1) → ℕ)
    (ownerTable : ∀ (f : fieldsAt(physicalFrames,digits)) t, let start := prep.symm f
      OwnerTable (teams start.1 t).pub ((teams start.1 t).postMemory (start.2 t))
        ⟨t.val,base f t,(dirsOf f.2.1).cells⟩ (PositiveTeam.ownerWord (teamOf f.2.1 f.2.2.1)))
    (issued : ∀ f,CoreDirectory.Issued dirsOf banks cellOwner original (shapeAt(physicalFrames))
      (rowsAt(physicalFrames)) teams prep f)
    (i : Raw) (q : Hist) (v : (dirsOf q).Route cube.width × (dirsOf q).Bank) :
    let A := (CoreDirectory.preparedRoutedRows dirsOf banks cellOwner original (shapeAt(physicalFrames))
      (rowsAt(physicalFrames)) teams prep teamOf (ownsAt(physicalFrames)) base ownerTable issued i q v).candidate
    A.UsesRows (staticCells(i,q,v)) := by
  subst physicalFrames
  exact CoreDirectory.preparedRoutedRows_source dirsOf banks cellOwner original shape rows teams prep teamOf owns
    base ownerTable issued i q v

/-- The native team frames of the issued execution all read the common
control base. Rewriting this one family carries each physical proposal to
the common chart while the prefix itself still comes from the original
inverse preparation on the unreindexed reports. -/
noncomputable def signedReceivedPrefixRunsOfPhysicalFrames
    {X₀ : Type} {w digits reserve groups capacity : ℕ}
    (physicalFrames : Fin (R+1) → ℕ) (alignment : physicalFrames=fun _ => frame)
    (teams : X₀ → Fin (R+1) → PositiveTeam (cube.cubeID e) SparseExterior.driver (k+1) w)
    (prep : JointBeforeCells teams ≃ fieldsAt(physicalFrames,digits))
    (base : fieldsAt(physicalFrames,digits) → Fin (R+1) → ℕ)
    (ownerTable : ∀ (f : fieldsAt(physicalFrames,digits)) t, let start := prep.symm f
      OwnerTable (teams start.1 t).pub ((teams start.1 t).postMemory (start.2 t))
        ⟨t.val,base f t,(dirsOf f.2.1).cells⟩ (PositiveTeam.ownerWord (teamOf f.2.1 f.2.2.1)))
    (issued : ∀ f,CoreDirectory.Issued dirsOf banks cellOwner original (shapeAt(physicalFrames))
      (rowsAt(physicalFrames)) teams prep f)
    (i : Raw) (q : Hist) (v : (dirsOf q).Route cube.width × (dirsOf q).Bank)
    (hdr : PositiveFields reserve cube.pred groups capacity (R+1) dim digits)
    (startup : Fin (R+1) → StartupArena)
    (source : ∀ (src : proposalAt(physicalFrames,i,q,v.1)) (cc : Fin ((R+1)*dim*digits) → Bool) t,
      let start := prep.symm ⟨i,q,v.1,cc,src⟩
      let tape := cast (congrArg (fun fs => proposalAt(fs,i,q,v.1)) alignment) src
      OriginalPrefixRun theTask hdr gid ((dirsOf q).owners v.1.val.1) (pathOf(q,v)) frame control (params).siteWidth
        (params).bodyCap startup (rows i q v.1) t (teams start.1 t) (start.2 t) tape cc) :
    let A := (CoreDirectory.preparedRoutedRows dirsOf banks cellOwner original (shapeAt(physicalFrames))
      (rowsAt(physicalFrames)) teams prep teamOf (ownsAt(physicalFrames)) base ownerTable issued i q v).candidate
    ∀ (same : A.UsesRows (staticCells(i,q,v))) (pubFrame : ∀ (ok : ∀ u c,c∈A.assigned u → c.Passing w (k+1)) cc t,
      frame=((A.team (canonicalReports A.assigned ok) cc t).pub 0).val),
    plan.signedReceivedPrefixRuns p fit W position params labels scalars sites edges ports table words good seeds
      free count Sum.inl hp q cube α ξ calibrated lit hd number arenaBase profileBits frame origin (banks i)
      v.1 v.2 A hdr same.1 same.2 startup gid pubFrame := by
  subst physicalFrames
  intro A same pubFrame
  exact plan.signedReceivedPrefixRunsOfIssuedSource cube ord p fit W position sites edges ports table words
    good seeds free count hp α ξ calibrated lit hd number reportArena dirs bundles marked expBits reportWord
    headerSize body arenaBase profileBits frame origin teams prep base ownerTable issued i q v hdr startup source pubFrame

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
