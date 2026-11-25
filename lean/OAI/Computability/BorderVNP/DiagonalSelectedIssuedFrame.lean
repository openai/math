import OAI.Computability.BorderVNP.DiagonalSelectedOriginalPrefixRuns

/-! # The public frame of every issued source prefix -/

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
local notation3 (prettyPrint := false) "receipt" => plan.signedReceivedRows p fit W position code sites edges ports table
  words good seeds free count (Sum.inl : e.Entry → scalarIDs) num hp
/-- The team layout of the actual received report directory. -/
private abbrev frameLayout {t c : ℕ} {L : Fin t → ReportLayout} (_ : ReceivedRows L c) := L
local notation3 (prettyPrint := false) "cellOwner" => fun h : Hist => ((dirsOf) h).owner
local notation3 (prettyPrint := false) "original" => fun h : Hist => plan.signedCellBundles p fit W position code sites edges ports table
  words good seeds free count (Sum.inl : e.Entry → scalarIDs) num hp h cube α ξ calibrated lit hd number params arenaBase profileBits
local notation3 (prettyPrint := false) "teamOf" => fun (h : Hist) (v : ((dirsOf) h).Route cube.width) (c : Fin ((dirsOf h).cells)) =>
  (dirsOf h).owners v.val.1 ((packets h).label c (chosen cube.b cube.width v.val.1))
local notation3 (prettyPrint := false) "rowsAt(" fs ")" =>
  fun (_ : Raw) (h : Hist) (v : ((dirsOf) h).Route cube.width) => receipt h cube α ξ calibrated lit hd number
    params arenaBase profileBits fs (fun _ => origin) (Subtype.val v)
local notation3 (prettyPrint := false) "shapeAt(" fs ")" => fun i h v => frameLayout (rowsAt(fs) i h v)
local notation3 (prettyPrint := false) "fieldsAt(" fs "," digits ")" =>
  PreparedFields Raw Hist (Fin ((R+1)*dim*digits) → Bool) (fun h => (dirsOf h).Route cube.width)
    (CoreDirectory.Proposals dirsOf (shapeAt(fs)) (rowsAt(fs)))
local notation3 (prettyPrint := false) "ownsAt(" fs ")" =>
  fun (_ : Raw) h v u j => plan.signedReceivedRows_owner p fit W position code sites edges ports table words
    good seeds free count (Sum.inl : e.Entry → scalarIDs) num hp h cube α ξ calibrated lit hd number params
    arenaBase profileBits fs (fun _ => origin) v.val u j

local notation3 (prettyPrint := false) "staticCells(" i "," h "," v ")" =>
  signedAssignedCells plan p fit W position code sites edges ports table words good seeds free count Sum.inl num hp
    h cube α ξ calibrated lit hd number params arenaBase profileBits (fun _ => frame) (fun _ => origin)
    (banks i) v (dirsOf h).owner

/-- The issued candidate reads its family's common public frame on every
returned report and subtotal at the original prepared exterior. -/
theorem signedIssuedFrameOfPhysicalFrames
    {X₀ : Type} {w digits : ℕ}
    (physicalFrames : Fin (R+1) → ℕ)
    (teams : X₀ → Fin (R+1) → PositiveTeam (cube.cubeID e) SparseExterior.driver (k+1) w)
    (prep : JointBeforeCells teams ≃ fieldsAt(physicalFrames,digits))
    (base : fieldsAt(physicalFrames,digits) → Fin (R+1) → ℕ)
    (ownerTable : ∀ (f : fieldsAt(physicalFrames,digits)) t, let start := prep.symm f
      OwnerTable (teams start.1 t).pub ((teams start.1 t).postMemory (start.2 t))
        ⟨t.val,base f t,(dirsOf f.2.1).cells⟩ (PositiveTeam.ownerWord (teamOf f.2.1 f.2.2.1)))
    (issued : ∀ f,CoreDirectory.Issued dirsOf banks cellOwner original (shapeAt(physicalFrames))
      (rowsAt(physicalFrames)) teams prep f)
    (i : Raw) (q : Hist) (v : (dirsOf q).Route cube.width × (dirsOf q).Bank)
    (stable : ∀ x u,((teams x u).pub 0).val=frame) :
    let A := (CoreDirectory.preparedRoutedRows dirsOf banks cellOwner original (shapeAt(physicalFrames))
      (rowsAt(physicalFrames)) teams prep teamOf (ownsAt(physicalFrames)) base ownerTable issued i q v).candidate
    ∀ (rr : NativeReports A.assigned) (cc : Fin ((R+1)*dim*digits) → Bool) (u : Fin (R+1)),
      frame=((A.team rr cc u).pub 0).val :=
  CoreDirectory.preparedRoutedRows_frame dirsOf banks cellOwner original (shapeAt(physicalFrames))
    (rowsAt(physicalFrames)) teams prep teamOf (ownsAt(physicalFrames)) base ownerTable issued i q v frame stable

/-- Canonical passing reports carry the same original frame at every subtotal. -/
theorem signedIssuedCanonicalFrameOfPhysicalFrames
    {X₀ : Type} {w digits : ℕ}
    (physicalFrames : Fin (R+1) → ℕ)
    (teams : X₀ → Fin (R+1) → PositiveTeam (cube.cubeID e) SparseExterior.driver (k+1) w)
    (prep : JointBeforeCells teams ≃ fieldsAt(physicalFrames,digits))
    (base : fieldsAt(physicalFrames,digits) → Fin (R+1) → ℕ)
    (ownerTable : ∀ (f : fieldsAt(physicalFrames,digits)) t, let start := prep.symm f
      OwnerTable (teams start.1 t).pub ((teams start.1 t).postMemory (start.2 t))
        ⟨t.val,base f t,(dirsOf f.2.1).cells⟩ (PositiveTeam.ownerWord (teamOf f.2.1 f.2.2.1)))
    (issued : ∀ f,CoreDirectory.Issued dirsOf banks cellOwner original (shapeAt(physicalFrames))
      (rowsAt(physicalFrames)) teams prep f)
    (i : Raw) (q : Hist) (v : (dirsOf q).Route cube.width × (dirsOf q).Bank)
    (stable : ∀ x u,((teams x u).pub 0).val=frame) :
    let A := (CoreDirectory.preparedRoutedRows dirsOf banks cellOwner original (shapeAt(physicalFrames))
      (rowsAt(physicalFrames)) teams prep teamOf (ownsAt(physicalFrames)) base ownerTable issued i q v).candidate
    ∀ (ok : ∀ u c,c∈A.assigned u → c.Passing w (k+1)) cc t,
      frame=((A.team (canonicalReports A.assigned ok) cc t).pub 0).val := by
  intro A ok cc t
  exact CoreDirectory.preparedRoutedRows_frame dirsOf banks cellOwner original (shapeAt(physicalFrames))
    (rowsAt(physicalFrames)) teams prep teamOf (ownsAt(physicalFrames)) base ownerTable issued i q v
    frame stable (canonicalReports A.assigned ok) cc t

/-- The same issued candidate has the selected ordered cells and the original
public frame on every canonical passing report. -/
theorem signedIssuedRowsAndFrameOfPhysicalFrames
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
    (i : Raw) (q : Hist) (v : (dirsOf q).Route cube.width × (dirsOf q).Bank)
    (stable : ∀ x u,((teams x u).pub 0).val=frame) :
    let A := (CoreDirectory.preparedRoutedRows dirsOf banks cellOwner original (shapeAt(physicalFrames))
      (rowsAt(physicalFrames)) teams prep teamOf (ownsAt(physicalFrames)) base ownerTable issued i q v).candidate
    A.UsesRows (staticCells(i,q,v)) ∧ ∀ (ok : ∀ u c,c∈A.assigned u → c.Passing w (k+1)) cc t,
      frame=((A.team (canonicalReports A.assigned ok) cc t).pub 0).val :=
  ⟨plan.signedIssuedUsesRowsOfPhysicalFrames cube ord p fit W position sites edges ports table words good
    seeds free count hp α ξ calibrated lit hd number reportArena dirs bundles marked expBits reportWord
    headerSize body arenaBase profileBits frame origin physicalFrames alignment teams prep base ownerTable issued i q v,
   plan.signedIssuedCanonicalFrameOfPhysicalFrames cube ord p fit W position sites edges ports table words good
    seeds free count hp α ξ calibrated lit hd number reportArena dirs bundles marked expBits reportWord
    headerSize body arenaBase profileBits frame origin physicalFrames teams prep base ownerTable issued i q v stable⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
