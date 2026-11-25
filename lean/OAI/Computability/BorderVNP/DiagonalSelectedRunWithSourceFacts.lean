import OAI.Computability.BorderVNP.DiagonalSelectedPhysicalRunRequest

/-! # The raw run and source identities on the same prepared route -/

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
variable {X₀ : Type} {w digits reserve groups capacity : ℕ}
    (physicalFrames : Fin (R+1) → ℕ) (alignment : physicalFrames=fun _ => frame)
    (teams : X₀ → Fin (R+1) → PositiveTeam (cube.cubeID e) SparseExterior.driver (k+1) w)

variable {plan cube ord p fit W position sites edges ports table words good seeds free count hp α ξ calibrated
  lit hd number reportArena dirs bundles marked expBits reportWord headerSize body arenaBase profileBits frame origin
  physicalFrames alignment teams}

local notation3 (prettyPrint := false) "runRequest" =>
  @PhysicalRunRequest D m _ K F _ _ e S R r pin link k d a regs rw ec width s copies T header work
  plan cube ord p fit order W position ns ne np sites edges ports table words good seeds free count hp
  α ξ calibrated lit hd cells number reportArena dirs bundles marked expBits reportWord headerSize body
  arenaBase profileBits frame origin X₀ w digits reserve groups capacity physicalFrames alignment teams
local notation3 (prettyPrint := false) "knownRows" =>
  @IssuedRowsFrameFormula D m _ K F _ _ e S R r pin link k d a regs rw ec width s copies T header work
  plan cube ord p fit order W position ns ne np sites edges ports table words good seeds free count hp
  α ξ calibrated lit hd cells number reportArena dirs bundles marked expBits reportWord headerSize body
  arenaBase profileBits frame origin X₀ w digits physicalFrames teams
local notation3 (prettyPrint := false) "nativeRequest" =>
  @physicalRunRequest D m _ K F _ _ e S R r pin link k d a regs rw ec width s copies T header work
  plan cube ord p fit order W position ns ne np sites edges ports table words good seeds free count hp
  α ξ calibrated lit hd cells number reportArena dirs bundles marked expBits reportWord headerSize body
  arenaBase profileBits frame origin X₀ w digits reserve groups capacity physicalFrames alignment teams
local notation3 (prettyPrint := false) "nativeFacts" =>
  @issuedRowsFrameProof D m _ K F _ _ e S R r pin link k d a regs rw ec width s copies T header work
  plan cube ord p fit order W position ns ne np sites edges ports table words good seeds free count hp
  α ξ calibrated lit hd cells number reportArena dirs bundles marked expBits reportWord headerSize body
  arenaBase profileBits frame origin X₀ w digits physicalFrames alignment teams

private noncomputable def applyKnownSource (runner : runRequest) (facts : knownRows)
    (stable : ∀ x u, ((teams x u).pub 0).val = frame) :=
  fun prep base ownerTable issued i q v hdr startup source =>
    let known := facts prep base ownerTable issued i q v stable
    runner prep base ownerTable issued i q v hdr startup source known.1 known.2

/-- The remaining source on a prepared route has one width and one owner
table. Its visible words and the canonical report refer to the same team. -/
noncomputable def SourceBackedRuns (stable : ∀ x u, ((teams x u).pub 0).val = frame) : Type _ :=
  type_of% (applyKnownSource nativeRequest nativeFacts stable)

/-- Attach already proved source-row and public-frame facts to the raw source.
The owner table and issued assignment are supplied only once. -/
noncomputable def PhysicalRunRequest.withSourceFacts (runner : runRequest) (facts : knownRows)
    (stable : ∀ x u, ((teams x u).pub 0).val = frame) :
    @SourceBackedRuns D m _ K F _ _ e S R r pin link k d a regs rw ec width s copies T header work
  plan cube ord p fit order W position ns ne np sites edges ports table words good seeds free count hp
  α ξ calibrated lit hd cells number reportArena dirs bundles marked expBits reportWord headerSize body
  arenaBase profileBits frame origin X₀ w digits reserve groups capacity physicalFrames alignment teams stable :=
  applyKnownSource runner facts stable

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
