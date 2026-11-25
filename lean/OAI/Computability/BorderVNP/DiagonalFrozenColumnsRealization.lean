import OAI.Computability.BorderVNP.DiagonalDeployedFrozenColumns
import OAI.Computability.BorderVNP.DiagonalFrozenSiteRealization

/-! # Realization on the signed task's installed site and its original mean packets -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Branch Crossing Cover Shortening Shortening.Adaptive Packing Packing.DeckGrid Diagonal Diagonal.CellEntries
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace GridHosts TeamContraction ProcessorSlots TeamScales EnrichedOuter
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar BorderVNP.Epoch BorderVNP.Epoch.Round
open RoutingISA RoutingISA.Evaluator CompactMachine CellMacro.Generator ResiduePins ResidueIndex ResidueBox
open RoutingISA.Pins RoutingISA.Transmission GeometryAdvice GeometryFrameEncoding PackedHistoryCircuit TeamSite
open DiagonalResidueRAM ResidueEntryInput ResidueRates VPVNP.BurstRAM
open FieldProcessor (Scale freeWidth)
open scoped Classical BigOperators
attribute [local instance] portFintype
set_option maxRecDepth 7500
set_option maxHeartbeats 3200000
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K K₀ : Type} [Field K] [Field K₀] {paid : PaidIdentity K D m}
    {schedule : SiteSchedule paid} (cube : FixedCube K₀) (φ : K₀ →+* K)
    {extra E deg Q₀ A B j cut : ℕ} (scales : EpochScales schedule (cube.pred+1) extra)
    (b : JointSchedule.{0} scales (E+1) deg Q₀ A B j)
    {R r k ec s copies T d header work pinWidth char : ℕ}
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) {C : CommonField paid (φ ∘ cube.table) char k s ord}
    (chart : AdvisedBranch C) [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    (reader : ChosenReader chart (R+1) r (b.physical.word (k+1)) (b.physical.word (k+1)) (b.physical.word (k+1)) pinWidth)
    (plan : SeedPlan schedule (k+1) r d T copies header work)

local notation "wordSize" => b.physical.word (k+1)
local notation "alpha₀" => scales.α
local notation "rate₀" => ((scales.τ:ℝ)/5)
local notation "axes₀" => Fintype.card (Cube D)
local notation "bundles" => (fan schedule)^T
local notation "headerFactor" => header
local notation3 (prettyPrint := false) "eval" => signedBody (cube.cubeID paid)
local notation3 (prettyPrint := false) "P" => (signedProgram (cube.cubeID paid)).program
local notation "lib" => siteLibrary SparseExterior.driver
local notation "marker" => fun _ : Fin 8 => some false
local notation3 (prettyPrint := false) "physical" => cube.signedSiteProgram paid
local notation3 (prettyPrint := false) "freeLen" => freeWidth (cube.signedSiteProgram paid) alpha₀ 32 64 r wordSize (k+1)
local notation3 (prettyPrint := false) "ell" => link rate₀ (R+1) (k+1)

variable (geo : Scale (cube.signedSiteProgram paid) ((withStartup (signedBody (cube.cubeID paid))).slots+1)
    64 32 scales.α ((scales.τ:ℝ)/5) r (k+1) R (b.physical.word (k+1)) ec)
local notation "indexWidth" => (pairedTableParameters (k+1) s+2)*pinWidth

variable {gridOrder : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate (R:=R) (r:=r) (link:=TeamScales.link ((scales.τ:ℝ)/5) (R+1) (k+1)) (regs:=64) (w:=(b.physical.word (k+1))) (e:=ec) (width:=(b.physical.word (k+1))+1)
        (k:=k) (a:=setupWidth ((b.physical.word (k+1))+1) (k+1)+(prefixCapacity r 32 64 (b.physical.word (k+1)) (k+1)+1+freeWidth (cube.signedSiteProgram paid) scales.α 32 64 r (b.physical.word (k+1)) (k+1)))
        (cube.signedSiteProgram paid) geo.fits ((pairedTableParameters (k+1) s+2)*pinWidth)) (Fin.last k) D (Fintype.card (Cube D)) d gridOrder
        (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (pos : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {ns ne np : ℕ}
    (sites : (W.routedFine pos).Site ↪ Fin ns) (edges : (W.routedFine pos).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate (R:=R) (r:=r) (link:=TeamScales.link ((scales.τ:ℝ)/5) (R+1) (k+1)) (regs:=64) (w:=(b.physical.word (k+1))) (e:=ec) (width:=(b.physical.word (k+1))+1)
      (k:=k) (a:=setupWidth ((b.physical.word (k+1))+1) (k+1)+(prefixCapacity r 32 64 (b.physical.word (k+1)) (k+1)+1+freeWidth (cube.signedSiteProgram paid) scales.α 32 64 r (b.physical.word (k+1)) (k+1))) (cube.signedSiteProgram paid) geo.fits
      ((pairedTableParameters (k+1) s+2)*pinWidth))) ↪ Fin np)
    (L : Routing.WireLayout (R+1) r (TeamScales.link ((scales.τ:ℝ)/5) (R+1) (k+1)))
    {reserve o field : ℕ} (sourceTable : Table (Fin reserve ⊕ Fin 0) o field)
    (task : SignedTaskArena.Layout)
    (seedTable : (seedBundle (tapeTemplate (R:=R) (r:=r) (link:=TeamScales.link ((scales.τ:ℝ)/5) (R+1) (k+1)) (regs:=64) (w:=(b.physical.word (k+1))) (e:=ec) (width:=(b.physical.word (k+1))+1)
      (k:=k) (a:=setupWidth ((b.physical.word (k+1))+1) (k+1)+(prefixCapacity r 32 64 (b.physical.word (k+1)) (k+1)+1+freeWidth (cube.signedSiteProgram paid) scales.α 32 64 r (b.physical.word (k+1)) (k+1)))
      (cube.signedSiteProgram paid) geo.fits ((pairedTableParameters (k+1) s+2)*pinWidth))
      (Fintype.card (Cube D)) d gridOrder pos copies).Tables K) {σ : Type} [Fintype σ] (input : σ → Bool)
    (count : (fan schedule)^T*copies=R+1)

local notation "tiles" => GridHosts.tileCount axes₀ d
local notation "boxCap" => seedBoxCapacity (k+1) r axes₀ d (Fintype.card (Direction axes₀))
local notation "bodyCap" => BottomGridBank.bodyBudget boxCap
local notation "H₀" => headerFactor*logWidth r (k+1)
local notation "dB" => seedDescriptionWidth (k+1) r axes₀ d H₀ bodyCap
local notation3 (prettyPrint := false) "arena" => reader.startupArenaWith (n:=k+1) (reg:=64) physical freeLen ell L.header
local notation3 (prettyPrint := false) "dir" => freeDirectory R r (arena).literal ell tiles
  (GridHosts.inputBlockWidth r (k+1) axes₀ d) (bundles*tiles) dB
local notation3 (prettyPrint := false) "reservedGap" => 7*(Directory.Layout.candidates dir)
local notation3 (prettyPrint := false) "base₀" => StartupArena.next arena+reservedGap
local notation3 (prettyPrint := false) "origin₀" => Allocation.dest base₀ reserve (Table.size sourceTable) o field
local notation3 (prettyPrint := false) "queryCount" => Fintype.card (Board.Physical (pairedTableParameters (k+1) s) pinWidth wordSize (paid.Entry ⊕ (TableEntry cube.pred cube.b cube.h cube.copies cube.width)))
local notation3 (prettyPrint := false) "guessCount" => Fintype.card (Guess (Fin (pairedTableParameters (k+1) s)) reader.gridRank
  (Nat.clog 2 C.p+1) (Nat.clog 2 C.p))
local notation3 (prettyPrint := false) "routeFields" => routingExtension (signedBudgetWords wordSize (exterior rate₀ r (k+1)))
  dir origin₀ task.cube.cables task.cube.cells
local notation3 (prettyPrint := false) "selectedPlace" u => reader.frozenTaskPlacement task arena u routeFields
local notation3 (prettyPrint := false) "pinnedFields" u => CubeHeaderInstall.pinFields (selectedPlace u).extension
  (Allocation.stop base₀ reserve (Table.size sourceTable) o field wordSize) task.cube.header.d (task.cube.n+1)
  (task.cube.h*task.cube.b) task.cube.header.blocks reserve
  (BorderVNP.Cube.Physical.declarationCap task.cube.n task.cube.header.d task.cube.header.blocks task.cube.b task.cube.h task.cube.s)
local notation3 (prettyPrint := false) "offset₀" => StartupArena.literal arena/4
local notation3 (prettyPrint := false) "stripeLen" => GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve sourceTable.size o field*wordSize) r
local notation3 (prettyPrint := false) "fields₀" u => Allocation.fields (pinnedFields u) base₀ reserve sourceTable.size o field offset₀ stripeLen
local notation3 (prettyPrint := false) "packets₀" => fun u : Fin (R+1) => reader.packetAt (ReaderPlacement.inArena arena
  (selectedPlace u).valuation (selectedPlace u).entry (selectedPlace u).totals (fields₀ u))
local notation3 (prettyPrint := false) "blank" => TimedProcessor.scaleData P lib marker geo
  (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => false) (fun _ _ _ => false)
local notation3 (prettyPrint := false) "adOff" => adviceOffsetWith physical r 32 64 wordSize (k+1)
local notation3 (prettyPrint := false) "live" j => (boxPinCodec (pairedTableParameters (k+1) s) reader.rankFits reader.boxFits).encode j
local notation3 (prettyPrint := false) "mac" => TeamSiteEvents.macros (w:=wordSize) lib ((k+1)^25+1)


local notation3 (prettyPrint := false) "deployed" => reader.deployedFrozenSites physical P blank geo.fits W pos sites edges ports copies bundles
  headerFactor L sourceTable task (exterior rate₀ r (k+1))
local notation3 (prettyPrint := false) "G₀" => tapeTemplate (r:=r) (R:=R) (link:=ell) (regs:=64) (w:=wordSize)
  (e:=ec) (width:=wordSize+1) (k:=k) (a:=setupWidth (wordSize+1) (k+1)+(prefixCapacity r 32 64 wordSize (k+1)+1+freeLen))
  physical geo.fits indexWidth
local notation3 (prettyPrint := false) "tag" => ParseTable.signedLiteralCode ord
local notation3 (prettyPrint := false) "words" => (plan.execute G₀ gridOrder pos σ).choose.eval input
local notation3 (prettyPrint := false) "leaf" => plan.frozenLeaf G₀ gridOrder pos W tag sites edges ports seedTable input
local notation3 (prettyPrint := false) "addresses" => fun u => (arena).unitAddresses adOff (packets₀ u)

/-- Supply actual live runs on the fixed original verifier. The reference contribution,
failed-exterior cancellation, all bounds, the ordered routed packet family, and its
block count are derived from the same deployed site and signed seed. -/
noncomputable def deployedRealizationOfRuns
    (length : LengthBudget b cut (k+1)) (room : ReaderTallyInputsAt cube b (k+1))
    (batch : r = stretch b.ρ (k+1)) (candidate : s = stretch b.σ (k+1)) (groups : R = b.physical.teamsPred (k+1))
    (depthEq : d+1 = CoverScale.initialDepth (Cube D) r (k+1)) (time : T = epochs scales.τ (k+1))
    (small : 1+initialMass (D:=D) (k+1) r d copies header ≤ TeamScales.width (k+1) (1/2:ℝ))
    (calibrated : plan.SignedLabelRows count ell (cube.pred+1) alpha₀ rate₀)
    (lit : (G₀).program.length+(TeamContraction.cutWidth (k+1)+
      (setupWidth (wordSize+1) (k+1)+(prefixCapacity r 32 64 wordSize (k+1)+1+freeLen))) = literal alpha₀ (k+1))
    (hd : 0 < BorderVNP.Cube.alphabet alpha₀ (k+1)) (hp : (fieldSewParams G₀ axes₀ d).Valid)
    {cells : ℕ} (number : (Cube D → Deck (depth schedule (d+1) T+1)) ≃ Fin cells)
    (mode : AllocatedPacketModes eval lib marker geo L.header reader.packetBitCount packets₀)
    (ok : AllocatedPacketReady eval lib marker geo L.header reader.packetBitCount packets₀)
    (bad : AllocatedPacketRejects eval lib marker geo L.header reader.packetBitCount packets₀) :=
  let columns := reader.deployedFrozenColumns cube geo W pos sites edges ports copies bundles headerFactor L sourceTable task mode ok bad
  plan.realizationOfFrozenPacketRuns cube φ scales b ord chart reader physical P geo.fits deployed W pos tag sites edges ports
    seedTable input count length room batch candidate groups depthEq time small calibrated lit hd hp number task.p.privateGap
    addresses mac (fun j => (columns.2 j).1) (fun j ext => (columns.2 j).2 ext)

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
