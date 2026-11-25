import OAI.Computability.BorderVNP.DiagonalFrozenTaskColumns
import OAI.Computability.BorderVNP.DiagonalFrozenSignedDeployment
import OAI.Computability.BorderVNP.DiagonalFrozenBootMeter

/-! # Reference, accepting and rejected columns on the deployed signed site table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Branch Cover Packing Packing.DeckGrid CellEntries ExternalSew ExternalSew.RowTrace
open VPVNP BurstRAM VerifierNetwork ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open TeamContraction TeamContraction.ProcessorSlots RoutingISA RoutingISA.Evaluator RoutingISA.Pins RoutingISA.CompactMachine
open GeometryAdvice GeometryFrameEncoding PackedHistoryCircuit TeamScales ResiduePins ResidueIndex ResidueBox TeamSite
open RoutingISA.Transmission DiagonalResidueRAM ResidueEntryInput ResidueRates
open FieldProcessor (Scale freeWidth)
open scoped Classical BigOperators
set_option maxRecDepth 7000
set_option maxHeartbeats 1600000

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {paid : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {C : CommonField paid aux q k s ord} {chart : AdvisedBranch C}
    [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r rw pinWidth ec axes d : ℕ} {α ξ : ℝ} {K₀ : Type} [Field K₀]
    (cube : FixedCube K₀) (reader : ChosenReader chart (R+1) r rw rw rw pinWidth)

local notation3 (prettyPrint := false) "eval" => signedBody (cube.cubeID paid)
local notation3 (prettyPrint := false) "P" => (signedProgram (cube.cubeID paid)).program
local notation "lib" => siteLibrary SparseExterior.driver
local notation "marker" => fun _ : Fin 8 => some false
local notation3 (prettyPrint := false) "physical" => cube.signedSiteProgram paid
local notation3 (prettyPrint := false) "freeLen" => freeWidth (cube.signedSiteProgram paid) α 32 64 r rw (k+1)
local notation3 (prettyPrint := false) "ell" => link ξ (R+1) (k+1)

variable (geo : Scale (cube.signedSiteProgram paid) ((withStartup (signedBody (cube.cubeID paid))).slots+1)
    64 32 α ξ r (k+1) R rw ec)
local notation "indexWidth" => (pairedTableParameters (k+1) s+2)*pinWidth

variable {gridOrder : Fin (GridHosts.tileCount axes d) ≃ (Fin axes → Deck (d+2))}
    (W : WiredWitness (tapeTemplate (R:=R) (r:=r) (link:=TeamScales.link ξ (R+1) (k+1)) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1)
        (k:=k) (a:=setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+freeWidth (cube.signedSiteProgram paid) α 32 64 r rw (k+1)))
        (cube.signedSiteProgram paid) geo.fits ((pairedTableParameters (k+1) s+2)*pinWidth)) (Fin.last k) D axes d gridOrder
        (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (pos : (Fin axes → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {ns ne np : ℕ}
    (sites : (W.routedFine pos).Site ↪ Fin ns) (edges : (W.routedFine pos).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate (R:=R) (r:=r) (link:=TeamScales.link ξ (R+1) (k+1)) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1)
      (k:=k) (a:=setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+freeWidth (cube.signedSiteProgram paid) α 32 64 r rw (k+1))) (cube.signedSiteProgram paid) geo.fits
      ((pairedTableParameters (k+1) s+2)*pinWidth))) ↪ Fin np)
    (copies bundles headerFactor : ℕ)
    (L : Routing.WireLayout (R+1) r (TeamScales.link ξ (R+1) (k+1)))
    {reserve o field : ℕ} (sourceTable : Table (Fin reserve ⊕ Fin 0) o field)
    (task : SignedTaskArena.Layout)

local notation "tiles" => GridHosts.tileCount axes d
local notation "boxCap" => seedBoxCapacity (k+1) r axes d (Fintype.card (Direction axes))
local notation "bodyCap" => BottomGridBank.bodyBudget boxCap
local notation "H₀" => headerFactor*logWidth r (k+1)
local notation "dB" => seedDescriptionWidth (k+1) r axes d H₀ bodyCap
local notation3 (prettyPrint := false) "arena" => reader.startupArenaWith (n:=k+1) (reg:=64) physical freeLen ell L.header
local notation3 (prettyPrint := false) "dir" => freeDirectory R r (arena).literal ell tiles
  (GridHosts.inputBlockWidth r (k+1) axes d) (bundles*tiles) dB
local notation3 (prettyPrint := false) "reservedGap" => 7*(Directory.Layout.candidates dir)
local notation3 (prettyPrint := false) "base₀" => StartupArena.next arena+reservedGap
local notation3 (prettyPrint := false) "origin₀" => Allocation.dest base₀ reserve (Table.size sourceTable) o field
local notation3 (prettyPrint := false) "queryCount" => Fintype.card (Board.Physical (pairedTableParameters (k+1) s) pinWidth rw (paid.Entry ⊕ ι))
local notation3 (prettyPrint := false) "guessCount" => Fintype.card (Guess (Fin (pairedTableParameters (k+1) s)) reader.gridRank
  (Nat.clog 2 C.p+1) (Nat.clog 2 C.p))
local notation3 (prettyPrint := false) "routeFields" => routingExtension (signedBudgetWords rw (exterior ξ r (k+1)))
  dir origin₀ task.cube.cables task.cube.cells
local notation3 (prettyPrint := false) "selectedPlace" u => reader.frozenTaskPlacement task arena u routeFields
local notation3 (prettyPrint := false) "pinnedFields" u => CubeHeaderInstall.pinFields (selectedPlace u).extension
  (Allocation.stop base₀ reserve (Table.size sourceTable) o field rw) task.cube.header.d (task.cube.n+1)
  (task.cube.h*task.cube.b) task.cube.header.blocks reserve
  (BorderVNP.Cube.Physical.declarationCap task.cube.n task.cube.header.d task.cube.header.blocks task.cube.b task.cube.h task.cube.s)
local notation3 (prettyPrint := false) "offset₀" => StartupArena.literal arena/4
local notation3 (prettyPrint := false) "stripeLen" => GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve sourceTable.size o field*rw) r
local notation3 (prettyPrint := false) "fields₀" u => Allocation.fields (pinnedFields u) base₀ reserve sourceTable.size o field offset₀ stripeLen
local notation3 (prettyPrint := false) "packets₀" => fun u : Fin (R+1) => reader.packetAt (ReaderPlacement.inArena arena
  (selectedPlace u).valuation (selectedPlace u).entry (selectedPlace u).totals (fields₀ u))
local notation3 (prettyPrint := false) "blank" => TimedProcessor.scaleData P lib marker geo
  (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => false) (fun _ _ _ => false)
local notation3 (prettyPrint := false) "adOff" => adviceOffsetWith physical r 32 64 rw (k+1)
local notation3 (prettyPrint := false) "live" j => (boxPinCodec (pairedTableParameters (k+1) s) reader.rankFits reader.boxFits).encode j
local notation3 (prettyPrint := false) "mac" => TeamSiteEvents.macros (w:=rw) lib ((k+1)^25+1)

/-- Every column of the fixed deployed tape uses the reference reader and the
specified traffic budget, even when the exterior supplies a malformed header. -/
theorem ChosenReader.deployedFrozenColumns
    (mode : AllocatedPacketModes eval lib marker geo L.header reader.packetBitCount packets₀)
    (ok : AllocatedPacketReady eval lib marker geo L.header reader.packetBitCount packets₀)
    (bad : AllocatedPacketRejects eval lib marker geo L.header reader.packetBitCount packets₀) :
    let T := reader.deployedFrozenSites physical P blank geo.fits W pos sites edges ports copies bundles
      headerFactor L sourceTable task (exterior ξ r (k+1))
    let sewn := SewnTape.wiring (k:=k) (regs:=64) (w:=rw) (ec:=ec) (width:=rw+1) physical geo.fits
      (T.enrichedFree physical P (k+1) ec ell) indexWidth
    let args := fun u => (arena).unitAddresses adOff (packets₀ u)
    (∀ u, let ad := args u
      ad.Fitted sewn u (packets₀ u) (T.publicWords u) adOff ∧
      packetUnitBudget ad.advice.count rw (sewn.transferFrame u ad.header ad.dst)
        (sewn.pinLayout u ad.ibase ad.hbase ad.starbase) ≤ T.limit.val) ∧
    ∀ j : Index (Fin (Module.finrank (ZMod C.p) chart.E)) (Fin (pairedTableParameters (k+1) s)) (chart.pinRadius (R+1) r),
      signedContraction sewn.slot (live j) = (if (live j)=(live reader.star) then 1 else 0)+
        ∑ ext, ∏ u, positiveMaskedNativeValue sewn eval mac T.publicWords T.registers args (live j)
          T.limit.val T.burst.val ((k+1)^25) ext u ∧
      ∀ ext, ¬ PositiveExterior sewn args (live j) rw ext →
        (∏ u, positiveMaskedNativeValue sewn eval mac T.publicWords T.registers args (live j)
          T.limit.val T.burst.val ((k+1)^25) ext u)=0 := by
  exact reader.frozenTask_columns cube geo W pos sites edges ports copies bundles headerFactor
    (fun u => (selectedPlace u).valuation) (fun u => (selectedPlace u).entry) (fun u => (selectedPlace u).totals)
    (fun u => pinnedFields u) L sourceTable (signedBootStripe (freeStartWith physical r 32 64 rw (k+1)))
    (fun _ => []) reservedGap task origin₀ queryCount guessCount reader.gates mode ok bad

/-- The budget for all charts at the chosen length applies to the real
installed literal, including its complete gate stripe and the team-specific
reserved scalar and reader locations. -/
theorem ChosenReader.deployedFrozenMeter (meter : reader.FrozenBootMeter cube geo L) :
    let T := reader.deployedFrozenSites physical P blank geo.fits W pos sites edges ports copies bundles
      headerFactor L sourceTable task (exterior ξ r (k+1))
    let wire := wiringWith physical P T indexWidth ell (k+1) ec geo.fits
    ∀ u, let ad := (arena).unitAddresses adOff (packets₀ u)
      packetUnitBudget ad.advice.count rw (wire.transferFrame u ad.header ad.dst)
        (wire.pinLayout u ad.ibase ad.hbase ad.starbase) ≤ T.limit.val := by
  intro T wire u
  exact meter (fun v => (selectedPlace v).valuation) (fun v => (selectedPlace v).entry)
    (fun v => (selectedPlace v).totals) (fun v => fields₀ v) T u

section SelectedTask

variable [NeZero D] {schedule : Normalized.SiteSchedule paid} {extra E degree Q A B j : ℕ}
    {epoch : EpochScales schedule (cube.pred+1) extra} (sched : JointSchedule.{0} epoch (E+1) degree Q A B j)

/-- The same startup bound on the actual header overlay of the chosen frozen
task. This spells the installed extension in signed-profile coordinates so
the owner and reader checks use their own physical addresses. -/
theorem ChosenReader.selectedFrozenMeter (dirs : SignedTaskArena.GeometryDirectories)
    (meter : reader.FrozenBootMeter cube geo L) :
    let ar := sched.frozenSignedTask cube (k+1) k s headerFactor arena dir reserve sourceTable.size o field dirs
    let T := reader.deployedFrozenSites physical P blank geo.fits W pos sites edges ports copies bundles
      headerFactor L sourceTable ar (exterior ξ r (k+1))
    let wire := wiringWith physical P T indexWidth ell (k+1) ec geo.fits
    let raw := SignedTaskArena.rawAddress arena ar.cube.header.profile ar.cube.n ar.cube.header.d ar.cube.header.cap
    let ext := fun u : Fin (R+1) => signedProfileExtension ar (signedBudgetWords rw (exterior ξ r (k+1)))
      dir origin₀ ar.cube.cables ar.cube.cells raw u.val rw base₀ reserve sourceTable.size o field offset₀ stripeLen
    ∀ u, let ref := reader.nativePacket (ar.valuation rw) (ar.entry rw queryCount guessCount reader.gates)
          (arena).ibase (arena).hbase ar.tallyBits (ext u)
      let ad := (arena).unitAddresses adOff ref
      packetUnitBudget ad.advice.count rw (wire.transferFrame u ad.header ad.dst)
        (wire.pinLayout u ad.ibase ad.hbase ad.starbase) ≤ T.limit.val := by
  intro ar T wire raw ext u
  exact meter (fun _ => ar.valuation rw) (fun _ => ar.entry rw queryCount guessCount reader.gates)
    (fun _ => ar.tallyBits) ext T u

end SelectedTask

end Diagonal

end BorderVNP
end Computability
end OAI
