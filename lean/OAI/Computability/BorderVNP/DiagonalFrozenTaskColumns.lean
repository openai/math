import OAI.Computability.BorderVNP.DiagonalSignedDeploymentBase
import OAI.Computability.BorderVNP.DiagonalTimedSiteColumns
import OAI.Computability.BorderVNP.DiagonalFrozenSignedLiteral

/-! # The signed mode sum on the calibrated physical task and frozen verifier -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Branch Cover Packing Packing.DeckGrid CellEntries ExternalSew ExternalSew.RowTrace
open VPVNP BurstRAM VerifierNetwork ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open TeamContraction TeamContraction.ProcessorSlots RoutingISA RoutingISA.Evaluator RoutingISA.Pins RoutingISA.CompactMachine
open GeometryAdvice GeometryFrameEncoding PackedHistoryCircuit TeamScales ResiduePins ResidueIndex ResidueBox TeamSite
open FieldProcessor (Scale freeWidth)
open scoped Classical BigOperators
set_option maxRecDepth 7000
set_option maxHeartbeats 2400000

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {paid : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {C : CommonField paid aux q k s ord} {chart : AdvisedBranch C}
    [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r mult tally rw pinWidth ec axes d : ℕ} {α ξ : ℝ} {K₀ : Type} [Field K₀]
    (cube : FixedCube K₀) (reader : ChosenReader chart (R+1) r mult tally rw pinWidth)

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
    (valuation entry totals : Fin (R+1) → ℕ) (old : Fin (R+1) → Fin 81 → Word rw)
    (L : Routing.WireLayout (R+1) r (TeamScales.link ξ (R+1) (k+1)))
    {reserve o field : ℕ} (sourceTable : Table (Fin reserve ⊕ Fin 0) o field)
    (boot : Stripe) (bootBits : Fin (R+1) → List Bool) (gap : ℕ)

local notation "tiles" => GridHosts.tileCount axes d
local notation "boxCap" => seedBoxCapacity (k+1) r axes d (Fintype.card (Direction axes))
local notation "bodyCap" => BottomGridBank.bodyBudget boxCap
local notation "H₀" => headerFactor*logWidth r (k+1)
local notation "dB" => seedDescriptionWidth (k+1) r axes d H₀ bodyCap
local notation3 (prettyPrint := false) "arena" => reader.startupArenaWith (n:=k+1) (reg:=64) physical freeLen ell L.header
local notation3 (prettyPrint := false) "fresh" => StartupArena.next arena+gap
local notation3 (prettyPrint := false) "off" => StartupArena.literal arena/4
local notation3 (prettyPrint := false) "stripeW" => GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve sourceTable.size o field*rw) r
local notation3 (prettyPrint := false) "stripe" => Allocation.stripe fresh reserve sourceTable.size o field off stripeW
local notation3 (prettyPrint := false) "deviceExt" u => Allocation.fields (old u) fresh reserve sourceTable.size o field off stripeW
local notation3 (prettyPrint := false) "place" => fun u : Fin (R+1) =>
  ReaderPlacement.inArena arena (valuation u) (entry u) (totals u) (deviceExt u)
local notation3 (prettyPrint := false) "geometryBits" => fun _ : Fin (R+1) =>
  GeometryAdvice.serialized (GeometryAdvice.packet (w:=rw) fresh (Allocation.packed fresh reserve sourceTable.size o field rw) sourceTable
    (fun i => StartupArena.broadcastBase arena+1+Fin.val i))
local notation3 (prettyPrint := false) "dir" => freeDirectory R r (arena).literal ell tiles
  (GridHosts.inputBlockWidth r (k+1) axes d) (bundles*tiles) dB
local notation3 (prettyPrint := false) "strings" => W.seedLiteralMatrix pos (ParseTable.signedLiteralCode ord) sites edges ports
  copies bundles H₀
variable (task : SignedTaskArena.Layout) (origin inputs guesses gates : ℕ)
local notation3 (prettyPrint := false) "initial" => cube.signedTaskData paid geo arena task origin inputs guesses gates
local notation3 (prettyPrint := false) "adOff" => adviceOffsetWith physical r 32 64 rw (k+1)
local notation3 (prettyPrint := false) "extension" => fun u : Fin (R+1) => deviceExt u
local notation3 (prettyPrint := false) "packets" => fun u : Fin (R+1) => reader.packetAt (place u)
local notation3 (prettyPrint := false) "live" j => (boxPinCodec (pairedTableParameters (k+1) s) reader.rankFits reader.boxFits).encode j
local notation3 (prettyPrint := false) "mac" => TeamSiteEvents.macros (w:=rw) lib ((k+1)^25+1)

/-- All live columns on the actual calibrated signed-task site. The original
private verifier W and cell-source table are fixed for the full sum. The
frame time, signed branches and failed exterior checks therefore use exactly
the same cutoff and original wires as the eventual wired executions. -/
theorem ChosenReader.frozenTask_columns
    (mode : AllocatedPacketModes eval lib marker geo L.header reader.packetBitCount packets)
    (ok : AllocatedPacketReady eval lib marker geo L.header reader.packetBitCount packets)
    (bad : AllocatedPacketRejects eval lib marker geo L.header reader.packetBitCount packets) :
    let T := reader.frozenSignedData physical P initial geo.fits W pos sites edges ports copies bundles
      headerFactor valuation entry totals old L sourceTable boot bootBits gap
    let sewn := SewnTape.wiring (k:=k) (regs:=64) (w:=rw) (ec:=ec) (width:=rw+1) physical geo.fits
      (T.enrichedFree physical P (k+1) ec ell) indexWidth
    let args := fun u => (arena).unitAddresses adOff (packets u)
    (∀ u, let ad := args u
      ad.Fitted sewn u (packets u) (T.publicWords u) adOff ∧
      packetUnitBudget ad.advice.count rw (sewn.transferFrame u ad.header ad.dst)
        (sewn.pinLayout u ad.ibase ad.hbase ad.starbase) ≤ T.limit.val) ∧
    ∀ j : Index (Fin (Module.finrank (ZMod C.p) chart.E)) (Fin (pairedTableParameters (k+1) s)) (chart.pinRadius (R+1) r),
      signedContraction sewn.slot (live j) = (if (live j)=(live reader.star) then 1 else 0)+
        ∑ ext, ∏ u, positiveMaskedNativeValue sewn eval mac T.publicWords T.registers args (live j)
          T.limit.val T.burst.val ((k+1)^25) ext u ∧
      ∀ ext, ¬ PositiveExterior sewn args (live j) rw ext →
        (∏ u, positiveMaskedNativeValue sewn eval mac T.publicWords T.registers args (live j)
          T.limit.val T.burst.val ((k+1)^25) ext u)=0 := by
  exact reader.jointSiteColumns (k:=k) eval lib marker geo L valuation entry totals extension dir boot stripe bootBits
    geometryBits strings mode ok bad (fun _ => task.ordinary arena origin 0 inputs guesses gates (fun _ => 0))
    (fun _ _ => 0) (fun _ _ => false) (fun _ _ _ => false)

end Diagonal

end BorderVNP
end Computability
end OAI
