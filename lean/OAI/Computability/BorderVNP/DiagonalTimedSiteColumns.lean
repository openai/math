import OAI.Computability.BorderVNP.DiagonalNativeTimedReaderSites
import OAI.Computability.BorderVNP.DiagonalEnrichedSiteWiring

/-! # All live reader columns on the single sewn startup and its real clock -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamScales TeamSite
open Branch Crossing MvPolynomial TeamContraction TeamContraction.ProcessorSlots
open FieldProcessor (Scale freeWidth)
open scoped Classical BigOperators

variable {K : Type*} [Field K] {dim labels : ℕ} {ι : Type} [Fintype ι]
variable {paid : PaidIdentity K dim labels} {aux : ι → K} {q k s : ℕ}
variable {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))} {common : CommonField paid aux q k s ord}
variable {chart : AdvisedBranch common} [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
variable {R r mult tally w pins e m g : ℕ} {Q Γ : Type} [Fintype Q] {α ξ : ℝ}
variable (reader : ChosenReader chart (R+1) r mult tally w pins)
variable (eval : Code) (lib : Fin 8 → Macro Q Γ m g) (mark : Fin 8 → Γ)
local notation "P" => Code.program (withStartup eval)
local notation "physical" => TimedProcessor.machine P lib mark
local notation "indexWidth" => (pairedTableParameters (k+1) s+2)*pins
local notation "l" => link ξ (R+1) (k+1)
local notation "a" => freeWidth physical α 32 64 r w (k+1)
local notation "off" => adviceOffsetWith physical r 32 64 w (k+1)
variable (geo : Scale (TimedProcessor.machine (withStartup eval).program lib mark) ((withStartup eval).slots+1) 64 32 α ξ r (k+1) R w e)
variable (L : Routing.WireLayout (R+1) r (link ξ (R+1) (k+1)))
local notation "arena" => reader.startupArenaWith (n:=(k+1)) (reg:=64) physical a l L.header
variable (valuation entry totals : Fin (R+1) → ℕ) (extension : Fin (R+1) → Fin 81 → Word w)
local notation "place" => fun u : Fin (R+1) => ReaderPlacement.inArena arena (valuation u) (entry u) (totals u) (extension u)
local notation "pack" => fun u : Fin (R+1) => reader.packetAt (place u)
variable (D : Packing.Directory.Layout) (boot geom : GeometryAdvice.Stripe)
variable (bootBits geomBits : Fin (R+1) → List Bool) (strings : Fin D.entries → Fin D.description → Bool)


open CellEntries ResiduePins ResidueIndex ResidueBox

local notation "pdim" => pairedTableParameters (k+1) s
local notation3 (prettyPrint := false) "live" j => (boxPinCodec pdim reader.rankFits reader.boxFits).encode j
local notation3 (prettyPrint := false) "mac" => TeamSiteEvents.macros lib ((k+1)^25+1)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1600000 in
/-- Split every reader column into its unit and positive branches on the very
same installed field packet. The real boot fits its native cutoffs, and every
exterior rejected by a team header check has zero joint positive contribution.
The remaining-index expression uses exactly the sewn parse tape. -/
theorem ChosenReader.jointSiteColumns (modes : AllocatedPacketModes eval lib mark geo L.header reader.packetBitCount pack)
    (ready : AllocatedPacketReady eval lib mark geo L.header reader.packetBitCount pack)
    (rejects : AllocatedPacketRejects eval lib mark geo L.header reader.packetBitCount pack)
    (extra : Fin (R+1) → Arg → Word w) (regs : Fin (R+1) → Bank w)
    (advice : Fin (R+1) → Fin r → Bool) (free : Fin (R+1) → Fin r → Fin a → Bool) :
    let S := TimedProcessor.scaleData P lib mark geo extra regs advice free
    let T := reader.startupSitesWith physical P S place geo.fits D boot geom bootBits geomBits strings L.header
    let G := SewnTape.wiring (k:=k) (regs:=64) (w:=w) (ec:=e) (width:=w+1) physical geo.fits
      (T.enrichedFree physical P (k+1) e l) indexWidth
    let args := fun u => (arena).unitAddresses off (pack u)
    (∀ u, let ad := args u
      ad.Fitted G u (pack u) (T.publicWords u) off ∧
      packetUnitBudget ad.advice.count w (G.transferFrame u ad.header ad.dst)
        (G.pinLayout u ad.ibase ad.hbase ad.starbase) ≤ T.limit.val) ∧
    ∀ j : Index (Fin (Module.finrank (ZMod common.p) chart.E)) (Fin pdim) (chart.pinRadius (R+1) r),
      signedContraction G.slot (live j) = (if (live j)=(live reader.star) then 1 else 0)+
        ∑ ext, ∏ u, positiveMaskedNativeValue G eval mac T.publicWords T.registers args (live j)
          T.limit.val T.burst.val ((k+1)^25) ext u ∧
      ∀ ext, ¬ PositiveExterior G args (live j) w ext →
        (∏ u, positiveMaskedNativeValue G eval mac T.publicWords T.registers args (live j)
          T.limit.val T.burst.val ((k+1)^25) ext u)=0 := by
  intro S T G args
  have ok := reader.sewn_startup_checks eval lib mark geo L valuation entry totals extension D boot geom bootBits
    geomBits strings ready rejects extra regs advice free
  refine ⟨ok.1,fun j => ⟨?_,ok.2 (live j)⟩⟩
  exact reader.sewn_startup_modes eval lib mark geo L valuation entry totals extension D boot geom bootBits geomBits
    strings modes extra regs advice free (live j)

end Diagonal

end BorderVNP
end Computability
end OAI
