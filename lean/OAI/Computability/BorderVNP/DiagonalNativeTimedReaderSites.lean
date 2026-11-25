import OAI.Computability.BorderVNP.DiagonalNativeTimedArenaChecks
import OAI.Computability.BorderVNP.TransmissionChosenPhysical

/-! # The broadcast-mode identity on the chosen reader's joint literal itself -/

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
variable {R r mult tally w pins n e m g : ℕ} {Q Γ : Type} [Fintype Q] {α ξ : ℝ}
variable (reader : ChosenReader chart (R+1) r mult tally w pins)
variable (eval : Code) (lib : Fin 8 → Macro Q Γ m g) (mark : Fin 8 → Γ)
local notation "P" => Code.program (withStartup eval)
local notation "physical" => TimedProcessor.machine P lib mark
local notation "indexWidth" => (pairedTableParameters (k+1) s+2)*pins
local notation "l" => link ξ (R+1) n
local notation "a" => freeWidth physical α 32 64 r w n
local notation "off" => adviceOffsetWith physical r 32 64 w n
variable (geo : Scale (TimedProcessor.machine (withStartup eval).program lib mark) ((withStartup eval).slots+1) 64 32 α ξ r n R w e)
variable (L : Routing.WireLayout (R+1) r (link ξ (R+1) n))
local notation "arena" => reader.startupArenaWith (n:=n) (reg:=64) physical a l L.header
variable (valuation entry totals : Fin (R+1) → ℕ) (extension : Fin (R+1) → Fin 81 → Word w)
local notation "place" => fun u : Fin (R+1) => ReaderPlacement.inArena arena (valuation u) (entry u) (totals u) (extension u)
local notation "pack" => fun u : Fin (R+1) => reader.packetAt (place u)
variable (D : Packing.Directory.Layout) (boot geom : GeometryAdvice.Stripe)
variable (bootBits geomBits : Fin (R+1) → List Bool) (strings : Fin D.entries → Fin D.description → Bool)

set_option maxRecDepth 3500 in
set_option maxHeartbeats 1800000 in
/-- The site's actual startup data, including the two boot/geometry stripes and the
private half-literal of the stored directory, is the very wiring in the native mode sum. -/
theorem ChosenReader.sewn_startup_modes (modes : AllocatedPacketModes eval lib mark geo L.header reader.packetBitCount pack)
    (extra : Fin (R+1) → Arg → Word w) (regs : Fin (R+1) → Bank w)
    (advice : Fin (R+1) → Fin r → Bool) (free : Fin (R+1) → Fin r → Fin a → Bool)
    (pin : Fin indexWidth → Bool) :
    let S := TimedProcessor.scaleData P lib mark geo extra regs advice free
    let T := reader.startupSitesWith physical P S place geo.fits D boot geom bootBits geomBits strings L.header
    let G := wiringWith physical P T indexWidth l n e geo.fits
    let args := fun u => (arena).unitAddresses off (pack u)
    signedContraction G.slot pin =
      (if pin=(pack 0).reference then 1 else 0) +
      ∑ ext, ∏ u, positiveMaskedNativeValue G eval (TeamSiteEvents.macros lib (n^25+1))
        T.publicWords T.registers args pin (ticks ξ r n) (TeamScales.width n (1/2)) (n^25) ext u := by
  intro S T G args
  have banks : (fun u => (reader.siteOperandsWith physical P S place geo.fits L.header u).bank (extra u)) =
      fun u => ((arena).operands u off (pack u)).bank (extra u) := by
    funext u
    rw [reader.siteOperands_arenaWith physical P S geo.fits valuation entry totals extension L u]
  let pub := fun u => ((arena).operands u off (pack u)).bank (extra u)
  have publicEq : T.publicWords = pub := banks
  let chosen := TimedProcessor.scaleData P lib mark geo pub regs (fun _ _ => false) T.free
  have same : T = chosen.withPacket pack :=
    congrArg (fun words => { T with publicWords := words }) publicEq
  rw [show G = wiringWith physical P (chosen.withPacket pack) indexWidth l n e geo.fits from
    congrArg (fun data => wiringWith physical P data indexWidth l n e geo.fits) same,publicEq]
  exact modes extra regs T.free pin

set_option maxRecDepth 3500 in
/-- On precisely the same jointly installed site, every packet fits and its unit
time is charged. The positive product vanishes for each malformed exterior wire. -/
theorem ChosenReader.sewn_startup_checks
    (ready : AllocatedPacketReady eval lib mark geo L.header reader.packetBitCount pack)
    (rejects : AllocatedPacketRejects eval lib mark geo L.header reader.packetBitCount pack)
    (extra : Fin (R+1) → Arg → Word w) (regs : Fin (R+1) → Bank w)
    (advice : Fin (R+1) → Fin r → Bool) (free : Fin (R+1) → Fin r → Fin a → Bool) :
    let S := TimedProcessor.scaleData P lib mark geo extra regs advice free
    let T := reader.startupSitesWith physical P S place geo.fits D boot geom bootBits geomBits strings L.header
    let G := wiringWith physical P T indexWidth l n e geo.fits
    let args := fun u => (arena).unitAddresses off (pack u)
    (∀ u, let addr := args u
      addr.Fitted G u (pack u) (T.publicWords u) off ∧
      packetUnitBudget addr.advice.count w (G.transferFrame u addr.header addr.dst)
        (G.pinLayout u addr.ibase addr.hbase addr.starbase) ≤ T.limit.val) ∧
    ∀ (pin : Fin indexWidth → Bool) ext, ¬ PositiveExterior G args pin w ext →
      (∏ u, positiveMaskedNativeValue G eval (TeamSiteEvents.macros lib (n^25+1))
        T.publicWords T.registers args pin T.limit.val T.burst.val (n^25) ext u) = 0 := by
  intro S T G args
  have words : T.publicWords = fun u => ((arena).operands u off (pack u)).bank (extra u) := by
    funext u
    change (reader.siteOperandsWith physical P S place geo.fits L.header u).bank (extra u) = _
    rw [reader.siteOperands_arenaWith physical P S geo.fits valuation entry totals extension L u]
  refine ⟨?_,rejects T extra words rfl⟩
  intro u
  rw [words]
  exact ready T extra u

end Diagonal

end BorderVNP
end Computability
end OAI
