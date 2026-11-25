import OAI.Computability.BorderVNP.DiagonalFrozenSignedDeployment

/-! # The signed processor's actual startup cost before selecting any site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamScales TeamSite
open FieldProcessor (Scale freeWidth)
open scoped Classical

variable {Q Γ : Type} [Fintype Q] {μ g r n R w ec pins : ℕ} {α ξ : ℝ}
    {eval : Code} {lib : Fin 8 → Macro Q Γ μ g} {mark : Fin 8 → Γ}
local notation "prog" => Code.program (withStartup eval)
local notation "physical" => TimedProcessor.machine prog lib mark
local notation "width₀" => freeWidth physical α 32 64 r w n
local notation "ell" => link ξ (R+1) n
variable {geo : Scale (TimedProcessor.machine (withStartup eval).program lib mark) ((withStartup eval).slots+1)
    64 32 α ξ r n R w ec} {header copied : ℕ} {pack : Fin (R+1) → ReferencePacket w pins}

/-- The timed initialization bound also applies after replacing the literal
advice, since neither physical frame size counts the contents of its bits. -/
theorem AllocatedPacketReady.installedTicks (ready : AllocatedPacketReady eval lib mark geo header copied pack)
    (site : SiteData R r 64 32 w width₀) (u : Fin (R+1)) :
    let ad := (programArena physical R r w n width₀ ell header copied).unitAddresses
      (adviceOffsetWith physical r 32 64 w n) (pack u)
    let wire := wiringWith physical prog site pins ell n ec geo.fits
    packetUnitBudget ad.advice.count w (wire.transferFrame u ad.header ad.dst)
      (wire.pinLayout u ad.ibase ad.hbase ad.starbase) ≤ ticks ξ r n := by
  intro ad wire
  let patched := wiringWith physical prog (site.withPacket pack) pins ell n ec geo.fits
  have cost : packetUnitBudget ad.advice.count w (patched.transferFrame u ad.header ad.dst)
      (patched.pinLayout u ad.ibase ad.hbase ad.starbase) ≤ ticks ξ r n :=
    (ready site (fun _ _ => 0) u).2
  have len : patched.program.length=wire.program.length := rfl
  simpa only [Wiring.transferFrame,Wiring.pinLayout,len] using cost

end TeamContraction.ProcessorSlots

namespace Diagonal

open Crossing Branch PackedHistoryCircuit.Normalized VPVNP BurstRAM
open TeamContraction TeamContraction.ProcessorSlots TeamSite TeamScales Filter
open RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine
open FieldProcessor (Scale freeWidth)
open scoped Classical

section Reader

variable {F K : Type} [Field F] [Field K] {D m : ℕ} {G : PaidIdentity F D m}
    {ι : Type} [Fintype ι] {aux : ι → F} {q k size : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {common : CommonField G aux q k size ord} {chart : AdvisedBranch common}
    [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    {R r w pin ec : ℕ} {α ξ : ℝ} (cube : FixedCube K)
    (reader : ChosenReader chart (R+1) r w w w pin)

local notation3 (prettyPrint := false) "physical" => cube.signedSiteProgram G
local notation3 (prettyPrint := false) "eval" => signedBody (cube.cubeID G)
local notation3 (prettyPrint := false) "P" => (signedProgram (cube.cubeID G)).program
local notation3 (prettyPrint := false) "ell" => link ξ (R+1) (k+1)
local notation3 (prettyPrint := false) "a" => freeWidth physical α 32 64 r w (k+1)
local notation3 (prettyPrint := false) "pins" => (pairedTableParameters (k+1) size+2)*pin

variable (geo : Scale (cube.signedSiteProgram G) ((withStartup (signedBody (cube.cubeID G))).slots+1)
    64 32 α ξ r (k+1) R w ec) (L : Routing.WireLayout (R+1) r (link ξ (R+1) (k+1)))
local notation3 (prettyPrint := false) "arena" => reader.startupArenaWith (n:=k+1) (reg:=64) physical a ell L.header
local notation3 (prettyPrint := false) "base" => adviceOffsetWith physical r 32 64 w (k+1)

/-- The measured gather, common-header copy and native pin startup on each
site at this length. The operand placement and literal table may vary
after the absolute simulation cutoff has been chosen. -/
def ChosenReader.FrozenBootMeter : Prop :=
  ∀ (valuation entry total : Fin (R+1) → ℕ) (ext : Fin (R+1) → Fin 81 → Word w)
    (site : SiteData R r 64 32 w a) (u : Fin (R+1)),
    let packet := reader.packetAt (ReaderPlacement.inArena arena (valuation u) (entry u) (total u) (ext u))
    let ad := (arena).unitAddresses base packet
    let wire := wiringWith physical P site pins ell (k+1) ec geo.fits
    packetUnitBudget ad.advice.count w (wire.transferFrame u ad.header ad.dst)
      (wire.pinLayout u ad.ibase ad.hbase ad.starbase) ≤ ticks ξ r (k+1)

end Reader

variable {F K : Type} [Field F] [Field K] {D m : ℕ} [NeZero D] {G : PaidIdentity F D m}
    {S : SiteSchedule G} {extra E dlog Q A B j : ℕ} (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{0} s (E+1) dlog Q A B j)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1600000 in
/-- The deadline is met simultaneously for the installed signed program on
the stretched sequence. The choice of scale precedes every field chart,
charged reader, site literal and operand bank. -/
theorem JointSchedule.eventually_frozen_boot_meter (φ : K →+* F) (q : ℕ)
    (f : ℕ → ℕ) (hf : PolynomiallyBounded f) (c power : ℕ) :
    ∀ᶠ k : ℕ in atTop, let n := k+1
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n
      let w := b.physical.word n
      let ξ := (s.τ:ℝ)/5
      let ec := Wires.sortExponent (block ξ n)
      let T := f (adviceScale b.σ b.ρ n)
      ∃ geo : Scale (cube.signedSiteProgram G) ((withStartup (signedBody (cube.cubeID G))).slots+1)
        64 32 s.α ξ r n R w ec,
      ∀ {size : ℕ} {ord : Fin n × Bool ≃ Fin (2*n)}
        {common : CommonField G (φ ∘ cube.table) q k size ord} (chart : AdvisedBranch common)
        [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
        (reader : ChosenReader chart (R+1) r w w w (T+6)), reader.charge ≤ c*(T+1)^power →
        ∀ L : Routing.WireLayout (R+1) r (link ξ (R+1) n), 0<L.header → reader.FrozenBootMeter cube geo L := by
  filter_upwards [b.eventually_fixed_signed_sites G cube φ q f hf c power] with k offered
  intro n r R w ξ ec T
  obtain ⟨geo,checks⟩ := offered
  refine ⟨geo,?_⟩
  intro size ord common chart prime alg reader small L positive valuation entry total ext site u
  have sameLink : b.physical.link n = link ξ (R+1) n := by
    dsimp only [R,ξ]
    rw [(b.sizes (Nat.succ_pos k)).1]
    rfl
  let L' : Routing.WireLayout (R+1) r (b.physical.link n) :=
    ⟨L.three,L.width,L.header,fun e => by rw [sameLink]; exact L.fits e⟩
  have ready := (checks chart reader small L' positive valuation entry total ext).2.1
  exact ready.installedTicks site u

end Diagonal

end BorderVNP
end Computability
end OAI
