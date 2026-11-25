import OAI.Computability.BorderVNP.DiagonalNativeBootPinStart
import OAI.Computability.BorderVNP.DiagonalNativeTimedArena
import OAI.Computability.BorderVNP.TransmissionChosenPhysical

/-! # The signed pin state on the chosen reader's physical site table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Pins TeamScales
open Branch Crossing MvPolynomial TeamContraction TeamContraction.ProcessorSlots
open RoutingISA.CompactMachine CellMacro.Generator JointHeader
open scoped Classical

variable {K : Type*} [Field K] {dim labels : ℕ} {ι : Type} [Fintype ι]
    {paid : PaidIdentity K dim labels} {aux : ι → K} {q k s : ℕ}
    {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))} {C : CommonField paid aux q k s ord}
    {chart : AdvisedBranch C} [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r mult tally w pinSize pc routines a link n ec : ℕ}
    (reader : ChosenReader chart (R+1) r mult tally w pinSize)
    (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc 64 32 routines)
    (S : SiteData R r 64 32 w a) (fit : fitsWith physical 64 32 r w a R link n ec)
    (valuation entry totals : Fin (R+1) → ℕ) (extension : Fin (R+1) → Fin 81 → Word w)
    (L : Routing.WireLayout (R+1) r link)
local notation "arena" => reader.startupArenaWith (n:=n) (reg:=64) physical a link L.header
local notation "place" => fun u : Fin (R+1) => ReaderPlacement.inArena arena (valuation u) (entry u) (totals u) (extension u)
local notation "pack" => fun u : Fin (R+1) => reader.packetAt (place u)
local notation "indexWidth" => (pairedTableParameters (k+1) s+2)*pinSize
local notation "off" => adviceOffsetWith physical r 32 64 w n
local notation "start" => freeStartWith physical r 32 64 w n
variable (D : Packing.Directory.Layout) (boot geom : GeometryAdvice.Stripe)
    (bootBits geomBits : Fin (R+1) → List Bool) (strings : Fin D.entries → Fin D.description → Bool)

set_option maxRecDepth 4500 in
set_option maxHeartbeats 2200000 in
/-- Choose the actual native-valued positive pin start on any exterior with the
common positive header. Its preserved source contains the installed boot,
geometry and private description bits, before joining any routed payloads. -/
theorem ChosenReader.booted_sitesCommon (gen : Fragment IO) (tail : List Bool) (length : (true::tail).length=L.header)
    (ext : Exterior R r link → Bool)
    (common : ∀ b, (L.exteriorEquiv ext).broadcast b = headerBits (true::tail) length)
    (u : Fin (R+1)) (pin : Fin indexWidth → Bool) (regions : JointRoom D start a boot geom)
    (copies : reader.packetBitCount ≤ r) (ceiling : (arena).next < 2^w) :
    let T := reader.startupSitesWith physical P S place fit D boot geom bootBits geomBits strings L.header
    let G := wiringWith physical P T indexWidth link n ec fit
    let args := fun v : Fin (R+1) => (arena).unitAddresses off (pack v)
    let ad := args u
    let F := G.processorFields u pin ext ad.ibase ad.hbase ad.starbase
    let f := G.transferFrame u ad.header ad.dst
    ad.Fitted G u (pack u) (T.publicWords u) off → modeTag (w := w) G args pin ext u ≠ 0 →
    ∃ B : BootedPinStart gen G T.publicWords T.registers args pin ext u,
      B.used ≤ jointBudget ad.advice.count w+f.readTicks+2 ∧
      BootHeaderState F f ad.advice (pack u) (T.publicWords u) (true::tail) B.out B.memory ∧
      JointImage D start a boot geom (bootBits u) (geomBits u) strings u.val F := by
  intro T G args ad F f ready tag
  let mac := TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n)
  have hdr : 0 < L.header := by rw [←length]; simp
  have fields := reader.arena_fitsWith physical P S fit valuation entry totals extension L u hdr copies ceiling
  have operands := reader.siteOperands_arenaWith physical P S fit valuation entry totals extension L u
  rw [operands] at fields
  have loops : LoopFits w (G.pinLayout u ad.ibase ad.hbase ad.starbase) := fields.2.2.2.2.1
  obtain ⟨es,z,mz,run,cost,_,post,image⟩ := reader.arena_header_startupCommonWith physical P S fit
    valuation entry totals extension L D boot geom bootBits geomBits strings (true::tail) length ext common u pin
    mac (T.registers u) regions hdr copies ceiling
  rw [operands] at run cost post image
  have paid : traceCost es ≤ jointBudget ad.advice.count w+f.readTicks := by
    change traceCost es ≤ jointBudget reader.packetBitCount w+f.readTicks
    rw [reader.packetAt_length] at cost
    exact cost
  obtain ⟨B,small,_,out,mem⟩ := bootedPinStart_of_header gen G T.publicWords T.registers args pin ext u tail
    ready loops tag es z mz run paid post
  exact ⟨B,small,out ▸ mem ▸ post,image⟩

end Diagonal

end BorderVNP
end Computability
end OAI
