import OAI.Computability.BorderVNP.DiagonalNativeCanonicalBoot
import OAI.Computability.BorderVNP.DiagonalNativePositiveSupport

/-! # The booted signed evaluator before authenticating its shared exterior

The header and each team's pin substitution are available immediately after
the physical copy. The records below can therefore be chosen on every
positive exterior before asking whether all teams reach their private calls.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator RoutingISA.CompactMachine
open PackedHistoryCircuit BorderVNP.Cube CellMacro.Generator JointHeader Routing
open scoped Classical

section Boot

variable {R r t d link inner n w : ℕ} {Edge : Type}
    (gen : Fragment IO) (G : Wiring R r t d link inner n Edge) (pub : Fin (R+1) → Arg → Word w)
    (reg : Fin (R+1) → Bank w) (args : Fin (R+1) → UnitAddresses) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (u : Fin (R+1))

local notation3 (prettyPrint := false) "mac" => TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n)
local notation3 (prettyPrint := false) "ad" => args u
local notation3 (prettyPrint := false) "loc" => G.pinLayout u (args u).ibase (args u).hbase (args u).starbase
local notation3 (prettyPrint := false) "f" => G.transferFrame u (args u).header (args u).dst
local notation3 (prettyPrint := false) "F" => G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase

/-- Actual incoming RAM, header trace and complete pin-return dictionary of one team. -/
structure BootedPinStart where
  /-- Trace of the executed scalar and packet startup and the common-header copy. -/
  trace : List (TeamRAM.Event w)
  /-- Registers after the copy. -/
  out : Bank w
  /-- Memory after the copy. -/
  memory : Memory w
  /-- Execution begins at the actual tape and native initial registers. -/
  boot : Runs (pub u) mac bootHeader (reg u) (processorMemory F w) trace out memory
  /-- Copy registers identify the physical partner and source. -/
  stable : (f).Stable (readings out)
  /-- The first copied word selects evaluation. -/
  positive : (memory (f).dst).val ≠ 0
  /-- The physical mask selects the positive branch. -/
  tagged : modeTag (w := w) G args pin ext u ≠ 0
  /-- The native dispatch prefix's addresses fit the processor word. -/
  frameFit : (pub u 0).val+15 < 2^w
  /-- Pin choices and all native pin returns correspond in both directions. -/
  pins : (Fin (loc).guessWidth → Bool) ≃
    Pins.Return (pub u) (install gen n mac) (Function.update out 10 (memory (f).dst)) memory
  /-- Each pin's actual prepared memory, trace spelling and cost. -/
  outputs : PositivePinOutputs loc pins

variable {gen G pub reg args pin ext u}
variable (B : BootedPinStart gen G pub reg args pin ext u)

/-- The pre-call pin state on the original shared exterior. -/
noncomputable def BootedPinStart.start : PinStart gen n w :=
  ⟨pub u,mac,Function.update B.out 10 (B.memory (f).dst),B.memory,(loc).guessWidth,B.pins⟩

/-- Actual ticks spent at entry to the positive evaluation branch. -/
def BootedPinStart.used : ℕ := traceCost B.trace+2

variable {dim box lanes selectors symbols : ℕ}
    (id : TableEntry dim box lanes selectors symbols → ℕ)

/-- A missing complete pre-call preparation makes this team's native value zero at
every cutoff, including on corrupt exterior payloads. -/
theorem BootedPinStart.zero_of_empty (ticks burst clock : ℕ) (empty : ¬ Nonempty (B.start.Prefix id)) :
    positiveMaskedNativeValue G (signedBody id) mac pub reg args pin ticks burst clock ext u = 0 :=
  positiveMasked_zero_of_prefix_empty id gen G pub reg args pin ext u ticks burst clock B.start
    B.trace B.out B.memory B.boot B.stable B.positive rfl rfl rfl rfl empty

/-- On a jointly reachable exterior the same startup determines the bounded
value of the physically certified team. -/
theorem BootedPinStart.team_value (limit burst : ℕ) (small : B.used ≤ limit)
    (cap : TeamScales.width n (1/2) ≤ burst)
    (C : PositiveContinuation id gen n (pub u) mac B.start.bank B.memory B.pins B.used limit) :
    let team := C.team burst cap B.frameFit
    positiveMaskedNativeValue G (signedBody id) mac pub reg args pin limit burst (n^25) ext u =
      boundedValue (signedBody id) team.pub (install gen n team.routines) team.bank team.memory
        (team.limit-team.used) team.burst (n^25) :=
  positiveMasked_at_boot id gen G pub reg args pin ext u limit burst cap B.trace B.out B.memory
    B.boot B.stable B.positive B.tagged small B.frameFit B.pins C

variable (gen G pub reg args pin ext u)

/-- Construct the actual pre-call state from the executed packet boot. Reads
the mode bit from its copied word and preserves the same returned registers,
memory, and authentic pin guesses for subsequent history decoding. -/
theorem bootedPinStart_of_header {packet : ReferencePacket w d} {offset : ℕ} (tail : List Bool)
    (ready : (ad).Fitted G u packet (pub u) offset) (loops : LoopFits w loc)
    (tag : modeTag (w := w) G args pin ext u ≠ 0) (trace : List (TeamRAM.Event w))
    (out : Bank w) (mem : Memory w)
    (run : Runs (pub u) mac bootHeader (reg u) (processorMemory F w) trace out mem)
    (paid : traceCost trace ≤ jointBudget (ad).advice.count w+(f).readTicks)
    (header : BootHeaderState F f (ad).advice packet (pub u) (true::tail) out mem) :
    ∃ B : BootedPinStart gen G pub reg args pin ext u,
      B.used ≤ jointBudget (ad).advice.count w+(f).readTicks+2 ∧
      B.trace=trace ∧ B.out=out ∧ B.memory=mem := by
  have front := ready.physical.frame
  have endAddr := ready.physical.out
  change (pub u 0).val+31 ≤ (args u).dst at front
  change (args u).dst+(args u).header < 2^w at endAddr
  have regFit : readings (pub u) 0+24 < 2^w := by change (pub u 0).val+24 < 2^w; omega
  have one : 1 < 2^w := by change (pub u 0).val+24 < 2^w at regFit; omega
  have bit := header.header ⟨0,by simp⟩
  change mem ((f).dst+0) = DiagonalResidueRAM.word w 1 at bit
  have positive : (mem (f).dst).val ≠ 0 := by
    rw [Nat.add_zero] at bit
    rw [bit]
    change 1 % 2^w ≠ 0
    rw [Nat.mod_eq_of_lt one]
    decide
  obtain ⟨stride,count,width,_⟩ := ready.pinRoom
  obtain ⟨pins,outputs⟩ := preparePins_exact loc (pub u) (install gen n mac) mem (Function.update out 10 (mem (f).dst))
    header.frame.pins regFit (show 0 < (loc).teams by change 0 < R+1; omega) stride count width loops
  exact ⟨⟨trace,out,mem,run,header.registers,positive,tag,by change (pub u 0).val+24 < 2^w at regFit; omega,
    pins,outputs⟩,Nat.add_le_add_right paid 2,rfl,rfl,rfl⟩

end Boot

section Installed

variable {dim box lanes selectors symbols R r w d link n ec a : ℕ}

/-- Run the actual startup for a shared positive header on the complete
physical exterior. The remaining link bits are unrestricted. Both the
pre-call pin state and the typed packet refer to this same native trace. -/
theorem bootedPinStart_of_common (physical : UniversalMachine.Program)
    (id : TableEntry dim box lanes selectors symbols → ℕ) (gen : Fragment IO)
    (data : SiteData R r 64 32 w a) (packet : Fin (R+1) → ReferencePacket w d)
    (fit : fitsWith physical 64 32 r w a R link n ec) (args : Fin (R+1) → UnitAddresses)
    (pin : Fin d → Bool) (L : WireLayout (R+1) r link) (ext : Exterior R r link → Bool) (u : Fin (R+1))
    (tail : List Bool) (length : (true::tail).length=L.header)
    (common : ∀ b, (L.exteriorEquiv ext).broadcast b = headerBits (true::tail) length) :
    let P := (withStartup (signedBody id)).program
    let G := wiringWith physical P (data.withPacket packet) d link n ec fit
    let ad := args u
    let f := G.transferFrame u ad.header ad.dst
    let loc := G.pinLayout u ad.ibase ad.hbase ad.starbase
    let F := G.processorFields u pin ext ad.ibase ad.hbase ad.starbase
    let pub := data.publicWords
    ad.header=L.header → ad.Fitted G u (packet u) (pub u) (adviceOffsetWith physical r 32 64 w n) →
    LoopFits w loc → modeTag (w := w) G args pin ext u ≠ 0 →
    (pub u 0).val+112 ≤ ad.dst →
    (ad.advice.dst+(packet u).bits.length ≤ ad.dst ∨ ad.dst+ad.header ≤ ad.advice.dst) →
    ∃ B : BootedPinStart gen G pub data.registers args pin ext u,
      B.used ≤ jointBudget ad.advice.count w+f.readTicks+2 ∧
      BootHeaderState F f ad.advice (packet u) (pub u) (true::tail) B.out B.memory := by
  intro P G ad f loc F pub size ready loops tag frameBefore apart
  let mac := TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n)
  obtain ⟨es,z,mz,run,cost,_,post⟩ := packet_header_runCommonWith physical P data packet link n ec fit u pin
    L (true::tail) length ext common ad.ibase ad.hbase ad.starbase ad.dst (pub u) mac (data.registers u) ad.advice
    (size ▸ ready.operands) (size ▸ ready.physical) (size ▸ ready.gather) ready.extended ready.literalOffset
    ready.packet ready.reference frameBefore (size ▸ apart)
  rw [←size] at cost post
  obtain ⟨B,paid,_,hout,hmem⟩ := bootedPinStart_of_header gen G pub data.registers args pin ext u tail
    ready loops tag es z mz run cost post
  exact ⟨B,paid,hout ▸ hmem ▸ post⟩

end Installed

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
