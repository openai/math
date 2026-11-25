import OAI.Hierarchy.DescentNamedEarnedCalendarRates
import OAI.Hierarchy.DescentTerminalEarnedChipClock
import OAI.Hierarchy.DescentWalshDyadicBudget

namespace OAI
/-! # Price of the actual chip and terminal word program on the calibrated named shell -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalGraphVolume DescentDatedAddressBook Catalyst ThreeFlat.Routing Filter
noncomputable section
set_option quotPrecheck false
open DescentTerminalCompiledPrefix DescentTerminalPreflightSpace DescentTerminalLocalPortBook ProtocolRAM
open AddressPlan
variable {F : Type} [Field F] (G : PoweredGadget F) (t f g reset τ B n depth C : ℕ)

local notation "src_" h:arg => ShellSource F h
local notation "age_" h:arg => Nat.log 2 h/(2*B)
local notation "st_" h:arg x:arg => stageNumbers G t (age_ h) f g reset (ShellSource.sites x) (tail τ (age_ h))
local notation "kb_" h:arg => groupBits t (age_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "bw_" h:arg x:arg => NativeBranch.binLimit (k:=kb_ h) (st_ h x)
local notation "j_" h:arg x:arg => Nat.clog 2 (NativeBranch.localLimit G (st_ h x))
local notation "unit_" h:arg => G.b^(t*(age_ h))*G.b
local notation "q_" h:arg x:arg => 2^(j_ h x)*(unit_ h)
local notation "p_" h:arg x:arg => (bw_ h x)*(h/(16*((q_ h x)*(bw_ h x))))
local notation "pins_" x:arg => Fintype.card (Port (ShellSource.ports x) (ShellSource.X x).width)
local notation "normal_" h:arg x:arg => terminalWireBudget (ShellSource.X x) G (st_ h x) (p_ h x) n depth C f g
local notation "pool_" h:arg x:arg => terminalPool (ShellSource.X x) G (st_ h x) (p_ h x) (q_ h x) (bw_ h x) n depth C f g
local notation "raw_" h:arg x:arg => terminalRawRows (ShellSource.X x) G (st_ h x) (p_ h x) (q_ h x) n depth C f g
local notation "dim_" h:arg x:arg => (st_ h x).groupWidth (kb_ h) (tail τ (age_ h)) 0+kb_ h
local notation "pub_" h:arg x:arg => (pins_ x)*2^((j_ h x)+((dim_ h x)-2*(j_ h x)))


variable (op : RotorSpec) (drift : ℕ) {height : ℕ} (x : ShellSource F height) (L : TerminalPlacement)
local notation "st" => st_ height x
local notation "k" => kb_ height
local notation "W" => bw_ height x
local notation "q" => q_ height x
local notation "p" => p_ height x
local notation "bins" => calibratedBins x.X G t (age_ height) f g reset x.sites τ height n depth C
local notation "piece" => height/(16*(q*W))
local notation "rows" => pool_ height x
local notation "V" => (st).groupCount (st).length*2^k
local notation "A" => NativeBranch.localLimit G st
local notation "fmt" => earnedFormat G op st q p drift
local notation "totalBits" => max 1 (V*actualSpan G st op q p drift)
local notation "routes" => RouteSources.Tables.mk 4 V (V*A) A (Book.tokenBits (V*A)) W q bins
local notation "cfg" => earnedShell G t f g reset τ B n depth C x L

local notation "inputs" => earnedInput G t f g reset τ B n depth C op drift x L

open DescentCompiler.TerminalScale DescentTerminalGraphVolume DescentTerminalVertexFields
open DescentTerminalCompiledPrefix.AddressPlan DescentStaticWordColumn
open DescentTerminalEmitter.Compact ThreeFlat.RAM PhysicalProcedure

private theorem actual_raw_paid (wire copies pitch binWidth exterior homes : ℕ) (window : 0<copies*pitch)
    (bin : 0<binWidth) (hosts : 0<homes) :
    poolBatchCount wire (copies*pitch) ≤ rowBudget pitch copies binWidth wire exterior homes 3 / binWidth * binWidth :=by
  have rounded:=DescentWalshDyadicBudget.ceil_le wire (copies*pitch) window
  have grow : wire≤3*(2*wire+exterior):=by omega
  have parts:=Nat.div_le_div_right (c:=copies*pitch) grow
  let subtotal:=3*(2*wire+exterior)/(copies*pitch)+homes*(3+3)
  have rem:=Nat.mod_lt (2*subtotal+binWidth) bin
  have split:=Nat.div_add_mod (2*subtotal+binWidth) binWidth
  rw [Nat.mul_comm binWidth] at split
  change _ ≤ (2*subtotal+binWidth)/binWidth*binWidth
  dsimp only [subtotal] at *
  omega

local notation "E" => pins_ x
local notation "T" => 2^(age_ height)
local notation "s_" => (st).firstWidth G.b p
local notation "d_" => (st).copies*s_
local notation "H" => (st).hostSize (st).length
local notation "raw" => raw_ height x
local notation "kbits" => j_ height x
local notation "rbits" => (dim_ height x)-2*(j_ height x)
local notation "nfee" => ⌈258*reentryRate depth C+reentryExteriorRate depth C 256
  (GroupStage.depthBound (atRound (st).rounds) n f g)⌉₊
local notation "coeff" c:arg => 6*(32*c)*(3+4*nfee)+2*c
local notation:max "cohort" blocks:arg => cohortSize («q»:=(fmt).publicArity) (t:=(fmt).roles)
  («H»:=(fmt).privateWords) (N:=(fmt).nodes) («A»:=(fmt).addresses) (w:=(fmt).piece)
  (groups:=(fmt).groups) (blocks:=blocks)
local notation:max "cells" blocks:arg => MaskAllocation.marks (channelSize («q»:=(fmt).publicArity) (t:=(fmt).roles)
  («H»:=(fmt).privateWords) (N:=(fmt).nodes) («A»:=(fmt).addresses) (w:=(fmt).piece)
  (groups:=(fmt).groups) (blocks:=blocks))+cohort blocks

/-- The physical paid-word batch covers every raw numerical row before rounding to whole bins. -/
theorem earned_raw_rows_le_pool (bin : 0<W) (window : 0<q*p) (sites : 0<H) : raw≤rows :=
  actual_raw_paid _ q p W _ H window bin sites

theorem earned_shell_chip_bill {blocks v tot : ℕ} (channels : MaskAllocation.Channels blocks)
    (start head w factor : ℕ)
    (short : v*span (fmt).publicArity (fmt).roles (fmt).privateWords (fmt).nodes (fmt).addresses (fmt).piece≤tot)
    (literal : Literals (inputs).sources) (chipInputs : DescentTerminalChipRuntime.Banks)
    (counts : EarnedCounts height cfg inputs) (bin : 0<W) (pack : 0<q*p) (sites : 0<H)
    (rowsFit : W≤2^(height/2)) (large : 10≤height) (support : 2^height≤2*(x.sites*(st).copies))
    (timeWidth : T≤ s_) (arch : w+1≤factor*height) (packet : height≤32*(q*p))
    (origin : (st).copies=2^(kbits+(kbits+rbits))) (exterior : height≤32*(2^kbits*s_))
    (mask : (privateMaskedClock (cells blocks) (cohort blocks) H blocks p+
      privateMaskedNames (cells blocks) (cohort blocks) blocks p)*(w+1)*T≤3213*factor*(x.sites*d_))
    (sweep : (4+(H+1)*(26+234*blocks))*height*T≤x.sites*d_) :
    let clock_:=clock fmt cfg inputs channels start head short literal (bw:=w)
    let ctl:=chip cfg inputs (afterMeter fmt cfg channels start)
    (time fmt cfg inputs channels start head+DescentTerminalChipRuntime.clocks rows rows+
      7*(names clock_+names (DescentTerminalChipRuntime.program ctl chipInputs w rows rows)))*
        (w+1)*T≤(22491*factor+115*(130*factor+344*(coeff factor))+24*factor+
          131072*(factor+32*factor+(coeff factor))+8*(coeff factor)+32*factor)*(d_*(x.sites+T*E)) :=by
  dsimp only
  have purchased:raw≤rows:=actual_raw_paid _ q p W _ H pack bin sites
  have bounded:w+1≤(32*factor)*(q*p):=calc
    _ ≤ factor*height:=arch
    _ ≤ factor*(32*(q*p)):=Nat.mul_le_mul_left _ packet
    _ = _ :=by ring
  have pool:=covered_bank T x.sites (st).copies s_ E nfee p q W H height (w+1) (32*factor) factor blocks
    rowsFit large support timeWidth bounded arch sweep
  have floor_:=Nat.div_mul_le_self
    (rowBudget p q W (integralFrontier T x.sites d_ E nfee) (d_*E) H 3) W
  have realRows:rows*(w+1)*T≤(coeff factor)*(d_*(x.sites+T*E)):=
    (Nat.mul_le_mul_right T (Nat.mul_le_mul_right (w+1) floor_)).trans pool
  apply earned_chip_clock fmt cfg inputs channels start head short literal chipInputs counts purchased (Nat.le_succ _)
    large support timeWidth arch origin exterior rfl _ sweep realRows
  change (privateMaskedClock (cells blocks) (cohort blocks) H blocks p+
    7*privateMaskedNames (cells blocks) (cohort blocks) blocks p)*(w+1)*T≤22491*factor*(x.sites*d_)
  simp only [Nat.add_mul,Nat.mul_assoc] at mask ⊢
  omega

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
