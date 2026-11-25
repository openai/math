import OAI.Hierarchy.DescentNamedEarnedMaskSweep
import OAI.Hierarchy.DescentTerminalEarnedTables

namespace OAI
/-! # The attained terminal clock, code and chip on each calibrated open host -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalGraphVolume DescentDatedAddressBook Catalyst ThreeFlat.Routing Filter
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 850000
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
local notation "chipShell" placement:arg => earnedShell G t f g reset τ B n depth C x placement
local notation "cfg" => chipShell L

local notation "chipSources" placement:arg => earnedInput G t f g reset τ B n depth C op drift x placement
local notation "inputs" => chipSources L

open DescentCompiler.TerminalScale DescentTerminalGraphVolume DescentTerminalVertexFields
open DescentTerminalCompiledPrefix.AddressPlan DescentStaticWordColumn
open DescentTerminalEmitter.Compact ThreeFlat.RAM PhysicalProcedure

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
local notation "κ" => groupRate G t f g reset
local notation "L₀" => localSocketRate G t g
local notation "uRate" => Nat.clog 2 G.b*(t+1)
local notation "sr" => L₀+uRate
local notation "wr" => τ+κ+4
local notation "ar" => sr+wr


/-- The price of the original terminal instructions, universally on the attained shell at one height. -/
def EarnedShellChipAt (c height : ℕ) : Prop :=
  ∀(x : ShellSource F height) (L : TerminalPlacement)
      (channels : MaskAllocation.Channels (st).radix) (start head w v tot : ℕ)
      (short : v*span (fmt).publicArity (fmt).roles (fmt).privateWords (fmt).nodes (fmt).addresses (fmt).piece≤tot)
      (literal : Literals ((chipSources L)).sources) (chipInputs : DescentTerminalChipRuntime.Banks),
      2^height≤2*(x.sites*(st).copies) → w+1≤c*height →
      let code_:=clock fmt (chipShell L) (chipSources L) channels start head short literal (bw:=w)
      let ctl:=chip (chipShell L) (chipSources L) (afterMeter fmt (chipShell L) channels start)
      (time fmt (chipShell L) (chipSources L) channels start head+DescentTerminalChipRuntime.clocks rows rows+
        7*(names code_+names (DescentTerminalChipRuntime.program ctl chipInputs w rows rows)))*
        (w+1)*T≤(22491*c+115*(130*c+344*(coeff c))+24*c+
          131072*(c+32*c+(coeff c))+8*(coeff c)+32*c)*(d_*(x.sites+T*E))

include op drift in
/-- The actual compiler uses one chronological mask and one sweep on each attained host. -/
theorem earned_shell_chip_price (c : ℕ)
    (branch : G.b≤2^(capRate G t g)) (big : 20≤B) (socketRoom : 2*L₀≤τ)
    (packing : 2*(L₀+wr)+uRate≤B) (router : 2*(wr+sr+2)≤B)
    (maskReserve : 5+(hostRate t reset*(t+1)+1)+sr≤τ)
    (tailReserve : L₀+(κ+10)≤τ) (bought : 2*ar+1≤B)
    (chart : 2*(τ+κ+(6*(terminalDegree G t f g reset+1)+19))≤B)
    (books : 2*bookRate G t f g reset τ≤B)
    (cpu : max (NativeBranch.clockRate G t f g reset τ)
      (NativeBranch.privateMaskArenaRate G t f g reset τ 0)≤c) :
    ∀ᶠ height : ℕ in atTop,EarnedShellChipAt G t f g reset τ B n depth C op drift c height :=by
  filter_upwards [earned_shell_mask_sweep G t f g reset τ B op drift c branch big socketRoom packing
      maskReserve tailReserve bought chart cpu,
    earned_tables G op drift t f g reset τ B branch big socketRoom packing router chart books,
    early_native_packing G t f g reset τ B big socketRoom packing,
    stage_open_split_counts G t f g reset τ L₀ wr B (by omega) packing,
    eventually_ge_atTop 10] with height suites tables packed counts large
  intro x L channels start head w v tot short literal chipInputs support arch
  let J:=age_ height
  obtain ⟨mask,sweep⟩:=suites x w support arch
  obtain ⟨_,_,q₀Fit,Wpos,Wfit,Upos,_,_⟩:=native_socket_scale G t J f g reset x.sites τ
  obtain ⟨divides,pPos,identity,low,high,_,_⟩:=counts x.sites (2^kbits) W (Nat.two_pow_pos _) Wpos q₀Fit Wfit
  have positive : 0<q:=Nat.mul_pos (Nat.two_pow_pos _) Upos
  have packet : height≤32*(q*p):=by simpa only [identity] using high
  have bits : W≤height/2:=by
    have a:=Nat.le_of_dvd pPos divides
    have b : p≤q*p:=Nat.le_mul_of_pos_left _ positive
    rw [←identity] at b
    omega
  have popPos : 0<x.sites:=by have:=x.opened;omega
  exact earned_shell_chip_bill G t f g reset τ B n depth C op drift x L channels start head w c short
    literal chipInputs (earned_counts_at G t f g reset τ B n depth C op drift x L (tables x.sites))
    Wpos (Nat.mul_pos positive pPos) (calibrated_hosts_positive G t J f g reset x.sites τ popPos)
    (bits.trans Nat.lt_two_pow_self.le) large support (packed x.sites).2.2.1 arch packet
    (packed x.sites).2.1 high mask sweep

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
