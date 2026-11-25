import OAI.Hierarchy.DescentNamedEarnedShellChipPrice
import OAI.Hierarchy.DescentNamedCountedPostPrice

namespace OAI
/-! # The original shell row operands in the accrued preflight return -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalGraphVolume DescentDatedAddressBook Catalyst ThreeFlat.Routing Filter
noncomputable section
set_option quotPrecheck false
set_option hygiene false
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
local notation:max "cfg" source:arg layout:arg => earnedShell G t f g reset τ B n depth C source layout

local notation "inputs" => earnedInput G t f g reset τ B n depth C op drift x L

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



local notation "rawCount" => integralFrontier T x.sites d_ E nfee
local notation "boughtRows" => bought (rowBudget p q W rawCount (d_*E) H 3) W

/-- All physical row capacities used at this height by the post-preflight ledger. -/
def PostRowsAt (c height : ℕ) : Prop :=
  ∀(x : ShellSource F height) (L : TerminalPlacement) (w : ℕ),
    2^height≤2*(x.sites*(st).copies) → w+1≤c*height →
    0<p ∧ p≤height ∧ 0<x.sites ∧ height≤32*(q*p) ∧ 0<W ∧ W≤2^(height/2) ∧
    (4+(H+1)*(26+234*(st).radix))*height*T≤x.sites*d_ ∧
    (cfg x L).terminal.plane.headerRows≤boughtRows+(rawCount/(q*p)+1) ∧
    (cfg x L).terminal.pool≤boughtRows ∧ drift+1≤ scale (age_ height) 1

include op drift in
theorem earned_post_row_limits (c : ℕ)
    (branch : G.b≤2^(capRate G t g)) (big : 20≤B) (socketRoom : 2*L₀≤τ)
    (packing : 2*(L₀+wr)+uRate≤B)
    (maskReserve : 5+(hostRate t reset*(t+1)+1)+sr≤τ)
    (tailReserve : L₀+(κ+10)≤τ) (boughtB : 2*ar+1≤B)
    (chart : 2*(τ+κ+(6*(terminalDegree G t f g reset+1)+19))≤B)
    (cpu : max (NativeBranch.clockRate G t f g reset τ)
      (NativeBranch.privateMaskArenaRate G t f g reset τ 0)≤c) :
    ∀ᶠ height : ℕ in atTop,PostRowsAt G t f g reset τ B n depth C drift c height :=by
  filter_upwards [earned_shell_mask_sweep G t f g reset τ B op drift c branch big socketRoom packing
      maskReserve tailReserve boughtB chart cpu,
    stage_open_split_counts G t f g reset τ L₀ wr B (by omega) packing,
    eventually_late drift B (by omega)] with height suites counts late
  intro x L w support arch
  let J:=age_ height
  obtain ⟨_,_,q₀Fit,Wpos,Wfit,Upos,_,_⟩:=native_socket_scale G t J f g reset x.sites τ
  obtain ⟨divides,pPos,identity,low,high,_,_⟩:=counts x.sites (2^kbits) W (Nat.two_pow_pos _) Wpos q₀Fit Wfit
  have qPos : 0<q:=Nat.mul_pos (Nat.two_pow_pos _) Upos
  have bits : p≤height/2:=by
    have b : p≤q*p:=Nat.le_mul_of_pos_left _ qPos
    rw [←identity] at b
    omega
  have pool : rows≤boughtRows:=by
    change _/W*W≤(_/W+1)*W
    exact Nat.mul_le_mul_right _ (Nat.le_succ _)
  have ageRoom : drift+1≤2^(J+1):=(Nat.succ_le_succ late).trans Nat.lt_two_pow_self.le
  refine ⟨pPos,by omega,by have:=x.opened;omega,by simpa only [identity] using high,Wpos,
    (Nat.le_of_dvd pPos divides).trans (bits.trans Nat.lt_two_pow_self.le),(suites x w support arch).2,
    pool.trans (Nat.le_add_right ..),pool,?_⟩
  simpa only [TerminalScale.scale,one_mul] using ageRoom

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
