import OAI.Hierarchy.DescentNamedEarnedShellChipBill
import OAI.Hierarchy.DescentTerminalMaskSetup
import OAI.Hierarchy.DescentPreflightHostUnits

namespace OAI
/-! # The authentic private mask and host sweep at the chosen terminal address -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalGraphVolume DescentDatedAddressBook Catalyst ThreeFlat.Routing Filter
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 650000
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
local notation:max "cohort" bn:arg => cohortSize («q»:=(fmt).publicArity) (t:=(fmt).roles)
  («H»:=(fmt).privateWords) (N:=(fmt).nodes) («A»:=(fmt).addresses) (w:=(fmt).piece)
  (groups:=(fmt).groups) (blocks:=bn)
local notation:max "cells" bn:arg => MaskAllocation.marks (channelSize («q»:=(fmt).publicArity) (t:=(fmt).roles)
  («H»:=(fmt).privateWords) (N:=(fmt).nodes) («A»:=(fmt).addresses) (w:=(fmt).piece)
  (groups:=(fmt).groups) (blocks:=bn))+cohort bn

local notation "κ" => groupRate G t f g reset
local notation "L₀" => localSocketRate G t g
local notation "uRate" => Nat.clog 2 G.b*(t+1)
local notation "sr" => L₀+uRate
local notation "wr" => τ+κ+4
local notation "ar" => sr+wr

private theorem host_sweep {H₀ b : ℕ} (hosts : 0<H₀) (radix : 0<b) :
    4+(H₀+1)*(26+234*b)≤H₀*(524*b) := by
  have twice : H₀+1≤2*H₀ :=by omega
  have cost : 26+234*b≤260*b :=by omega
  have body:=Nat.mul_le_mul twice cost
  have four : 4≤4*(H₀*b):=by have:=Nat.mul_pos hosts radix;omega
  nlinarith only [body,four]

include op drift in
/-- Both attained costs use the original radix, host count and free scalar width. -/
theorem earned_shell_mask_sweep (c : ℕ)
    (branch : G.b≤2^(capRate G t g)) (big : 20≤B) (_socketRoom : 2*L₀≤τ)
    (packing : 2*(L₀+wr)+uRate≤B)
    (maskReserve : 5+(hostRate t reset*(t+1)+1)+sr≤τ)
    (tailReserve : L₀+(κ+10)≤τ) (bought : 2*ar+1≤B)
    (chart : 2*(τ+κ+(6*(terminalDegree G t f g reset+1)+19))≤B)
    (cpu : max (NativeBranch.clockRate G t f g reset τ)
      (NativeBranch.privateMaskArenaRate G t f g reset τ 0)≤c) :
    ∀ᶠ height : ℕ in atTop,∀x : ShellSource F height,∀w : ℕ,
      2^height≤2*(x.sites*(st).copies) → w+1≤c*height →
      (privateMaskedClock (cells (st).radix) (cohort (st).radix) H (st).radix p+
        privateMaskedNames (cells (st).radix) (cohort (st).radix) (st).radix p)*
        (w+1)*T≤3213*c*(x.sites*d_) ∧
      (4+(H+1)*(26+234*(st).radix))*height*T≤x.sites*d_ :=by
  filter_upwards [NativeBranch.terminal_mask_setup G op drift t f g reset sr ar τ B 0 c
    branch maskReserve bought chart cpu,
    stage_open_split_counts G t f g reset τ L₀ wr B (by omega) packing] with height masks counts
  intro x w support arch
  let J:=age_ height
  obtain ⟨_,_,q₀Fit,Wpos,Wfit,Upos,qFit,_⟩:=native_socket_scale G t J f g reset x.sites τ
  have qPos : 0<q:=Nat.mul_pos (Nat.two_pow_pos _) Upos
  obtain ⟨_,pPos,socketSize,low,high,_,_⟩:=counts x.sites (2^kbits) W (Nat.two_pow_pos _) Wpos q₀Fit Wfit
  have qHeight : q≤height:=by
    have lhs : q≤q*p:=Nat.le_mul_of_pos_right _ pPos
    rw [←socketSize] at lhs
    omega
  have grain : p≤ s_ :=by
    change p≤((st).grainAt G.b p 0)*G.b
    rw [(st).grain_initial]
    have paid : 0<G.b:=by have:=G.paid;omega
    exact (Nat.le_mul_of_pos_right _ (pow_pos paid _)).trans (Nat.le_mul_of_pos_right _ paid)
  have cap : x.sites≤2^(2*height):=by simpa [pow_mul,Nat.mul_comm] using x.upper
  have aperture : q*W≤ DescentCompiler.TerminalScale.scale J ar:=(Nat.mul_le_mul qFit Wfit).trans (scale_mul ..).le
  have rawMask:=(masks x.sites 0 q W q cap support qPos Wpos qFit aperture qHeight (Nat.zero_le _)).2.2.2
  have bound:=Nat.mul_le_mul_right T (Nat.mul_le_mul_left
    (privateMaskedClock (cells (st).radix) (cohort (st).radix) H (st).radix p+
      privateMaskedNames (cells (st).radix) (cohort (st).radix) (st).radix p) arch)
  constructor
  · apply bound.trans (rawMask.trans ?_)
    apply Nat.mul_le_mul_left
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (x.sites*(st).copies) grain
  · have stored : 0<H:=calibrated_hosts_positive G t J f g reset x.sites τ (by have:=x.opened;omega)
    have radix : (st).radix≤ DescentCompiler.TerminalScale.scale J κ:=Nat.pow_le_pow_right (by decide : 0<2)
      (groupBits_linear t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    have fixed : 524≤ DescentCompiler.TerminalScale.scale J 10:=by
      have digits : 524≤2^10:=by decide
      exact digits.trans (Nat.pow_le_pow_right (by decide) (show 10≤10*(J+1) from Nat.le_mul_of_pos_right _ (Nat.succ_pos J)))
    have factors : 524*(st).radix≤ DescentCompiler.TerminalScale.scale J (κ+10):=by
      rw [←scale_mul]
      simpa only [Nat.mul_comm 524] using Nat.mul_le_mul radix fixed
    have summed:=(host_sweep stored (Nat.two_pow_pos _)).trans (Nat.mul_le_mul_left H factors)
    exact (Nat.mul_le_mul_right T (Nat.mul_le_mul_right height summed)).trans
      (preflight_host_units G t J f g reset x.sites τ height s_ (κ+10) tailReserve high)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
