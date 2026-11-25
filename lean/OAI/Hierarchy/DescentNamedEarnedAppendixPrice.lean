import OAI.Hierarchy.DescentNamedEarnedShellChipPrice
import OAI.Hierarchy.DescentTerminalChipBootExtent
import OAI.Hierarchy.DescentTerminalOriginalInvoice

namespace OAI
/-! # The original sixteen paid terminal columns and physical open-port appendix -/
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
local notation "κ" => groupRate G t f g reset
local notation "L₀" => localSocketRate G t g
local notation "uRate" => Nat.clog 2 G.b*(t+1)
local notation "sr" => L₀+uRate
local notation "wr" => τ+κ+4
local notation "ar" => sr+wr



local notation "codes_" => DescentTerminalScalarHeader.range q (fmt).roles (fmt).privateWords
  (fmt).nodes (fmt).addresses p V

/-- The four summands are the authenticated chip, dense header, paid rows and open-port rows. -/
private theorem original_appendix_words (chipBlocks laneCount quotaSize pieceSize codeCount rowCount publicCount heightValue : ℕ)
    (dense : DescentTerminalDenseWindow.formatBits quotaSize (laneCount*pieceSize)+2*(quotaSize*(laneCount*pieceSize))≤heightValue/2)
    (route : DescentTerminalBinFormat.controlBits laneCount quotaSize+DescentTerminalBinReaddress.sliceWidth laneCount quotaSize pieceSize≤heightValue/2)
    (alphabet : codeCount+1≤2^(heightValue/2)) :
    DescentTerminalPublicIdentity.total chipBlocks laneCount quotaSize pieceSize codeCount rowCount publicCount≤
      8*(chipBlocks*laneCount)+2*rowCount+2*publicCount+38*2^(heightValue/2) :=by
  have first:=DescentTerminalChipBootWords.room chipBlocks laneCount quotaSize pieceSize codeCount heightValue dense route alphabet
  have second:=DescentTerminalDenseHeaderBoot.extent_le dense
  have third:=DescentTerminalPaidBoot.total_le chipBlocks laneCount quotaSize pieceSize codeCount rowCount
  have fourth:=DescentTerminalPublicIdentity.total_le chipBlocks laneCount quotaSize pieceSize codeCount rowCount publicCount
  unfold DescentTerminalBoot.total at third
  have positive : 0<2^(heightValue/2):=Nat.two_pow_pos _
  omega

/-- The original predicate used at the input allocation of the named open host. -/
def EarnedShellAppendixAt (c height : ℕ) : Prop :=
  ∀(x : ShellSource F height) (L : TerminalPlacement) (w : ℕ),2^height≤2*(x.sites*(st).copies) →
    w+1≤c*height →
    DescentTerminalPublicIdentity.total bins W q piece codes_ (earnedShell G t f g reset τ B n depth C x L).terminal.plane.rawRows
      (earnedShell G t f g reset τ B n depth C x L).terminal.plane.publicRows*(w+1)*T≤(10*(coeff c)+102*c)*(d_*(x.sites+T*E))

theorem earned_shell_appendix_at (c : ℕ)
    (branch : G.b≤2^(capRate G t g)) (big : 20≤B) (socketRoom : 2*L₀≤τ)
    (packing : 2*(L₀+wr)+uRate≤B) (router : 2*(wr+sr+2)≤B)
    (maskReserve : 5+(hostRate t reset*(t+1)+1)+sr≤τ)
    (tailReserve : L₀+(κ+10)≤τ) (bought : 2*ar+1≤B)
    (chart : 2*(τ+κ+(6*(terminalDegree G t f g reset+1)+19))≤B)
    (cpu : max (NativeBranch.clockRate G t f g reset τ)
      (NativeBranch.privateMaskArenaRate G t f g reset τ 0)≤c) :
    ∀ᶠ height : ℕ in atTop,EarnedShellAppendixAt G t f g reset τ B n depth C op drift c height :=by
  filter_upwards [earned_shell_mask_sweep G t f g reset τ B op drift c branch big socketRoom packing
      maskReserve tailReserve bought chart cpu,
    terminal_format_calibration_full G op drift t f g reset τ B branch (by omega) chart router,
    early_native_packing G t f g reset τ B big socketRoom packing,
    stage_open_split_counts G t f g reset τ L₀ wr B (by omega) packing,
    eventually_ge_atTop 10] with height suites formats packed counts large
  intro x L w support arch
  let J:=age_ height
  let fund:=d_*(x.sites+T*E)
  obtain ⟨_,sweep⟩:=suites x w support arch
  obtain ⟨_,_,q₀Fit,Wpos,Wfit,Upos,_,_⟩:=native_socket_scale G t J f g reset x.sites τ
  obtain ⟨divides,pPos,identity,low,high,_,_⟩:=counts x.sites (2^kbits) W (Nat.two_pow_pos _) Wpos q₀Fit Wfit
  have qPos : 0<q:=Nat.mul_pos (Nat.two_pow_pos _) Upos
  have packet : height≤32*(q*p):=by simpa only [identity] using high
  have bits : W≤height/2:=by
    have a:=Nat.le_of_dvd pPos divides
    have b : p≤q*p:=Nat.le_mul_of_pos_left _ qPos
    rw [←identity] at b
    omega
  have popPos : 0<x.sites:=by have:=x.opened;omega
  have sites:=calibrated_hosts_positive G t J f g reset x.sites τ popPos
  have crop : raw≤rows:=earned_raw_rows_le_pool G t f g reset τ B n depth C x Wpos (Nat.mul_pos qPos pPos) sites
  have dates:=packed x.sites
  have timeWidth:T≤ s_:=dates.2.2.1
  have bounded:w+1≤(32*c)*(q*p):=calc
    _ ≤ c*height:=arch
    _ ≤ c*(32*(q*p)):=Nat.mul_le_mul_left _ packet
    _ = _:=by ring
  have paid:=covered_bank T x.sites (st).copies s_ E nfee p q W H height (w+1) (32*c) c (st).radix
    (bits.trans Nat.lt_two_pow_self.le) large support timeWidth bounded arch sweep
  have floor_:=Nat.div_mul_le_self (rowBudget p q W (integralFrontier T x.sites d_ E nfee) (d_*E) H 3) W
  have priced : rows*(w+1)*T≤(coeff c)*fund :=
    (Nat.mul_le_mul_right T (Nat.mul_le_mul_right (w+1) floor_)).trans paid
  have private_ : raw*(w+1)*T≤(coeff c)*fund :=
    (Nat.mul_le_mul_right T (Nat.mul_le_mul_right (w+1) crop)).trans priced
  have outside:=packet_bill (st).copies s_ E kbits rbits height (w+1) c dates.2.1 high arch
  have public_ : (pub_ height x)*(w+1)*T≤32*c*fund :=calc
    _ ≤ (32*c*d_*E)*T:=Nat.mul_le_mul_right T outside
    _ = (32*c)*(d_*(T*E)):=by ring
    _ ≤ _:=Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_add_left ..))
  have half : 2^(height/2)*(w+1)*T≤c*fund :=calc
    _ ≤ 2^(height/2)*(c*height)*T:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ arch)
    _ = c*((2^(height/2)*height)*T):=by ring
    _ ≤ c*((x.sites*(st).copies)*s_):=Nat.mul_le_mul_left _ (Nat.mul_le_mul (table_fund large support) timeWidth)
    _ = c*(d_*x.sites):=by ring
    _ ≤ _:=Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_add_right ..))
  obtain ⟨dense,route,alphabet,_⟩:=formats x.sites
  have size_:=original_appendix_words bins W q piece codes_ raw (pub_ height x) height dense route alphabet
  change DescentTerminalPublicIdentity.total bins W q piece codes_ raw (pub_ height x)*(w+1)*T≤_
  apply (Nat.mul_le_mul_right T (Nat.mul_le_mul_right (w+1) size_)).trans
  change (8*rows+2*raw+2*(pub_ height x)+38*2^(height/2))*(w+1)*T≤(10*(coeff c)+102*c)*fund
  simp only [Nat.add_mul,Nat.mul_assoc] at priced private_ public_ half ⊢
  omega

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
