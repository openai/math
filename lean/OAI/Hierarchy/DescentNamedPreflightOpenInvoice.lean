import OAI.Hierarchy.DescentNamedFundedPreflight
import OAI.Hierarchy.DescentPreflightOpenPrice

namespace OAI
/-! # Charge the native, ROM-mounted terminal preflight at its chronological insertion point -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch DescentKernelHistory
open DescentTerminalGraphVolume DescentTerminalCompiledPrefix.AddressPlan
open ProtocolRAM DescentSIMDLookup DescentTerminalCombinedRole DescentTerminalPointerDigits DescentTerminalLocalPortBook
open DescentTerminalPreflightSpace DescentStaticWordColumn ThreeFlat.RAM
open ThreeFlat.RAM.PhysicalProcedure
open scoped Classical
noncomputable section
private theorem insert_preflight_charge {w : ℕ} (front middle back : Procedure w)
    (rest clock turns fund prior sections rate : ℕ)
    (before : (rest+7*names (front.seq back))*(w+1)*turns ≤ prior*fund)
    (native : (names middle+clock)*(w+1) ≤ 24200200*sections)
    (pages : sections*turns ≤ rate*fund) :
    (rest+clock+7*names ((front.seq middle).seq back))*(w+1)*turns ≤
      (prior+7*24200200*rate)*fund := by
  have weighted : (clock+7*names middle)*(w+1)*turns ≤ (7*24200200*rate)*fund := calc
    _ ≤ (7*(names middle+clock))*(w+1)*turns :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    _ = 7*((names middle+clock)*(w+1))*turns := by ring
    _ ≤ 7*(24200200*sections)*turns := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ native)
    _ = (7*24200200)*(sections*turns) := by ring
    _ ≤ (7*24200200)*(rate*fund) := Nat.mul_le_mul_left _ pages
    _ = _ := by ring
  simp only [names_seq] at before ⊢
  calc
    _ = (rest+7*(names front+names back))*(w+1)*turns+(clock+7*names middle)*(w+1)*turns := by ring
    _ ≤ _ := (Nat.add_le_add before weighted).trans_eq (by ring)

set_option quotPrecheck false
set_option hygiene false
variable {F:Type} [Field F] {cp P:ℕ} (X:Approximation F cp P) (G:PoweredGadget F) (op:RotorSpec)
  (t f g reset τ B height sites drift p:ℕ)
local notation "age" => Nat.log 2 height/(2*B)
local notation "tailBits" => tail τ age
local notation "S" => stageNumbers G t age f g reset sites tailBits
local notation "k" => groupBits t age (S).hostGain (S).capGain (cutRate t f g)
local notation "Q" => PreflightCalendar.publicSlots G S
local notation "κ" => groupRate G t f g reset
local notation "σ" => PreflightCalendar.palette G t f g reset
local notation "ε₀" => PreflightCalendar.publicBits G t g
local notation "σall" => PreflightCalendar.fieldExponent G t f g reset τ
local notation "invoice" => PreflightCalendar.scanExponent G t f g reset
local notation "wire" => (S).epochPower^(S).priceExponent
local notation "s" => (S).firstWidth G.b p
local notation "q_" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "ε" => ((((S).initialSites*(S).copies:ℕ):ℝ)/(S).epochPower)
local notation "u" => q_*(wire:ℝ)
variable {n D C:ℕ}
local notation "Ht" => GroupStage.depthBound (atRound (S).rounds) n f g
variable {he:0≤ε} {hu:0≤u} {radix:(S).radix=2^k}
  {r:Epochs G hu he (h:=D) (C:=C) («Ht»:=Ht) (t:=(S).rounds) (S).height
    (initial X (S).copies s ((S).groupCount 0) k ((S).initialDigits radix))}
  {c:(Epochs.finish G hu he r).Choice} (b:Branch X G S radix drift r c)
  (hp:0<p) (grain:p≤height) (hb:0<B) (paid:2*(6*σall+11)≤B)
  (date:PreflightCalendar.Ready G op t f g reset τ B drift height)
  (headerRows paidRows origin:ℕ)
local notation "L" => geometryFormat G S k g p tailBits Q drift op headerRows paidRows
local notation "x" => preflightSpec X G S k g p tailBits L


variable (peer:Bank) (old:Fin (x).scalar.blocks→Fin (2*(x).cap)→Bank)
    (sitesPos:0< sites)

variable (w nd nodes hidden args:ℕ) (oldPaid actor:Fin (x).scalar.blocks→Bank)
    (first second:Shelf) (chart:Fin (x).scalar.columns→Fin (x).scalar.blocks→Gather.Address)
    {out0 out7:ℕ} (f0:(Fin (x).scalar.columns→Cell (x).scalar.pointerBits)→Cell out0)
    (f7:(Fin (x).scalar.columns→Cell (x).scalar.pointerBits)→Cell out7)
    (decode:(Fin (x).strips→Cell (x).printBits)→Directory 4 (x).vertices (x).arguments)
    (org:ℕ) (homes:Bank) (control:ℕ→ℕ)
local notation "scan_" => (x).scanPages org Q
local notation "M" => (x).purchasedProgram origin peer old w Q p nd nodes hidden args oldPaid actor first second
  chart f0 f7 decode (scan_).total (scan_).modulo homes (scan_).boundaries control
local notation "ticks" => (x).purchasedClocks origin peer old Q p oldPaid actor chart (scan_).total (scan_).modulo homes (scan_).boundaries

local notation "eBits" => Nat.clog 2 (NativeBranch.localLimit G S)
local notation "T" => 2^age
variable (outside slots bundle bins homes₀ factor rate blocks₀ : ℕ)
local notation "pop" => (S).copies
local notation "d" => pop*s
local notation "F₀" => d*(sites+T*outside)
local notation "rows_" => integralFrontier T sites d outside rate
local notation "pool" => bought (rowBudget bundle slots bins rows_ (d*outside) homes₀ 3) bins
local notation "coefficient" => 6*(32*factor)*(3+4*rate)+2*factor
local notation "actual" => ((scan_).program w).seq M
local notation "clock_" => 4+10*(scan_).words+ticks

include b hp grain hb paid date sitesPos in
theorem mounted_preflight_open_price (reserve : localSocketRate G t g+invoice≤τ)
    (large : 10≤height) (support : 2^height≤2*(sites*pop)) (width : T≤ s)
    (arch : w+1≤factor*height) (packHead : height≤32*((2^eBits)*s))
    (packEnd : height≤32*(slots*bundle)) (binPos : 0<bins) (binTable : bins≤2^(height/2))
    (positions : (4+(homes₀+1)*(26+234*blocks₀))*height*T≤ sites*d)
    (headerCount : headerRows≤pool+(rows_/(slots*bundle)+1)) (paidCount : paidRows≤pool)
    (front back : Procedure w) (rest prior : ℕ)
    (previous : (rest+7*names (front.seq back))*(w+1)*T≤prior*F₀) :
    (rest+clock_+7*names ((front.seq actual).seq back))*(w+1)*T≤
      (prior+7*24200200*(2*factor+6*coefficient))*F₀ := by
  have paidNative:=mounted_preflight X G op t f g reset τ B height sites drift p (n:=n) (D:=D) (C:=C) (he:=he) (hu:=hu)
    (radix:=radix) (r:=r) (c:=c) b hp grain hb paid date
    headerRows paidRows origin peer old sitesPos w nd nodes hidden args oldPaid actor first second chart
    f0 f7 decode org homes control
  have frozen:=preflight_host_units G t age f g reset sites τ height s invoice reserve packHead
  have pages:=preflight_open_pages T sites pop s outside rate bundle slots bins homes₀ height w factor blocks₀
    ((S).hostSize (S).length) (scale age invoice) headerRows paidRows binPos binTable large support width arch
    packEnd positions frozen headerCount paidCount
  let sections:=(2^(height/2)+(S).hostSize (S).length*scale age invoice)*(w+1)+(paidRows+headerRows)*(w+1)
  change (names actual+clock_)*(w+1)≤24200200*sections at paidNative
  change sections*T≤(2*factor+6*coefficient)*F₀ at pages
  exact insert_preflight_charge front actual back rest clock_ T F₀ prior sections
    (2*factor+6*coefficient) previous paidNative pages

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
