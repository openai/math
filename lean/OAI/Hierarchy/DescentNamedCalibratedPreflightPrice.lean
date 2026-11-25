import OAI.Hierarchy.DescentNamedPreflightOpenInvoice
import OAI.Hierarchy.DescentFixedReplayOpenInvoice
import OAI.Hierarchy.DescentTerminalFixedSlices
import OAI.Hierarchy.DescentNamedPreflightMachine

namespace OAI
/-! # The six original dated sheets precede frozen replay and the purchased terminal preflight -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch DescentKernelHistory
open DescentTerminalGraphVolume DescentTerminalCompiledPrefix.AddressPlan
open ProtocolRAM DescentSIMDLookup DescentTerminalCombinedRole DescentTerminalPointerDigits DescentTerminalLocalPortBook
open DescentTerminalPreflightSpace DescentStaticWordColumn ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
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



variable (outside slots bundle bins homes₀ factor rate blocks₀ : ℕ)
local notation "j_" => Nat.clog 2 (NativeBranch.localLimit G S)
local notation "T" => 2^age
local notation "d" => (S).copies*s
local notation "fund" => d*(sites+T*outside)
local notation "rawCount" => integralFrontier T sites d outside rate
local notation "pool" => bought (rowBudget bundle slots bins rawCount (d*outside) homes₀ 3) bins
local notation "ρ" => 6*(32*factor)*(3+4*rate)+2*factor
local notation "α" => 1+operandExponent G (stageNumbers G t 0 f g reset 0 0)
local notation "sliceRate" => α+κ+4
variable (phase : DescentTerminalFixedSlices.Phase F) (first w : ℕ)
variable (cal : DescentTerminalFixedReplay.Calendar k)
local notation "base" => phase.stop first
local notation "romBase" => cal.packetEnd base
local notation "censusAt" => ((x).scanPages romBase Q).stop
local notation "homes" => cal.homes base
local notation "L₀" => phase.output
variable (cohortRoom : cal.stop censusAt<2^w)
local notation "replay" => cal.program base censusAt cohortRoom
local notation "replayCost" => cal.cost base censusAt cohortRoom
variable (peer : Bank) (paidOld actor : Fin (x).scalar.blocks→Bank)
    (signed : Fin (x).scalar.blocks→Fin (2*(x).cap)→Bank) (matrix roleBase : ℕ)
    {ap : ℕ} (ptr : Fin 4→Fin ap→Fin (x).scalar.blocks→Bank)
    (baseGroups : (S).baseGroups=2^tailBits)
local notation "machine" => fixedPreflight X G S baseGroups radix g p Q drift op headerRows paidRows origin romBase
  w peer homes paidOld actor signed matrix roleBase (phase.banks first) ptr
local notation "clock_" => fixedPreflightClocks X G S («k»:=k) (tail:=tailBits) g p Q drift op headerRows paidRows
  origin romBase peer homes paidOld actor signed matrix ptr

set_option maxRecDepth 3500 in
set_option maxHeartbeats 800000 in
include b hp grain hb paid date in
theorem calibrated_preflight_prefix (sitesPos : 0< sites)
    (reserve : localSocketRate G t g+max invoice sliceRate≤τ)
    (large : 10≤height) (support : 2^height≤2*(sites*(S).copies)) (width : T≤ s)
    (arch : w+1≤factor*height) (packHead : height≤32*((2^j_)*s)) (packEnd : height≤32*(slots*bundle))
    (binPos : 0<bins) (binTable : bins≤2^(height/2)) (positions : (4+(homes₀+1)*(26+234*blocks₀))*height*T≤ sites*d)
    (headerCount : headerRows≤pool+(rawCount/(slots*bundle)+1)) (paidCount : paidRows≤pool)
    (late : drift+1≤ scale age 1) (measured : phase.Paid height (scale age sliceRate))
    (ended : (L₀).metadataEnd phase.dateBase≤first) (space : phase.stop first<2^w)
    (homesEq : (L₀).receiver.hosts=(S).hostSize (S).length) (active : 0<(L₀).receiver.hosts)
    (lanes : (L₀).argumentSlots≤(S).retainedArgumentsAt G drift) (blocks : (L₀).receiver.blocks≤2^k)
    (flight : FlightInvoice T fund ((128000+262144)*factor) replay replayCost)
    (front back : Procedure w) (rest prior : ℕ)
    (before : (rest+7*names (front.seq back))*(w+1)*T≤prior*fund) :
    (rest+phase.cost first+replayCost+clock_+7*names ((((front.seq (phase.program first w)).seq replay).seq machine).seq back))*
      (w+1)*T≤(prior+7*16384*(2*factor)+(128000+262144)*factor+7*24200200*(2*factor+6*ρ))*fund := by
  have phaseBill:=phase.open_price G t age f g reset sites τ drift s height w outside factor first measured ended space
    homesEq active lanes blocks late ((Nat.add_le_add_left (le_max_right invoice sliceRate) _).trans reserve)
    large support width arch packHead front back rest prior before
  have replayBill:=flight (front.seq (phase.program first w)) back (rest+phase.cost first)
    (prior+7*16384*(2*factor)) phaseBill
  apply mounted_preflight_open_price X G op t f g reset τ B height sites drift p
    (n:=n) (D:=D) (C:=C) (he:=he) (hu:=hu) (radix:=radix) (r:=r) (c:=c) b hp grain hb paid date
    headerRows paidRows origin peer signed sitesPos w _ _ _ _ paidOld actor _ _ _ _ _ _
    romBase homes _ outside slots bundle bins homes₀ factor rate blocks₀
    ((Nat.add_le_add_left (le_max_left invoice sliceRate) _).trans reserve) large support width arch packHead packEnd
    binPos binTable positions headerCount paidCount _ back _ _ replayBill

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
