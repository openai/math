import OAI.Hierarchy.DescentNamedPreflightBill
import OAI.Hierarchy.DescentTerminalFundedPreflight

namespace OAI
/-! # Charge the three mounted native scan tables in the named terminal bill -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch DescentKernelHistory
open ProtocolRAM DescentSIMDLookup DescentTerminalCombinedRole DescentTerminalPointerDigits DescentTerminalLocalPortBook
open DescentTerminalPreflightSpace DescentStaticWordColumn ThreeFlat.RAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
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
local notation "scheduleAt" G:arg t:arg f:arg g:arg reset:arg τ:arg B:arg height:arg sites:arg =>
  stageNumbers G t (Nat.log 2 height/(2*B)) f g reset sites (tail τ (Nat.log 2 height/(2*B)))
local notation "keyAt" G:arg t:arg f:arg g:arg reset:arg B:arg height:arg =>
  groupBits t (Nat.log 2 height/(2*B)) (hostRate t reset) (capRate G t g) (cutRate t f g)
variable {n D C : ℕ}
variable {he : 0 ≤ ((((scheduleAt G t f g reset τ B height sites).initialSites*(scheduleAt G t f g reset τ B height sites).copies : ℕ) : ℝ)/(scheduleAt G t f g reset τ B height sites).epochPower)}
  {hu : 0 ≤ (1 / (((scheduleAt G t f g reset τ B height sites).firstWidth G.b p : ℝ) * ((scheduleAt G t f g reset τ B height sites).epochPower : ℝ) ^ (scheduleAt G t f g reset τ B height sites).priceExponent)) *
    ((scheduleAt G t f g reset τ B height sites).epochPower : ℝ) ^ (scheduleAt G t f g reset τ B height sites).priceExponent} {radix : (scheduleAt G t f g reset τ B height sites).radix = 2^(keyAt G t f g reset B height)}
  {r : Epochs G hu he (h:=D) (C:=C) (Ht:=GroupStage.depthBound (atRound (scheduleAt G t f g reset τ B height sites).rounds) n f g)
    (t:=(scheduleAt G t f g reset τ B height sites).rounds) (scheduleAt G t f g reset τ B height sites).height
    (initial X (scheduleAt G t f g reset τ B height sites).copies ((scheduleAt G t f g reset τ B height sites).firstWidth G.b p) ((scheduleAt G t f g reset τ B height sites).groupCount 0) (keyAt G t f g reset B height) ((scheduleAt G t f g reset τ B height sites).initialDigits radix))}
  {c : (Epochs.finish G hu he r).Choice}
  (b : Branch X G (scheduleAt G t f g reset τ B height sites) (p:=p) (n:=n) (h:=D) (C:=C) (f:=f) (g:=g) radix drift r c)
  (hp:0<p) (grain:p≤height) (hb:0<B) (paid:2*(6*(PreflightCalendar.fieldExponent G t f g reset τ)+11)≤B)
  (date:PreflightCalendar.Ready G op t f g reset τ B drift height)
  (headerRows paidRows origin:ℕ)
local notation "L" => geometryFormat G S k g p tailBits Q drift op headerRows paidRows
local notation "issuedSpec" => preflightSpec X G S k g p tailBits L




include b hp grain hb paid date in
theorem mounted_preflight (peer:Bank) (old:Fin (issuedSpec).scalar.blocks→Fin (2*(issuedSpec).cap)→Bank)
    (sitesPos:0<sites)
    (w nd nodes hidden args:ℕ) (oldPaid actor:Fin (issuedSpec).scalar.blocks→Bank)
    (first second:Shelf) (chart:Fin (issuedSpec).scalar.columns→Fin (issuedSpec).scalar.blocks→Gather.Address)
    {out0 out7:ℕ} (f0:(Fin (issuedSpec).scalar.columns→Cell (issuedSpec).scalar.pointerBits)→Cell out0)
    (f7:(Fin (issuedSpec).scalar.columns→Cell (issuedSpec).scalar.pointerBits)→Cell out7)
    (decode:(Fin (issuedSpec).strips→Cell (issuedSpec).printBits)→Directory 4 (issuedSpec).vertices (issuedSpec).arguments)
    (org:ℕ) (homes:Bank) (control:ℕ→ℕ) :
    let scan := (issuedSpec).scanPages org Q
    let program := (issuedSpec).purchasedProgram origin peer old w Q p nd nodes hidden args oldPaid actor
      first second chart f0 f7 decode scan.total scan.modulo homes scan.boundaries control
    let runTicks := (issuedSpec).purchasedClocks origin peer old Q p oldPaid actor chart scan.total scan.modulo homes scan.boundaries
    (names ((scan.program w).seq program)+(4+10*scan.words+runTicks))*(w+1) ≤
      24200200*((2^(height/2)+(S).hostSize (S).length*scale age invoice)*(w+1)+(paidRows+headerRows)*(w+1)) := by
  have room:=purchased_room X G op t f g reset τ B height sites drift p (n:=n) (D:=D) (C:=C) (he:=he) (hu:=hu) (radix:=radix) (r:=r) (c:=c) b hp grain hb paid date headerRows paidRows
    origin peer old sitesPos
  apply (issuedSpec).funded_preflight_price org Q origin peer old w p nd nodes hidden args oldPaid actor first second
    chart f0 f7 decode homes control height (scale age invoice) (paidRows+headerRows) room
  · change 0<sites*(2^_*2^_)^_
    positivity
  · exact Nat.two_pow_pos _
  · rfl

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
