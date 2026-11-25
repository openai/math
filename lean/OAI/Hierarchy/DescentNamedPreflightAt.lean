import OAI.Hierarchy.DescentNamedPreflightCalendar
import OAI.Hierarchy.DescentNamedLeafCalibration

namespace OAI
/-! # Height and scan invoice for one fixed executable preprocessing layout on the true chosen leaf -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch DescentKernelHistory
open scoped Classical
noncomputable section
set_option quotPrecheck false
section
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)

open DescentTerminalPreflightSpace

variable {tail : ℕ} (baseGroups : S.baseGroups = 2^tail) (boundary : ℕ) (op : RotorSpec)
    (headerRows paidRows : ℕ)
local notation "chosenFormat" => geometryFormat G S k g p tail boundary R op headerRows paidRows
local notation "chosenSpec" => preflightSpec X G S k g p tail chosenFormat

include b hp baseGroups in
private theorem geometry_room_of_measures (height rate : ℕ)
    (keys : (chosenSpec).registerBits ≤ height) (scan : (chosenSpec).scanScale ≤ rate) :
    (chosenSpec).ScalarRoom height rate (paidRows+headerRows) := by
  have population := preflight_population X G S (k:=k) (n:=n) (h:=h) (C:=C)
    (f:=f) (g:=g) (p:=p) (R:=R) (he:=he) (hu:=hu) (radix:=radix)
    (r:=r) (c:=c) (tail:=tail) b hp baseGroups chosenFormat
  exact (chosenSpec).calibrated height rate (paidRows+headerRows) keys scan le_rfl
    (geometry_positive G S X k g p tail boundary R op headerRows paidRows)
    (preflight_strips X G S (k:=k) (g:=g) (p:=p) (tail:=tail) chosenFormat)
    population

end

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
theorem stage_preflight :
    (issuedSpec).registerBits≤height ∧ (issuedSpec).scanScale≤ scale age invoice ∧
      (issuedSpec).maskBase origin≤origin+512*(2^(height/2)+(S).hostSize (S).length*scale age invoice+
        (paidRows+headerRows)+1) := by
  exact original_preflight X G S («k»:=k) (n:=n) (h:=D) (C:=C) (f:=f) (g:=g)
    (p:=p) (R:=drift) (he:=he) (hu:=hu) (radix:=radix) (r:=r) (c:=c) (tail:=tailBits)
    b hp rfl Q op headerRows paidRows τ κ 1 B height σ ε₀
    date.positive hb rfl grain (groupBits_linear ..) rfl date.frozen date.late
    (date.scalar sites p grain) (date.payer sites) paid date.room origin

include b hp grain hb paid date in
/-- This is the exact finite input of the allocator cost and native clock/names invoice.
All room conditions, including both original cohort populations, follow from the
single earlier calibrated date and the selected original reached history. -/
theorem stage_room :
    (issuedSpec).ScalarRoom height (scale age invoice) (paidRows+headerRows) := by
  have fit:=stage_preflight X G op t f g reset τ B height sites drift p (n:=n) (D:=D) (C:=C)
    (he:=he) (hu:=hu) (radix:=radix) (r:=r) (c:=c) b hp grain hb paid date headerRows paidRows 0
  exact geometry_room_of_measures X G S («k»:=k) (n:=n) (h:=D) (C:=C) (f:=f) (g:=g)
    (p:=p) (R:=drift) (he:=he) (hu:=hu) (radix:=radix) (r:=r) (c:=c) (tail:=tailBits)
    b hp rfl Q op headerRows paidRows height (scale age invoice) fit.1 fit.2.1
end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
