import OAI.Hierarchy.TaggedWideOriginalCalendarPrice
import OAI.Hierarchy.TaggedWideCalendarExit
import OAI.Hierarchy.TaggedWideWindowWidthCap

namespace OAI
/-! # One fixed terminal aperture for all funded purchases and all selectors -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 700000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage CoreBoard HistoryRoles ReportSockets Tagged TaggedShorterBudget TaggedPrune
open Tagged.WideStack WireTelescope AdaptiveProbe
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ)

/-- The original last-count bound must fit the displayed positive port as well
as both private ports. Allocate that many view coordinates before selecting any
parent, selector, near/far price, or purchase. -/
def calendarUnit := v.sharpPaidUnit+v.widePrivateUnit v.sharpPaidUnit+1

theorem calendarUnit_rate : v.sharpPaidUnit≤v.calendarUnit := by unfold calendarUnit;omega

theorem calendarUnit_view : v.widePrivateUnit v.sharpPaidUnit≤v.wideHistoryUnit v.calendarUnit := by
  have clk:0<HistoryRoles.clock v.mesh:=by
    unfold HistoryRoles.clock
    have started:=v.clock.inject_pos
    positivity
  have enough : v.calendarUnit≤HistoryRoles.clock v.mesh*v.calendarUnit := Nat.le_mul_of_pos_left _ clk
  unfold wideHistoryUnit
  have left : v.widePrivateUnit v.sharpPaidUnit≤v.calendarUnit:=by unfold calendarUnit;omega
  omega

def calendarLaneExponent := v.wideInstalledCap v.calendarUnit
theorem calendar_lanes : v.wideInstalledCap v.calendarUnit≤2^v.calendarLaneExponent :=
  (Nat.lt_two_pow_self (n:=v.calendarLaneExponent)).le

/-- Old role apertures use the final time block. Positive and private reported
outputs use their respective physical banks in `parentShared`. -/
def calendarTerminalWidth := v.wideHistoryUnit v.calendarUnit+1

theorem calendarTerminalWidth_pos : 0<v.calendarTerminalWidth := Nat.succ_pos _

variable (x:WideParent κ A) (m ell short:ℕ)
local notation "unit" => v.calendarUnit
local notation "view" => v.wideHistoryUnit unit*x.w
local notation "days" => events v.mesh
local notation "D" => v.parentShared x m ell short unit ((days).length+1)
local notation "sites" => Fin (siteLast x.h (2^v.W) k+1)
local notation "stage" => typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)
local notation "catalog" => (v.widePlacement x.h x.w).catalogue
local notation "order" => v.wideOrder x.h x.w
local notation "dir" => WideMemory.dir x.h v.W k v.wideJobs
local notation "priv" => fun _:(catalog).Private order=>v.widePrivateUnit unit*x.w
local notation "book" => HistoryRoles.ceiling v.sampler (h:=x.h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh unit v.keepLimit (CatalystArchive.fuel v.mesh) x.w
local notation "pack" => fun t:Fin (m+1)=>⌈dyadic ((stage).index t).2*x.w⌉₊
local notation "lens" => TurnShelf.Aperture (TurnShelf.exponent v.wideShelfRoles)
  (TurnShelf.exponent (v.calendarTerminalWidth*x.w))

def calendarTerminalPins (i:sites) : lens→D⊕Bool :=
  Terminal.outputAperture (lanes:=2^ell) («view»:=view) v.sampler dir days catalog order priv book pack
    ((siteNumber x.h (2^v.W) k).symm i) (fun r out=>v.wide_shelf_role_fit x.h r.val out)

theorem calendar_terminal_pins (s:Site x.h (2^v.W) k) :
    v.calendarTerminalPins x m ell short (siteNumber x.h (2^v.W) k s)=
      Terminal.outputAperture (lanes:=2^ell) («view»:=view) v.sampler dir days catalog order priv book pack
        s (fun r out=>v.wide_shelf_role_fit x.h r.val out) := by
  let apertureAt (t : Site x.h (2^v.W) k) : lens→D⊕Bool :=
    Terminal.outputAperture (lanes:=2^ell) («view»:=view) v.sampler dir days catalog order priv book pack
      t (fun r out=>v.wide_shelf_role_fit x.h r.val out)
  exact congrArg apertureAt ((siteNumber x.h (2^v.W) k).symm_apply_apply s)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
