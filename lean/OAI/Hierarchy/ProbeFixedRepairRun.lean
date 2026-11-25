import OAI.Hierarchy.ProbeFixedRepairSlot
import OAI.Hierarchy.ProtocolRAMCalendarVerdict

namespace OAI
/-! # Dated physical repair receipts from one authenticated and accepted calendar run -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart PurchaseStage StockCommit
open StripDirectory
open scoped Classical

/-- Acceptance at an arbitrary current event follows from acceptance of the
ordered execution, with exactly the memory produced by its original prefix. -/
theorem Slot.accepted_at {w q d : ℕ} {C : Chart w q d} {init entry : Memory w} {e : Event}
    {prior tail : List Event} (cut : Slot C init e prior tail entry)
    (valid : admissible C (Calendar.events C.mesh) init) : accepted C e entry := by
  have rest (xs : List Event) (m : Memory w) : admissible C (xs++e::tail) m →
      admissible C (e::tail) (run C xs m) := by
    induction xs generalizing m with
    | nil => exact id
    | cons x xs ih => exact fun ok=>ih _ ok.2
  rw [cut.events] at valid
  have atCut:=(rest prior init valid).1
  rwa [cut.entry] at atCut

namespace FixedProtocolFormat
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

/-- Dimension sufficient for all repair, menu letter, and charged-word bounds.
The coefficient includes both previously retained stock and all new copies. -/
def repairHeight : ℕ := max v.stripHeight (max ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊
  (max v.menu.alphabet (v.keepLimit+v.menu.maximum+1)))

theorem repair_numeric {z width : ℕ} (height : v.repairHeight≤z) (payload : width≤2^z) :
    let w:=wordBits z (2^v.W) copies
    v.stripHeight≤z ∧ ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^w ∧ v.menu.alphabet<2^w ∧
      v.keepLimit*width+v.menu.maximum*v.menu.copiesAt v.copyScale width<2^w := by
  intro w
  have cut : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊≤z:= (le_max_left ..).trans ((le_max_right ..).trans height)
  have alpha : v.menu.alphabet≤z:= (le_max_left ..).trans ((le_max_right ..).trans ((le_max_right ..).trans height))
  have coeff : v.keepLimit+v.menu.maximum+1≤z:= (le_max_right ..).trans ((le_max_right ..).trans ((le_max_right ..).trans height))
  have power : z<2^z:=Nat.lt_two_pow_self (n:=z)
  have high : z<2^w:=power.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [w];rw [wordBits_linear]; omega))
  have copies : v.menu.copiesAt v.copyScale width≤width:=Nat.div_le_self ..
  have sum : v.keepLimit*width+v.menu.maximum*v.menu.copiesAt v.copyScale width≤(v.keepLimit+v.menu.maximum)*2^z := by
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ payload) (Nat.mul_le_mul_left _ (copies.trans payload))
  have word:=append_room (h:=z) (d:=2^v.W) (copies:=Native.copies) (K:=v.keepLimit+v.menu.maximum) (coeff.trans power.le)
  exact ⟨(le_max_left ..).trans height,cut.trans_lt high,alpha.trans_lt high,
    sum.trans_lt ((Nat.le_add_left ..).trans_lt word)⟩

variable (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "H" => v.publicHeader P z width
local notation "G" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "FEE" => StripChart.charges F (v.sized (v.seed P z width) width) v.cost (H).stop
local notation "g" => v.stamp P z width r banks src tab dst owners

/-- All scalar word bounds and local validity come from the same actual
admitted execution. The only table readings are the immutable original ROMs. -/
def RepairSlot.ofWords (mem : Memory W)
    (run : StockBound.Run C (v.stockBanks P z width) mem z N k (v.keepLimit*width))
    (admitted : admissible C (events v.mesh) mem) («public» : (H).Resident mem)
    (prices : InitialPrices P.joint z N k (DeadlineROM.prices v.mesh v.finish (v.basePhase width)) (fun _=>0) mem)
    (fees : (FEE).Resident mem) (budget : P.joint.cap*P.joint.width=v.keepLimit*width)
    (late : v.stripHeight≤z) (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W)
    (letterFit : v.menu.alphabet<2^W)
    (rateRoom : v.keepLimit*width+v.menu.maximum*v.menu.copiesAt v.copyScale width<2^W) (large : v.widthFloor≤width)
    (a : Attempt) (prior tail : List Event) (entry : Memory W) (cut : Slot C mem (.attempt a) prior tail entry)
    (layout : StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width ((G).base v.mesh (.attempt a)))
    (failed : AttemptGate.actual (repair C a).policy
      (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))=2) :
    v.RepairSlot P z width r banks src tab dst owners a entry := by
  exact ⟨mem,prior,tail,cut,«public»,fun _=>0,prices,fees,run,budget.ge,layout,cut.accepted_at admitted,failed,
    large,v.clock.inject_pos.trans_le (v.clock.inject_width.trans large),late,threshold,letterFit,rateRoom⟩

/-- All scalar word bounds and local validity come from the same actual
admitted execution. The only table readings are the immutable original ROMs. -/
def RepairSlot.ofRun (mem : Memory W)
    (run : StockBound.Run C (v.stockBanks P z width) mem z N k (v.keepLimit*width))
    (admitted : admissible C (events v.mesh) mem) («public» : (H).Resident mem)
    (prices : InitialPrices P.joint z N k (DeadlineROM.prices v.mesh v.finish (v.basePhase width)) (fun _=>0) mem)
    (fees : (FEE).Resident mem) (budget : P.joint.cap*P.joint.width=v.keepLimit*width)
    (height : v.repairHeight≤z) (large : v.widthFloor≤width) (payload : width≤2^z)
    (a : Attempt) (prior tail : List Event) (entry : Memory W) (cut : Slot C mem (.attempt a) prior tail entry)
    (layout : StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width ((G).base v.mesh (.attempt a)))
    (failed : AttemptGate.actual (repair C a).policy
      (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))=2) :
    v.RepairSlot P z width r banks src tab dst owners a entry := by
  have bound:=v.repair_numeric height payload
  exact RepairSlot.ofWords v P z width r banks src tab dst owners mem run admitted «public» prices fees budget
    bound.1 bound.2.1 bound.2.2.1 bound.2.2.2 large a prior tail entry cut layout failed

end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
