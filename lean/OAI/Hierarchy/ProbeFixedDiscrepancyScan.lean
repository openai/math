import OAI.Hierarchy.ProbeDiscrepancyScanArithmetic
import OAI.Hierarchy.ProbeFixedFailureCeilings
import OAI.Hierarchy.ProbeFixedMarketRows

namespace OAI
/-! # Word room for the native deposited-failure scan before the current attempt -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit StripDirectory PurchaseCT
open scoped Classical Fin.CommRing BigOperators
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "wall" => wallCap v.radius (upperBox (publicStages v.W) v.radius)
local notation "rowFactor" => StripChart.treeRowsFactor (2^v.W) k v.sampler.degree v.depth

/-- All padded paths, score words, and the guard threshold have coefficients
independent of the height, phase, and stock at the current event. -/
def discrepancyScanHeight :=
  max v.stripHeight (max (rowFactor*⌈wall*(v.precision:ℝ)⌉₊) ⌈4*v.toleranceAt*(v.precision:ℝ)⌉₊+1)

variable (P : v.Placement) (z width : ℕ)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local notation "fm" => v.nativeFormats P z width
local notation "bs" => v.nativeBoards P z width

private theorem scan_product_room (height : v.discrepancyScanHeight≤z) (K : ℕ)
    (small : K ≤ max (rowFactor*⌈wall*(v.precision:ℝ)⌉₊) ⌈4*v.toleranceAt*(v.precision:ℝ)⌉₊) :
    K*2^z<2^W := by
  have bound : K+1≤z :=
    (Nat.succ_le_succ small).trans ((le_max_right ..).trans height)
  have room := append_room (h:=z) (d:=2^v.W) (copies:=copies) (K:=K) (bound.trans (Nat.lt_two_pow_self (n:=z)).le)
  exact (Nat.le_add_left ..).trans_lt room

/-- The entire real sum fits, even when every allocated padded path has a
nonzero test word. The source can be any immutable snapshot of the market. -/
theorem discrepancy_scan_sum (height : v.discrepancyScanHeight≤z) (a : Attempt) (m : Memory W)
    (pointwise : ∀i,((fm a).market.failures.value m i:ℝ)/v.precision≤wall) :
    (∑i,(fm a).market.failures.value m i)<2^W := by
  let K:=⌈wall*(v.precision:ℝ)⌉₊
  have room:=v.scan_product_room z height (rowFactor*K) (le_max_left ..)
  calc
    (∑i,(fm a).market.failures.value m i)≤(fm a).market.failures.rows*K :=
      deposited_sum_le _ _ wall v.clock.precision_pos pointwise
    _=(rowFactor*K)*2^z := by rw [v.discrepancy_scan_rows P z width a];ac_rfl
    _<2^W := room

theorem discrepancy_scan_threshold (height : v.discrepancyScanHeight≤z) (a : Attempt) :
    (fm a).market.failures.globalBound<2^W := by
  let k₀:=⌈4*v.toleranceAt*(v.precision:ℝ)⌉₊
  have raw : (fm a).market.failures.globalBound=⌈4*v.toleranceAt*(2^z:ℕ)*(v.precision:ℝ)⌉₊ := by cases a <;> rfl
  rw [raw]
  exact (ceiled_score_le (4*v.toleranceAt) (2^z) v.precision).trans_lt
    (v.scan_product_room z height k₀ (le_max_right ..))

/-- The single eventual height works for every allocation, payload width, and
event on the same fixed protocol. -/
theorem discrepancy_scan_eventually :
    ∀ᶠ h : ℕ in Filter.atTop, ∀(P' : v.Placement) (w : ℕ) (a : Attempt),
      let b:=wordBits h (2^v.W) copies
      let fail:=(v.nativeFormats P' h w a).market.failures
      fail.globalBound<2^b ∧ ∀m : Memory b,(∀i,(fail.value m i:ℝ)/v.precision≤wall) →
        (∑i,fail.value m i)<2^b := by
  filter_upwards [Filter.eventually_ge_atTop v.discrepancyScanHeight] with h large
  intro P' w a
  exact ⟨v.discrepancy_scan_threshold P' h w large a,fun m=>v.discrepancy_scan_sum P' h w large a m⟩

variable (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "H" => v.publicHeader P z width
local notation "g₀" => JointHeader.scores P.joint z N k
local notation "pg[" a "]" => DeadlineROM.scorePage v.mesh g₀ z N k a
local notation "price[" a "]" => (DeadlineROM.prices v.mesh v.finish (v.basePhase width) (DeadlineROM.index v.mesh a))
local notation "raw[" a "," m "]" => ((guard C a).apply m)

section
variable (phase trial : ℕ)
local notation "ev" => Attempt.outer phase trial

theorem payload_discrepancy_scan (entry : Memory W) (date : dateInTable v.mesh ev)
    (positive : 0<time v.mesh v.finish ev) (height : v.discrepancyScanHeight≤z)
    (header : (H).Resident raw[ev,entry]) (scores : GlobalTests.Resident pg[ev] z N k price[ev] raw[ev,entry])
    (limit : ∀i,(entry ((A).stockAt ev i)).val<(g₀).stride) :
    (∑i,(fm ev).market.failures.value raw[ev,entry] i)<2^W :=
  v.discrepancy_scan_sum P z width height ev _ (v.payload_guard_failure_ceiling P z width r banks src tab dst owners
    phase trial entry date positive ((le_max_left ..).trans height) header scores limit)
end

section
variable (phase trial slice inner : ℕ)
local notation "ev" => Attempt.inner phase trial slice inner
local notation "sh" => ((bs).outer phase trial).market.shelf
local notation "S" => (bs).sampler
local notation "h₀" => stratumHeader z (2^v.W) k (S).degree v.depth ((bs).stratumHeader phase trial)

theorem purchased_discrepancy_scan (entry : Memory W) (date : dateInTable v.mesh ev)
    (positive : 0<time v.mesh v.finish ev) (height : v.discrepancyScanHeight≤z)
    (header : (H).Resident raw[ev,entry]) (scores : GlobalTests.Resident pg[ev] z N k price[ev] raw[ev,entry])
    (limit : ∀t,(entry ((A).stockAt ev t)).val<(g₀).stride) (π : Equiv.Perm (Fin (2^z)))
    (head : (h₀).Loaded raw[ev,entry])
    (paths : ∀key : PurchaseFrozen.Key z (2^v.W) k,ProtocolRAMPurchaseGateColumns.TileRows
      ((sh).L S v.depth key).source (PurchaseFrozen.Shelf.pathRows S π v.depth key) raw[ev,entry])
    (certify : ∀ j : Fin (fm ev).market.rows, (fm ev).market.failures.live.eval raw[ev,entry] (j.val:Word W) ≠ 0 →
      v.PurchasedLiveRow P z width phase trial slice inner π j) :
    (∑i,(fm ev).market.failures.value raw[ev,entry] i)<2^W :=
  v.discrepancy_scan_sum P z width height ev _ (v.purchased_guard_failure_ceiling P z width r banks src tab dst owners
    phase trial slice inner entry date positive ((le_max_left ..).trans height) header scores limit π head paths certify)
end

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
