import OAI.Hierarchy.ProbeFixedScalarQuoteCells
import OAI.Hierarchy.ProbeFixedMenuWordCeiling
import OAI.Hierarchy.ProbeFixedAffirmativeRows
import OAI.Hierarchy.ProbeFixedPayloadPopulation
import OAI.Hierarchy.ProbeFixedRowTiles
import OAI.Hierarchy.ProbeFixedPurchasedArchiveRows

namespace OAI
/-! # The actual guarded failure word of every padded payload or replay row -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit StripDirectory PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local instance failureCeilingsPayloadRoleNonempty : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
local instance failureCeilingsPurchasedRoleNonempty : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
local notation "H" => v.publicHeader P z width
local notation "bs" => v.nativeBoards P z width
local notation "fm" => v.nativeFormats P z width
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "bills" => v.issued P z width r banks src tab dst owners
local notation "chart" => v.nativeChart P z width r banks src tab dst owners
local notation "g₀" => JointHeader.scores P.joint z N k
local notation "wall" => wallCap v.radius (upperBox (publicStages v.W) v.radius)
local notation "phaseRows" => DeadlineROM.prices v.mesh v.finish (v.basePhase width)
local notation "idx[" a "]" => DeadlineROM.index v.mesh a
local notation "pg[" a "]" => DeadlineROM.scorePage v.mesh g₀ z N k a
local notation "state[" a "," entry "]" => ((guard chart a).apply entry)

section
variable (phase trial : ℕ)
local notation "ev" => Attempt.outer phase trial

theorem payload_guard_failure_ceiling (entry : Memory W) (date : dateInTable v.mesh ev)
    (positive : 0<time v.mesh v.finish ev) (late : v.stripHeight≤z)
    (header : (H).Resident state[ev,entry])
    (scores : GlobalTests.Resident pg[ev] z N k (phaseRows idx[ev]) state[ev,entry])
    (limit : ∀ t, (entry ((A).stockAt ev t)).val<(g₀).stride)
    (i : Fin (fm ev).market.failures.rows) :
    ((fm ev).market.failures.value state[ev,entry] i:ℝ)/v.precision≤wall := by
  let m := state[ev,entry]
  let a := ev
  have coords := v.row_quote_cells P z width bills a entry m date header.scalar scores
    (v.purchased_table_room z late).2.2.2
    (v.guard_quote_stock P z width bills r banks src tab dst owners a entry) limit
  by_cases live : (fm ev).market.failures.live.eval m (i.val:Word W)=0
  · have none : (fm ev).market.failures.value m i=0 := by
      simp [FailureWords.value,FailureWords.effective,Expr.eval,ThreeFlat.RAM.DescriptorExpr.Comparison.test,live]
    change ((fm ev).market.failures.value m i:ℝ)/v.precision≤wall
    rw [none]
    simp only [Nat.cast_zero,zero_div]
    have box : 0 ≤ upperBox (publicStages v.W) v.radius := (Nat.cast_nonneg _).trans (le_max_left ..)
    unfold wallCap
    positivity
  · have original := v.payload_live_lt P z width phase trial m i
      (i.isLt.trans_le (v.market_rows_fit P z width late ev)) live
    let hits := PayloadStrip.rowAddress («N»:=N) (k:=k) (⟨i.val,original⟩ : Fin (2^z))
    let key := v.rowKey P z width bills a (time v.mesh v.finish a) positive entry hits
    have digits := v.payloadKey_read P z width r banks src tab dst owners phase trial
      entry (time v.mesh v.finish a) positive i original m coords
    exact v.payload_failure_ceiling_of_resident P z width phase trial m header i key digits
end

section
variable (phase trial slice inner : ℕ)
local notation "ev" => Attempt.inner phase trial slice inner
local notation "sh" => ((bs).outer phase trial).market.shelf
local notation "S" => (bs).sampler
local notation "h₀" => stratumHeader z (2^v.W) k (S).degree v.depth ((bs).stratumHeader phase trial)

/-- A disabled replay row contributes zero. An enabled row uses the stock slots of its retained path. -/
theorem purchased_guard_failure_ceiling (entry : Memory W) (date : dateInTable v.mesh ev)
    (positive : 0<time v.mesh v.finish ev) (late : v.stripHeight≤z)
    (header : (H).Resident state[ev,entry])
    (scores : GlobalTests.Resident pg[ev] z N k (phaseRows idx[ev]) state[ev,entry])
    (limit : ∀ t, (entry ((A).stockAt ev t)).val<(g₀).stride) (π : Equiv.Perm (Fin (2^z)))
    (head : (h₀).Loaded state[ev,entry])
    (paths : ∀ key : PurchaseFrozen.Key z (2^v.W) k, ProtocolRAMPurchaseGateColumns.TileRows
      ((sh).L S v.depth key).source (PurchaseFrozen.Shelf.pathRows S π v.depth key) state[ev,entry])
    (certify : ∀ j : Fin (fm ev).market.rows,
      (fm ev).market.failures.live.eval state[ev,entry] (j.val : Word W) ≠ 0 →
      v.PurchasedLiveRow P z width phase trial slice inner π j)
    (i : Fin (fm ev).market.failures.rows) :
    ((fm ev).market.failures.value state[ev,entry] i:ℝ)/v.precision≤wall := by
  let a := ev
  let m := state[ev,entry]
  by_cases asleep : (fm ev).market.failures.live.eval m (i.val : Word W) = 0
  · have zero : (fm ev).market.failures.value m i = 0 := by
      simp [FailureWords.value,FailureWords.effective,Expr.eval,
        ThreeFlat.RAM.DescriptorExpr.Comparison.test,asleep]
    change ((fm ev).market.failures.value m i : ℝ) / v.precision ≤ wall
    rw [zero]
    simp only [Nat.cast_zero,zero_div]
    have box : 0 ≤ upperBox (publicStages v.W) v.radius :=
      (Nat.cast_nonneg _).trans (le_max_left ..)
    unfold wallCap
    positivity
  · have sizes := v.purchased_table_room z late
    have coords := v.row_quote_cells P z width bills a entry m date header.scalar scores sizes.2.2.2
      (v.guard_quote_stock P z width bills r banks src tab dst owners a entry) limit
    obtain ⟨hits,_,first,_⟩ := v.purchased_raw_slots P z width phase trial slice inner π m m
      head head paths paths sizes.1 sizes.2.1 i (certify i asleep)
    let key := v.rowKey P z width bills a (time v.mesh v.finish a) positive entry hits
    have digits := v.purchasedKey_read P z width r banks src tab dst owners phase trial slice inner
      entry (time v.mesh v.finish a) positive i hits m coords first
    exact v.purchased_failure_ceiling_of_resident P z width phase trial slice inner m header i key digits
end

section
variable (phase trial slice inner : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.inner phase trial slice inner
local notation "pre" => (guard chart ev).apply entry
local notation "stage" => v.stage P z width r banks src tab dst owners ev entry
local notation "sh" => ((bs).outer phase trial).market.shelf
local notation "S" => (bs).sampler
local notation "h₀" => stratumHeader z (2^v.W) k (S).degree v.depth ((bs).stratumHeader phase trial)

set_option maxHeartbeats 1200000 in
/-- A nonzero guard flag has the same archived bit at the stage, where it identifies a real path. -/
theorem purchased_archive_live_rows (π : Equiv.Perm (Fin (2^z))) (late : v.stripHeight ≤ z)
    (archive : v.PurchasedArchiveRows P z width r banks src tab dst owners phase trial slice inner entry π)
    (j : Fin (fm ev).market.rows) (active : (fm ev).market.failures.live.eval pre (j.val : Word W) ≠ 0) :
    v.PurchasedLiveRow P z width phase trial slice inner π j := by
  have rows := v.purchased_raw_rows P z width phase trial slice inner
  let ordinal : Fin (h₀).count := ⟨j.val, rows ▸ j.isLt⟩
  have stageLive : (flagBank sh S z (2^v.W) k v.depth).read stage (ordinal.val : Word W) ≠ 0 := by
    rw [archive.flagRead ordinal]
    exact active
  exact v.purchased_live_row P z width phase trial slice inner π archive.stock archive.phase archive.heat
    archive.kind archive.frozen stage archive.stageFlags (v.purchased_table_room z late).2.2.1 j stageLive

end

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
