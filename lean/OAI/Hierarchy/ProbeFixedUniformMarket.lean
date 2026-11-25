import OAI.Hierarchy.ProbeFixedUniformFailureExpr
import OAI.Hierarchy.ProbeFixedMarketRows
import OAI.Hierarchy.ProtocolRAMCalendarBill
import OAI.Hierarchy.ProtocolRAMCalendarHardware
import OAI.Hierarchy.ProbeFixedWideSettlement
import OAI.Hierarchy.ProbeFixedTerminalStock

namespace OAI
/-! # Fixed hardware and linear work of the complete original frozen market -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart
open PurchaseFrozen PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

def frozenTimeFactor : ℕ :=
  4+treeRowsFactor (2^v.W) k v.sampler.degree v.depth*(2*v.failureExprWork+4)+
    Shelf.timeFactor (2^v.W) v.sampler.degree v.depth k

def frozenTextBound : ℕ :=
  11+4*v.failureExprWork+Shelf.hardware (2^v.W) v.sampler.degree v.depth k

/-- Actual frozen prefix, including the first failure-expression scan and every
per-key executed CT and mark step. All stock, table and tape addresses are free. -/
theorem fixed_market_resources (P : v.Placement) (h width : ℕ) (a : Attempt) :
    let s:=(v.nativeFormats P h width a).atTime v.mesh v.finish (v.basePhase width) a
    s.prefix.ticks≤v.frozenTimeFactor*2^h ∧ ProbeStage.Native.text s.prefix.native≤v.frozenTextBound := by
  let s:=(v.nativeFormats P h width a).atTime v.mesh v.finish (v.basePhase width) a
  let rows:=treeRowsFactor (2^v.W) k v.sampler.degree v.depth
  have n : s.failures.rows≤2^h*rows := by
    rw [Nat.mul_comm]
    exact (v.discrepancy_scan_rows P h width a).le
  have sam : s.sampler=v.sampler := by cases a <;> rfl
  have depth : s.depth=v.depth := by cases a <;> rfl
  have work : s.failures.test.work≤v.failureExprWork := v.failure_expr_work P h width a
  have inner : 2*s.failures.test.work+4≤2*v.failureExprWork+4 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 2 work) 4
  have cutoff : marketFactor s rows≤v.frozenTimeFactor := by
    change 4+rows*(2*s.failures.test.work+4)+Shelf.timeFactor _ s.sampler.degree s.depth k≤_
    rw [sam,depth]
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left rows inner) 4) _
  constructor
  · calc s.prefix.ticks ≤ 2^h*marketFactor s rows := market_bill s rows Nat.one_le_two_pow n
         _ ≤ 2^h*v.frozenTimeFactor := Nat.mul_le_mul_left _ cutoff
         _ = _ := Nat.mul_comm ..
  · refine (text_market s).trans ?_
    rw [sam,depth]
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 4 work) 11) _

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
noncomputable section
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

/-- One absolute constant for this protocol controls every actual native ballot. -/
theorem wide_uniform_market :
    ∃ K : ℕ, ∀ h width : ℕ, ∀ a : Attempt, Event.attempt a∈events v.mesh →
      let P:=v.widePlacement h width
      let C:=v.wideSignedChart h width (v.fixedTerminalStock P h width)
      (C.frozen a).ticks≤K*2^h ∧ ProbeStage.Native.text (C.frozen a).native≤K := by
  refine ⟨max v.frozenTimeFactor v.frozenTextBound,?_⟩
  intro h width a _
  have exactCost := v.fixed_market_resources (v.widePlacement h width) h width a
  exact ⟨exactCost.1.trans (Nat.mul_le_mul_right _ (le_max_left ..)),exactCost.2.trans (le_max_right ..)⟩

end
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
