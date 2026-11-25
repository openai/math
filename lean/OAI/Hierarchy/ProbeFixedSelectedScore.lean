import OAI.Hierarchy.ProbeFixedFailureEconomy
import OAI.Hierarchy.ProbeFixedCatalystMask
import OAI.Hierarchy.ProtocolRAMCalendarPricedBallot

namespace OAI
/-! # A paid selected row comes from the actual positive pre-guard score -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit PurchaseStage
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (z width : ℕ)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "st" => v.taskCommit P z width
local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "input" => v.stage P z width r banks src tab dst owners

theorem selected_high (a : Attempt) (entry : Memory W)
    (layout : StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width
      ((v.privateArena P z width).base v.mesh (.attempt a))) (run : ready C (.attempt a) entry)
    (π : PortPlan (st a) (b a) (input a entry) (f a).market.rows)
    (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W) (j : Fin (f a).market.rows)
    (keep : j∈(v.selectedTape P z width r banks src tab dst owners a entry layout run π).selected) :
    ∀ h : j.val<(f a).market.failures.rows,(f a).market.failures.cut<
      (f a).market.failures.value ((guard C a).apply entry) ⟨j.val,h⟩ := by
  intro h
  let market:=(f a).atTime v.mesh v.finish (v.basePhase width) a
  let B:=repair C a
  have mask:=run.2.2.2.2.2.1
  have checks:=run.2.2.2.2.2.2.1
  have order:=run.2.2.2.2.2.2.2.1
  have active : market.ready ((guard C a).apply entry):=run.2.1
  have bounds:=v.catalystMaskBounds P z width r banks src tab dst owners a threshold
  have fits : market.rows≤2^W := by
    change B.repairBits.base+market.rows<2^W at mask
    omega
  have before : B.keys≤B.verdict := by
    change (f a).maskStart+2^(f a).indexBits ≤ PostLayout.column (f a).maskStart (f a).indexBits (f a).market.rows _
    unfold PostLayout.column PostLayout.startColumns
    omega
  have width4:=layout.window.wide
  have same:=priced_liveRows market.layout B (f a).pricedArea (f a).stockSource (g a) (prepared C a entry)
    checks order (by omega) before (before.trans (Nat.le_succ _)) bounds.ordered
  let row : Fin market.rows := ⟨j.val,j.isLt⟩
  have ballots : liveRows (enabledBatch market.layout B) (input a entry) market.rows =
      liveRows (enabledBatch market.layout B)
        (postSnapshot market.layout B (prepared C a entry)) market.rows := same
  have committed : row ∈ liveRows (enabledBatch market.layout B)
      (postSnapshot market.layout B (prepared C a entry)) market.rows :=
    (congrArg (fun rows : Finset (Fin market.rows) => row ∈ rows) ballots).mp keep
  have owner : B.batch.owner=.row := by cases a <;> rfl
  have installed : B.failedMIS=market.failures.bank := by cases a <;> rfl
  have selected : (enabledBatch market.layout B).selected
      (postSnapshot market.layout B (prepared C a entry)) (row.val : Word W) :=
    (Finset.mem_filter.mp committed).2.1
  exact market.threshold_of_mask B _ active row owner installed fits bounds.rows bounds.cap bounds.bits
    width4 bounds.cut bounds.prior selected.1

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
