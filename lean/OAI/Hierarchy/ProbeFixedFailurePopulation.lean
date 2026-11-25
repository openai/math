import OAI.Hierarchy.ProbeFixedFailureEconomy
import OAI.Hierarchy.ProbeFixedCatalystMask
import OAI.Hierarchy.ProtocolRAMCalendarFailureVote
import OAI.Hierarchy.ProtocolRAMCalendarPricedBallot
import OAI.Hierarchy.ProbeMarketFailures

namespace OAI
/-! # Density of the selected native repair histograms at an actual fixed-protocol date -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StockCommit PurchaseStage
open scoped BigOperators Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "st" => v.taskCommit P z width
local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "input" => v.stage P z width r banks src tab dst owners
local notation "raw" => (fun a=>(f a).atTime v.mesh v.finish (v.basePhase width) a)
local notation "wall" => wallCap v.radius (upperBox (publicStages v.W) v.radius)
variable (a : Attempt) (entry : Memory (wordBits z (2^v.W) copies))
local notation "B" => repair C a
local notation "original" => (guard C a).apply entry
local notation "checked" => postSnapshot ((C).layout a) B (prepared C a entry)

theorem score_room (run : ready C (.attempt a) entry) (wide : 4≤2^W) : TestRoom B W := by
  refine ⟨wide,run.2.2.2.2.1.1,?_,?_,?_⟩ <;> exact Nat.lt_succ_self _

def activeRoots := Finset.univ.filter (fun i : Fin (raw a).rows=>
  (raw a).failures.live.eval original (i.val:Word W)≠0)

theorem selected_population (layout : StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a)
      v.keepLimit width ((v.privateArena P z width).base v.mesh (.attempt a)))
    (run : ready C (.attempt a) entry) (π : PortPlan (st a) (b a) (input a entry) (f a).market.rows)
    (valid : accepted C (.attempt a) entry) (failed : AttemptGate.actual (B).policy checked=2)
    (threshold : (⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊)<2^W)
    (support : (v.activeRoots P z width r banks src tab dst owners a entry).card≤2^z)
    (ceiling : ∀i : Fin (raw a).failures.rows,((raw a).failures.value original i:ℝ)/v.precision≤wall)
    (eligible : ∀i : Fin (raw a).rows,∀h : i.val<(raw a).failures.rows,
      (raw a).failures.cut<(raw a).failures.value original ⟨i.val,h⟩ →
      (B).batch.packet.eval checked (i.val:Word W)≠0 ∧ ∀p,
        (((B).batch.need p).eval checked (i.val:Word W)).val≤(((B).batch.stock p).eval checked (i.val:Word W)).val) :
    v.loss*(2^z:ℕ)≤(v.selectedTape P z width r banks src tab dst owners a entry layout run π).selected.card := by
  let market:=raw a
  let live:=v.activeRoots P z width r banks src tab dst owners a entry
  let fail:=market.failures
  have mask:=run.2.2.2.2.2.1
  have checks:=run.2.2.2.2.2.2.1
  have order:=run.2.2.2.2.2.2.2.1
  have active : market.ready original:=run.2.1
  have bounds:=v.catalystMaskBounds P z width r banks src tab dst owners a threshold
  have wide:=layout.window.wide
  have score : TestRoom B W := v.score_room P z width r banks src tab dst owners a entry run wide
  have count : market.rows=fail.rows := by cases a <;> rfl
  have totalCap : fail.globalBound=⌈4*v.toleranceAt*(2^z:ℕ)*(v.precision:ℝ)⌉₊ := by cases a <;> rfl
  have Bfits : market.rows≤2^W := by change (B).repairBits.base+market.rows<2^W at mask;omega
  have global:= (discrepancy_votes ((C).layout a) B (prepared C a entry) score).1 failed
  change decide (fail.globalBound≤∑i,fail.value ((B).tests.payload.after ((B).tests.excess.after
    (market.prefix.after original))) i)=true at global
  have lo : fail.base≤(B).tests.excess.out := (Nat.le_add_right ..).trans bounds.prior.1
  have hi : fail.base≤(B).tests.payload.out := (Nat.le_add_right ..).trans bounds.prior.2.1
  have sameTotal : (∑ i : Fin fail.rows, fail.value ((B).tests.payload.after
      ((B).tests.excess.after (market.prefix.after original))) i) =
      ∑ i : Fin fail.rows, fail.value original i := by
    apply Finset.sum_congr rfl
    intro i _
    exact market.failure_value_after original active (B).tests.excess (B).tests.payload lo hi i
  have yes : fail.globalBound ≤ ∑ i : Fin fail.rows, fail.value original i :=
    (of_decide_eq_true global).trans sameTotal.le
  have high : fail.globalBound≤∑i : Fin market.rows,fail.value original ⟨i.val,i.isLt.trans_le bounds.rows⟩ := by
    have eqn:=(finCongr count).sum_comp (fun i=>fail.value original i)
    exact yes.trans eqn.ge
  have hits:=market.committed_iff_threshold B original active (by cases a <;> rfl) (by cases a <;> rfl)
    Bfits bounds.rows bounds.cap bounds.bits wide bounds.cut bounds.prior
    ((bounds.mask.mode ((C).layout a) B (prepared C a entry)).symm.trans failed)
    (fun j=>valid j.val j.isLt) (fun j=>eligible j _)
  have nonneg : 0≤wall := by
    have box : 0≤upperBox (publicStages v.W) v.radius := (Nat.cast_nonneg _).trans (le_max_left ..)
    unfold wallCap
    positivity
  have enough:=market.paid_population B original (2^z) v.precision v.toleranceAt wall v.clock.precision_pos
    v.geometry.cutoff.1 nonneg bounds.rows live support (v.catalyst_test_cut P z width a) totalCap
    (by
      intro i off
      have zero : market.failures.live.eval original (i.val:Word W)=0 := by
        simpa [live,activeRoots] using off
      simp [FailureWords.value,FailureWords.effective,Expr.eval,
        ThreeFlat.RAM.DescriptorExpr.Comparison.test,zero])
    (fun i=>ceiling _) high hits
  have before : (B).keys≤(B).verdict := by
    change (f a).maskStart+2^(f a).indexBits ≤ PostLayout.column (f a).maskStart (f a).indexBits (f a).market.rows _
    unfold PostLayout.column PostLayout.startColumns
    omega
  have endFlag : (B).keys≤(g a).out := before.trans (Nat.le_succ _)
  have same:=priced_liveRows market.layout B (f a).pricedArea (f a).stockSource (g a) (prepared C a entry)
    checks order (by omega) before endFlag bounds.ordered
  change v.loss*(2^z:ℕ)≤(liveRows (enabledBatch market.layout B) (input a entry) market.rows).card
  rw [show liveRows (enabledBatch market.layout B) (input a entry) market.rows=
    liveRows (enabledBatch market.layout B) checked market.rows from same]
  exact enough

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
