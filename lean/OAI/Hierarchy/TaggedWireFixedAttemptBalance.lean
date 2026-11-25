import OAI.Hierarchy.ProbeFixedStockConservation
import OAI.Hierarchy.TaggedWireFixedGoodsChange

namespace OAI
/-! # Conservation of the dated physical goods total at a selected attempt -/
noncomputable section
set_option maxRecDepth 4096
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage ProbeStage.Native CoreBoard
open StripChart StockCommit PurchaseStage RepairHistogram
open scoped BigOperators Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  {v : FixedProtocolFormat F k p q Q σ Λ} {P : v.Placement} {z width r : ℕ}
  {banks : RouteSettlement.Banks} {src tab dst : ℕ} {owners : Bank}
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "bs" => v.stockBanks P z width
local notation "es" => events v.mesh
local notation "Good" => FeedLayout.Good z (Stages z (2^v.W)) k
local notation "Qty" => v.datedQuantity P z width r banks src tab dst owners
variable {π : Equiv.Perm (Fin (2^z))} {mem fixture : Memory (Native.wordBits z (2^v.W) copies)}
  (D : v.ReadbackRun P z width r banks src tab dst owners π mem fixture)

include D in
/-- In a failed trial, the exact two temporal quantities differ by the signed
issued occurrence widths and the actual clipping word. Every other mode
preserves the two temporal quantities and publishes a zero clipping word. -/
theorem ReadbackRun.dated_attempt_balance (B : RepairWordBounds v P z width)
    (n : ℕ) (on : n<(es).length) (a : Attempt) (atTrial : (es)[n]=.attempt a)
    {prior tail : List Event} {entry : Memory W} (cut : Slot (w := W) C mem (.attempt a) prior tail entry)
    (i : Good) :
    let out:=after C (.attempt a) entry
    let ar:=(f a).pricedArea
    let t:=v.taskCommit P z width a
    let u:=v.stage P z width r banks src tab dst owners a entry
    let j:=v.nativeSlots P z width a i
    let tag:=RepairHistogram.kind (n:=t.occurrences) (goods:=t.goods) t.plan.bank t.columns u
    let put:=resourceBits tag (installedBits (n:=t.occurrences) t.columns u) j
    let take:=resourceBits tag (consumedBits (n:=t.occurrences) t.columns u) j
    let spill:=(out (ar.output+ar.goods+ar.goods+PurchaseInventory.slot i)).val
    let mode:=(out ((C).modeAt a)).val
    (mode=2 → Qty n entry i+put=Qty (n+1) out i+spill+take) ∧
      (mode≠2 → Qty n entry i=Qty (n+1) out i ∧ spill=0) := by
  classical
  intro out ar t u j tag put take spill mode
  let old:=(entry ((f a).stockSource.old.base+j.val)).val
  let kept:=(out (ar.output+j.val)).val
  let saved:=(out (ar.output+ar.goods+j.val)).val
  let waiting:=v.attemptPassive P z width r banks src tab dst owners a entry i
  let new:=v.newlyHeld P z width r banks src tab dst owners a out i
  have pos : j.val=PurchaseInventory.slot i:=v.slot_index P z width a i
  have stamped:=D.attempt_mode a prior tail entry cut
  have h:=D.attempt_conservation B a prior tail entry cut j
  dsimp only at h
  rw [←stamped] at h
  change (mode=2 → old+put=kept+(out (ar.output+ar.goods+ar.goods+j.val)).val+take) ∧
    (mode=3 → old=kept+saved) ∧ (mode≠2 → mode≠3 → old=kept) ∧
    (mode≠2 → (out (ar.output+ar.goods+ar.goods+j.val)).val=0) at h
  have spillWord : (out (ar.output+ar.goods+ar.goods+j.val)).val=spill := by rw [pos]
  rw [spillWord] at h
  obtain ⟨prev,next⟩:=v.dated_attempt_quantities P z width r banks src tab dst owners n on a atTrial cut i
  change Qty n entry i=waiting+PurchaseInventory.stock ((bs).previous v.mesh (.attempt a)) entry i at prev
  rw [←(v.attempt_stock_banks P z width a).1] at prev
  change Qty n entry i=waiting+(entry ((f a).stockSource.old.base+PurchaseInventory.slot i)).val at prev
  rw [←pos] at prev
  change Qty (n+1) out i=waiting+new+(out (ar.output+PurchaseInventory.slot i)).val at next
  rw [←pos] at next
  change Qty n entry i=waiting+old at prev
  change Qty (n+1) out i=waiting+new+kept at next
  have accrual : new=(if mode=3 then saved else 0) := by
    cases a with
    | outer p a =>
      have occurs : Event.attempt (.outer p a)∈events v.mesh:=by
        change _∈events (C).mesh
        rw [cut.events]
        simp
      have room : 3<2^W:=by have := (D.boards _ occurs).1.window.wide;omega
      have small : (3:Word W).val=3:=Fin.val_cast_of_lt room
      have eqv : out ((C).modeAt (.outer p a))=3 ↔ mode=3 := by
        constructor
        · intro eq
          change (out _).val=3
          rw [eq,small]
        · intro eq
          apply Fin.ext
          exact eq.trans small.symm
      dsimp only [new]
      rw [v.newlyHeld_outer P z width r banks src tab dst owners p a out i]
      by_cases yes : mode=3
      · rw [ite_eq_left (eqv.mpr yes), ite_eq_left yes]
        change (out (ar.output+ar.goods+PurchaseInventory.slot i)).val=_
        rw [←pos]
      · rw [ite_eq_right (fun hit => yes (eqv.mp hit)), ite_eq_right yes]
    | inner p a s b =>
      have off : mode≠3:=by
        rw [show mode=AttemptGate.actual (repair C (.inner p a s b)).policy
          (postSnapshot ((C).layout (.inner p a s b)) (repair C (.inner p a s b))
            (prepared C (.inner p a s b) entry)) from stamped]
        exact AttemptGate.reserve_no_purchase _ _ rfl
      rw [ite_eq_right off]
      rfl
  rw [prev,next,accrual]
  constructor
  · intro fail
    rw [ite_eq_right (by omega : mode≠3)]
    have balance:=h.1 fail
    omega
  · intro off
    refine ⟨?_,h.2.2.2 off⟩
    by_cases buy : mode=3
    · rw [ite_eq_left buy]
      have sale:=h.2.1 buy
      omega
    · rw [ite_eq_right buy]
      have idle:=h.2.2.1 off buy
      omega

include D in
/-- The signed emitted occurrence columns themselves vanish outside a repair.
Thus the same ledger identity holds across every attempt without a case mask. -/
theorem ReadbackRun.dated_attempt_ledger (B : RepairWordBounds v P z width)
    (n : ℕ) (on : n<(es).length) (a : Attempt) (atTrial : (es)[n]=.attempt a)
    {prior tail : List Event} {entry : Memory W} (cut : Slot (w := W) C mem (.attempt a) prior tail entry)
    (i : Good) :
    let out:=after C (.attempt a) entry
    let ar:=(f a).pricedArea
    let t:=v.taskCommit P z width a
    let u:=v.stage P z width r banks src tab dst owners a entry
    let j:=v.nativeSlots P z width a i
    let tag:=RepairHistogram.kind (n:=t.occurrences) (goods:=t.goods) t.plan.bank t.columns u
    let put:=resourceBits tag (installedBits (n:=t.occurrences) t.columns u) j
    let take:=resourceBits tag (consumedBits (n:=t.occurrences) t.columns u) j
    let spill:=(out (ar.output+ar.goods+ar.goods+PurchaseInventory.slot i)).val
    let _mode:=(out ((C).modeAt a)).val
    Qty n entry i+put=Qty (n+1) out i+spill+take := by
  classical
  intro out ar t u j tag put take spill _mode
  have link:=D.dated_attempt_balance B n on a atTrial cut i
  by_cases active : _mode=2
  · exact link.1 active
  · obtain ⟨unchanged,spillZero⟩:=link.2 active
    change Qty n entry i=Qty (n+1) out i at unchanged
    change spill=0 at spillZero
    let data:=v.slot_inputs P z width r banks src tab dst owners mem fixture D.boards a prior tail entry cut
    obtain ⟨ports⟩:=data.ports
    have flag:=D.attempt_mode a prior tail entry cut
    have absent : AttemptGate.actual (repair C a).policy
        (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))≠2:=by
      rw [←flag]
      exact active
    have widths (e : Fin t.occurrences) : installedBits t.columns u e=0 ∧ consumedBits t.columns u e=0 := by
      have off:=v.rows_off_of_ne P z width r banks src tab dst owners a entry cut.currentReady
        data.toTrialLayout absent (ports.enum.symm e).1
      exact ports.off e (by
        simpa only [StockCommit.liveRows, Finset.mem_filter, Finset.mem_univ, true_and,
          FixedProtocolFormat.ballot, FixedProtocolFormat.stage] using off)
    have emptyPut : put=0:=by
      unfold put resourceBits
      apply Finset.sum_eq_zero
      intro e _
      simp [(widths e).1]
    have emptyTake : take=0:=by
      unfold take resourceBits
      apply Finset.sum_eq_zero
      intro e _
      simp [(widths e).2]
    omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
