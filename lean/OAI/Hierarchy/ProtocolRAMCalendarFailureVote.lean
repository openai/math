import OAI.Hierarchy.ProtocolRAMCalendarThreshold
import OAI.Hierarchy.ProtocolRAMCalendarPriced

namespace OAI
/-! # A repair vote measures the original failed-strip score words -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AttemptGate PurchaseStage
open ThreeFlat.RAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {z d k q goods r edges : ℕ}

private theorem effective_fits (v : Market z d k) {m : PurchaseFrozen.Shelf.Mem z d}
    (h : v.ready m) : v.failures.effective.Fits (wordBits z d copies) v.failures.base :=
  h.1.1.2.1

/-- The frozen pass writes the local flags above all expression inputs. The two
preceding tests also write above these inputs, so each discrepancy score word
still reads the value from the incoming market tape. -/
theorem Market.failure_value_after (v : Market z d k) (m : PurchaseFrozen.Shelf.Mem z d)
    (h : v.ready m) (excess payload : Check)
    (lo : v.failures.base≤excess.out) (hi : v.failures.base≤payload.out) (i : Fin v.failures.rows) :
    v.failures.value (payload.after (excess.after (v.prefix.after m))) i=v.failures.value m i := by
  have marketStart := h.2.1
  apply congrArg Fin.val
  apply ProtocolRAM.eval_below _ _ m _ (effective_fits v h)
  intro a ha
  exact (payload.frame _ a (ha.trans_le hi)).trans ((excess.frame _ a (ha.trans_le lo)).trans
    (v.prefix.frame m a h (.inl (lt_min ha (by omega)))))

/-- Both Boolean outcomes of the physical discrepancy pass equal the comparison
on the incoming market tape. The live selector is part of the expression. -/
theorem Market.failure_high (v : Market z d k) (m : PurchaseFrozen.Shelf.Mem z d)
    (h : v.ready m) (b : Repair q goods) (lo : v.failures.base≤b.tests.excess.out)
    (hi : v.failures.base≤b.tests.payload.out) :
    let t := (testedBoard v.failures b).tests
    t.discrepancy.high (t.payload.after (t.excess.after (v.prefix.after m))) =
      decide (v.failures.globalBound ≤ ∑ i, v.failures.value m i) := by
  change decide (v.failures.globalBound ≤ ∑ i, v.failures.value
    (b.tests.payload.after (b.tests.excess.after (v.prefix.after m))) i) = _
  simp_rw [v.failure_value_after m h _ _ lo hi]

/-- For an actual installed date the guard, failure flags, and all three score
checks use their concrete allocated addresses. A mode-two vote gives the
integer comparison on the pre-guard tape, also for a reserve attempt. -/
theorem priced_failure_vote (c : Mesh) (finish : ℝ) (prices : PhasePrice) (format : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (a : Attempt)
    (m : PurchaseFrozen.Shelf.Mem z d) :
    let C := pricedInstalled c finish prices format feeds sink idBase role ids
    let B := repair C a
    ready C (.attempt a) m → TestRoom B (wordBits z d copies) →
    actual B.policy (postSnapshot (C.layout a) B (prepared C a m))=2 →
    (format a).market.failures.globalBound ≤ ∑ i, (format a).market.failures.value m i := by
  let C := pricedInstalled c finish prices format feeds sink idBase role ids
  let B := repair C a
  let v := (format a).atTime c finish prices a
  let base := (guard C a).apply m
  change ready C (.attempt a) m → TestRoom B (wordBits z d copies) →
    actual B.policy (postSnapshot (C.layout a) B (prepared C a m))=2 →
    v.failures.globalBound ≤ ∑ i, v.failures.value m i
  intro ok room mode
  have rv : v.ready base := ok.2.1
  have flags : v.shelf.firstBase ≤ v.flags := by
    unfold Market.flags PurchaseFrozen.Shelf.flagsBase
    omega
  have lo : v.failures.base ≤ (format a).testsStart := by
    have first := rv.2.1
    change v.failures.base ≤ v.flags+v.rows
    omega
  have start : v.failures.base ≤ B.tests.excess.out := by
    change v.failures.base ≤ (format a).testsStart+1
    omega
  have later : v.failures.base ≤ B.tests.payload.out := by have order := room.excess; omega
  have hit := (discrepancy_votes (C.layout a) B (v.prefix.after base) room).1 mode
  change decide (v.failures.globalBound ≤ ∑ i, v.failures.value
    (B.tests.payload.after (B.tests.excess.after (v.prefix.after base))) i) = true at hit
  simp_rw [v.failure_value_after base rv _ _ start later] at hit
  have old (i : Fin v.failures.rows) : v.failures.value base i = v.failures.value m i := by
    apply congrArg Fin.val
    apply ProtocolRAM.eval_below _ _ m base (effective_fits v rv)
    intro j hj
    exact ProtocolRAMGeneratedWrite.frame_image (C.stopAt a) 1 (stop C.mesh C.modeAt a) m j
      (.inl (hj.trans_le lo))
  simp_rw [old] at hit
  exact of_decide_eq_true hit

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
