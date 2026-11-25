import OAI.Hierarchy.ProbeCommittedMaskLive
import OAI.Hierarchy.ProtocolRAMCommittedDensity
import OAI.Hierarchy.ProtocolRAMCalendarFrozen

namespace OAI
/-! # A committed repair row is affirmative in the original physical strip directory -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native PurchaseFrozen PurchaseStage RepairHistogram StockCommit
open scoped Fin.CommRing Classical
noncomputable section

theorem Market.threshold_of_selected {z d k q goods : ℕ} (v : Market z d k) (B : Repair q goods)
    (base : Shelf.Mem z d) (ready : v.ready base) (j : Fin v.rows)
    (owner : B.batch.owner=.row) (installed : B.failedMIS=v.failures.bank)
    (fits : v.rows≤2^wordBits z d copies) (rows : v.rows≤v.failures.rows)
    (cap : v.rows≤v.failures.bank.size) (bits : v.rows≤B.repairBits.size)
    (wide : 4≤2^wordBits z d copies) (cut : v.failures.cut<2^wordBits z d copies)
    (prior : v.failures.base+v.rows≤B.tests.excess.out ∧ v.failures.base+v.rows≤B.tests.payload.out ∧
      v.failures.base+v.rows≤B.tests.discrepancy.out) :
    let m := v.prefix.after base
    (enabledBatch v.layout B).selected (postSnapshot v.layout B m) (j.val:Word (wordBits z d copies)) →
    v.failures.cut<v.failures.value base ⟨j.val,j.isLt.trans_le rows⟩ := by
  intro m yes
  exact v.threshold_of_mask B base ready j owner installed fits rows cap bits wide cut prior yes.1

theorem Market.threshold_of_committed {z d k q goods : ℕ} (v : Market z d k) (B : Repair q goods)
    (base : Shelf.Mem z d) (ready : v.ready base) (j : Fin v.rows)
    (owner : B.batch.owner=.row) (installed : B.failedMIS=v.failures.bank)
    (fits : v.rows≤2^wordBits z d copies) (rows : v.rows≤v.failures.rows)
    (cap : v.rows≤v.failures.bank.size) (bits : v.rows≤B.repairBits.size)
    (wide : 4≤2^wordBits z d copies) (cut : v.failures.cut<2^wordBits z d copies)
    (prior : v.failures.base+v.rows≤B.tests.excess.out ∧ v.failures.base+v.rows≤B.tests.payload.out ∧
      v.failures.base+v.rows≤B.tests.discrepancy.out) :
    let m := v.prefix.after base
    j∈liveRows (enabledBatch v.layout B) (postSnapshot v.layout B m) v.rows →
    v.failures.cut<v.failures.value base ⟨j.val,j.isLt.trans_le rows⟩ := by
  intro m keep
  exact v.threshold_of_selected B base ready j owner installed fits rows cap bits wide cut prior (Finset.mem_filter.mp keep).2.1

theorem Market.live_of_selected {z d k q goods : ℕ} (v : Market z d k) (B : Repair q goods)
    (base : Shelf.Mem z d) (ready : v.ready base) (j : Fin v.rows)
    (owner : B.batch.owner=.row) (installed : B.failedMIS=v.failures.bank)
    (fits : v.rows≤2^wordBits z d copies) (rows : v.rows≤v.failures.rows)
    (cap : v.rows≤v.failures.bank.size) (bits : v.rows≤B.repairBits.size)
    (wide : 4≤2^wordBits z d copies) (cut : v.failures.cut<2^wordBits z d copies)
    (prior : v.failures.base+v.rows≤B.tests.excess.out ∧ v.failures.base+v.rows≤B.tests.payload.out ∧
      v.failures.base+v.rows≤B.tests.discrepancy.out) :
    let m := v.prefix.after base
    (enabledBatch v.layout B).selected (postSnapshot v.layout B m) (j.val:Word (wordBits z d copies)) →
    v.failures.live.eval base (j.val:Word (wordBits z d copies))≠0 := by
  intro m keep
  have positive := v.threshold_of_selected B base ready j owner installed fits rows cap bits wide cut prior keep
  intro asleep
  have eq : v.failures.value base ⟨j.val,j.isLt.trans_le rows⟩=0 := by
    simp [FailureWords.value,FailureWords.effective,Expr.eval,asleep,
      ThreeFlat.RAM.DescriptorExpr.Comparison.test]
  omega

theorem Market.live_of_committed {z d k q goods : ℕ} (v : Market z d k) (B : Repair q goods)
    (base : Shelf.Mem z d) (ready : v.ready base) (j : Fin v.rows)
    (owner : B.batch.owner=.row) (installed : B.failedMIS=v.failures.bank)
    (fits : v.rows≤2^wordBits z d copies) (rows : v.rows≤v.failures.rows)
    (cap : v.rows≤v.failures.bank.size) (bits : v.rows≤B.repairBits.size)
    (wide : 4≤2^wordBits z d copies) (cut : v.failures.cut<2^wordBits z d copies)
    (prior : v.failures.base+v.rows≤B.tests.excess.out ∧ v.failures.base+v.rows≤B.tests.payload.out ∧
      v.failures.base+v.rows≤B.tests.discrepancy.out) :
    let m := v.prefix.after base
    j∈liveRows (enabledBatch v.layout B) (postSnapshot v.layout B m) v.rows →
    v.failures.live.eval base (j.val:Word (wordBits z d copies))≠0 := by
  intro m keep
  exact v.live_of_selected B base ready j owner installed fits rows cap bits wide cut prior
    (Finset.mem_filter.mp keep).2.1


end
end Hierarchy.ProtocolRAM.Calendar

end OAI
