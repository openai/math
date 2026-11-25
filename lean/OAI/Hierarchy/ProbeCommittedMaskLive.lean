import OAI.Hierarchy.ProtocolRAMMarketPrefixExec
import OAI.Hierarchy.ProtocolRAMNativeFormat

namespace OAI
/-! # The actual committed repair mask reads the original failure and live cell -/
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native PurchaseFrozen PurchaseStage RepairHistogram
open scoped Fin.CommRing Classical
noncomputable section

/-- Earlier-than-sum allocation keeps each affirmative failure word through all
three native checks. Since the owner's address is literally the row, the later
repair mask cannot redirect one physical row's debit through another tile. -/
theorem Market.threshold_of_mask {z d k q goods : ℕ} (v : Market z d k) (B : Repair q goods)
    (base : Shelf.Mem z d) (ready : v.ready base) (j : Fin v.rows)
    (owner : B.batch.owner=.row) (installed : B.failedMIS=v.failures.bank)
    (fits : v.rows≤2^wordBits z d copies) (rows : v.rows≤v.failures.rows)
    (cap : v.rows≤v.failures.bank.size) (bits : v.rows≤B.repairBits.size)
    (wide : 4≤2^wordBits z d copies) (cut : v.failures.cut<2^wordBits z d copies)
    (prior : v.failures.base+v.rows≤B.tests.excess.out ∧ v.failures.base+v.rows≤B.tests.payload.out ∧
      v.failures.base+v.rows≤B.tests.discrepancy.out) :
    let m := v.prefix.after base
    B.repairBits.read (postSnapshot v.layout B m) (j.val:Word (wordBits z d copies))≠0 →
    v.failures.cut<v.failures.value base ⟨j.val,j.isLt.trans_le rows⟩ := by
  intro m keep
  have eq : B.repairBits.read (postSnapshot v.layout B m) (j.val:Word (wordBits z d copies))=
      (repairMask B).eval (B.tests.after m) (j.val:Word (wordBits z d copies)) := by
    rw [Bank.read,Fin.val_cast_of_lt (j.isLt.trans_le fits),Nat.mod_eq_of_lt (j.isLt.trans_le bits)]
    exact ProtocolRAMGeneratedWrite.read_image ..
  rw [eq] at keep
  simp only [repairMask,AttemptGate.ifRepair,AttemptGate.ifMode_eval _ _ _ _ _ _ wide (by decide : 2<4),Expr.eval] at keep
  have on : B.failedMIS.read (B.tests.after m) (B.batch.owner.eval (B.tests.after m) (j.val:Word (wordBits z d copies)))≠0 := by
    split_ifs at keep <;> simp_all
  rw [installed,owner] at on
  change B.tests.after m (v.failures.base+((j.val:Word (wordBits z d copies)).val%v.failures.bank.size))≠0 at on
  rw [Fin.val_cast_of_lt (j.isLt.trans_le fits),Nat.mod_eq_of_lt (j.isLt.trans_le cap)] at on
  let address := v.failures.base+j.val
  have earlier : address<v.failures.base+v.rows := Nat.add_lt_add_left j.isLt _
  have word := v.failed_word base ready cut ⟨j.val,j.isLt.trans_le rows⟩
  change B.tests.after m address≠0 at on
  rw [AttemptGate.TestBoard.after,B.tests.discrepancy.frame _ _ (earlier.trans_le prior.2.2),
    B.tests.payload.frame _ _ (earlier.trans_le prior.2.1),B.tests.excess.frame _ _ (earlier.trans_le prior.1)] at on
  have positive : v.failures.cut<v.failures.value base ⟨j.val,j.isLt.trans_le rows⟩ := by
    by_contra no
    simp [no] at word
    exact on word
  exact positive

theorem Market.live_of_mask {z d k q goods : ℕ} (v : Market z d k) (B : Repair q goods)
    (base : Shelf.Mem z d) (ready : v.ready base) (j : Fin v.rows)
    (owner : B.batch.owner=.row) (installed : B.failedMIS=v.failures.bank)
    (fits : v.rows≤2^wordBits z d copies) (rows : v.rows≤v.failures.rows)
    (cap : v.rows≤v.failures.bank.size) (bits : v.rows≤B.repairBits.size)
    (wide : 4≤2^wordBits z d copies) (cut : v.failures.cut<2^wordBits z d copies)
    (prior : v.failures.base+v.rows≤B.tests.excess.out ∧ v.failures.base+v.rows≤B.tests.payload.out ∧
      v.failures.base+v.rows≤B.tests.discrepancy.out) :
    let m := v.prefix.after base
    (postSnapshot v.layout B m) (B.repairBits.base+j.val)≠0 →
    v.failures.live.eval base (j.val:Word (wordBits z d copies))≠0 := by
  intro m keep
  have flag : B.repairBits.read (postSnapshot v.layout B m) (j.val:Word (wordBits z d copies))≠0 := by
    simpa only [Bank.read,Fin.val_cast_of_lt (j.isLt.trans_le fits),Nat.mod_eq_of_lt (j.isLt.trans_le bits)] using keep
  have positive := v.threshold_of_mask B base ready j owner installed fits rows cap bits wide cut prior flag
  intro asleep
  have eq : v.failures.value base ⟨j.val,j.isLt.trans_le rows⟩=0 := by
    simp [FailureWords.value,FailureWords.effective,Expr.eval,asleep,
      ThreeFlat.RAM.DescriptorExpr.Comparison.test]
  omega

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
