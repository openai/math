import OAI.Hierarchy.ProtocolRAMCalendarFrozen
import OAI.Hierarchy.ProtocolRAMBelow

namespace OAI
/-! # A strip's native repair ballot is determined before its current private selector -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen PurchaseStage
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing

private theorem check_before {w cut : ℕ} (c : AttemptGate.Check) (left right : Memory w)
    (agree : Below cut left right) (low : cut≤c.out) : Below cut (c.after left) (c.after right) := by
  intro a ha
  rw [c.frame left a (ha.trans_le low),c.frame right a (ha.trans_le low)]
  exact agree a ha

private theorem high_before {w cut : ℕ} (c : AttemptGate.Check) (left right : Memory w)
    (agree : Below cut left right) (terms : c.term.Fits w cut) :
    c.high left=c.high right := by
  suffices same : c.score left=c.score right by simp only [AttemptGate.Check.high,same]
  exact funext fun i=>congrArg Fin.val (agree.expr c.term (i.val:Word w) terms le_rfl)

/-- The discrepancy bit at a single native candidate is computed on the
original stock and price words. All sign/DFS words and current counters
may vary except where the two actual executions read an earlier address. -/
theorem Market.mask_before {z d k q goods cut : ℕ} (v : Market z d k) (b : Repair q goods)
    (left right : Shelf.Mem z d) (hL : v.ready left) (hR : v.ready right)
    (agree : Below cut left right) (before : cut≤v.prefix.start)
    (owner : b.batch.owner=.row) (mis : b.failedMIS=v.failures.bank)
    (stop : AttemptGate.bit b.tests.stop (v.prefix.after left)=AttemptGate.bit b.tests.stop (v.prefix.after right))
    (excess : b.tests.excess.term.Fits (wordBits z d copies) cut)
    (payload : b.tests.payload.term.Fits (wordBits z d copies) cut)
    (disc : b.tests.discrepancy.term=v.failures.effective)
    (effective : v.failures.effective.Fits (wordBits z d copies) cut)
    (ordered : b.tests.stop.base<b.tests.excess.out ∧
      b.tests.excess.out+b.tests.excess.rows<b.tests.payload.out ∧
      b.tests.payload.out+b.tests.payload.rows<b.tests.discrepancy.out)
    (early : v.failures.base+v.rows≤b.tests.excess.out)
    (allRows : v.rows≤v.failures.rows) (maskRoom : v.rows≤b.repairBits.size)
    (pageRoom : v.rows≤v.failures.bank.size)
    (wordRoom : v.rows≤2^wordBits z d copies) (wide : 0<wordBits z d copies)
    (thresholdRoom : v.failures.cut<2^wordBits z d copies)
    (i : Fin v.rows) :
    b.repairBits.read (postSnapshot v.layout b (v.prefix.after left)) (i.val:Word (wordBits z d copies)) =
    b.repairBits.read (postSnapshot v.layout b (v.prefix.after right)) (i.val:Word (wordBits z d copies)) := by
  let l:=v.prefix.after left
  let r:=v.prefix.after right
  let row:= (i.val:Word (wordBits z d copies))
  have first : Below cut l r := by
    intro a ha
    exact (v.prefix.frame left a hL (Or.inl (ha.trans_le before))).trans
      ((agree a ha).trans (v.prefix.frame right a hR (Or.inl (ha.trans_le before))).symm)
  have hcut : cut≤v.failures.base := before.trans (Nat.min_le_left ..)
  obtain ⟨hs,hx,hp⟩:=ordered
  have sec := check_before b.tests.excess l r first (by omega)
  have third := check_before b.tests.payload _ _ sec (by omega)
  have mode : (AttemptGate.mode b.policy).eval (b.tests.after l) row =
      (AttemptGate.mode b.policy).eval (b.tests.after r) row := by
    have stopWord : AttemptGate.bit b.tests.stop l=AttemptGate.bit b.tests.stop r := stop
    unfold Repair.policy
    rw [b.tests.mode l row wide hs hx hp,b.tests.mode r row wide hs hx hp,stopWord,
      high_before _ _ _ first excess,high_before _ _ _ sec payload,
      high_before _ _ _ third (disc.symm ▸ effective)]
  have failed (m : Shelf.Mem z d) (recorded : v.ready m) :
      b.failedMIS.read (b.tests.after (v.prefix.after m)) row =
      if v.failures.cut<v.failures.value m ⟨i.val,i.isLt.trans_le allRows⟩ then 1 else 0 := by
    rw [mis]
    change b.tests.after (v.prefix.after m) (v.failures.base+row.val%v.failures.bank.size)=_
    have hrow : row.val=i.val := Fin.val_cast_of_lt (i.isLt.trans_le wordRoom)
    rw [hrow,Nat.mod_eq_of_lt (i.isLt.trans_le pageRoom)]
    have h:=i.isLt
    rw [AttemptGate.TestBoard.after,b.tests.discrepancy.frame _ _ (by omega),
      b.tests.payload.frame _ _ (by omega),b.tests.excess.frame _ _ (by omega)]
    exact v.failed_word m recorded thresholdRoom ⟨i.val,i.isLt.trans_le allRows⟩
  have data : b.failedMIS.read (b.tests.after l) row=b.failedMIS.read (b.tests.after r) row := by
    rw [failed left hL,failed right hR]
    have value : v.failures.value left ⟨i.val,i.isLt.trans_le allRows⟩=
        v.failures.value right ⟨i.val,i.isLt.trans_le allRows⟩ :=
      congrArg Fin.val (agree.expr _ row effective le_rfl)
    rw [value]
  have readMask (m : Shelf.Mem z d) :
      b.repairBits.read (postSnapshot v.layout b m) row=(repairMask b).eval (b.tests.after m) row := by
    rw [Bank.read,show row.val=i.val from Fin.val_cast_of_lt (i.isLt.trans_le wordRoom),
      Nat.mod_eq_of_lt (i.isLt.trans_le maskRoom)]
    exact ProtocolRAMGeneratedWrite.read_image ..
  change b.repairBits.read (postSnapshot v.layout b l) row=b.repairBits.read (postSnapshot v.layout b r) row
  rw [readMask l,readMask r]
  simp only [repairMask,AttemptGate.ifRepair,AttemptGate.ifMode,Expr.eval,owner,mode,data]
  rfl

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
