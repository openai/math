import OAI.Hierarchy.ProtocolRAMCalendarVerdict

namespace OAI
/-! # Retaining a word through the actual post-test writes and stock commit -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing Classical
noncomputable section
namespace Calendar
open PurchaseStage

theorem after_prepared {w q goods : ℕ} (C : Chart w q goods) (a : Attempt) (m : Memory w) (x : ℕ)
    (h : ready C (.attempt a) m) : let B:=repair C a
    x<B.tests.excess.out → x<B.tests.payload.out → x<B.tests.discrepancy.out → x<B.repairBits.base →
    (∀u∈audits (C.layout a) B,x<u.low) → x<B.verdict → (C.commit a).keeps x →
      after C (.attempt a) m x=prepared C a m x := by
  intro B hx hy hz hm ha hv hc
  let L:=C.layout a
  let v:=prepared C a m
  rcases h with ⟨_,_,_,_,_,_,ok,_,_,_,commit,_,_⟩
  rw [after,(C.commit a).frame _ _ commit hc]
  change verdictMemory B.verdict (audits L B) (postSnapshot L B v) x=v x
  simp only [verdictMemory,image,fillSegment,not_le.mpr hv,false_and,ite_false]
  rw [audit_below _ _ ok x ha]
  change image B.repairBits.base _ _ (B.tests.after v) x=v x
  simp only [image,fillSegment,not_le.mpr hm,false_and,ite_false,AttemptGate.TestBoard.after]
  rw [B.tests.discrepancy.frame _ x hz,B.tests.payload.frame _ x hy,B.tests.excess.frame _ x hx]

end Calendar
end
end Hierarchy.ProtocolRAM

end OAI
