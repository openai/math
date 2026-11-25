import OAI.Hierarchy.ProtocolRAMPortPaddingCore
import OAI.Hierarchy.ProtocolRAMRepairHistogram
import OAI.Hierarchy.ProtocolRAMAdmission

namespace OAI
/-! # A fixed native port count for different local packet geometries -/

namespace Hierarchy.ProtocolRAM.PortPadding
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
variable {n D q w : ℕ}

/-- Extra roles have no stock demand and no stock. The selector alphabet and
the packet lookup continue to read the original words for this geometry. -/
def batch (D : ℕ) (b : Batch q n) : Batch q D :=
  ⟨b.copies,b.radix,b.maxWidth,b.quotes,b.menu,b.termCount,b.enabled,b.owner,b.field,
    extend b.stock (.lit 0), extend b.perCopy (.lit 0)⟩

theorem real_need (b : Batch q n) (bound : n ≤ D) (i : Fin n) :
    (batch D b).need (inject bound i) = b.need i := by simp [Batch.need,batch]

theorem tail_need (b : Batch q n) (m : Memory w) (r : Word w) (i : Fin D) (hi : n ≤ i.val)
    (fits : b.maxWidth < 2^w) :
    ((batch D b).need i).eval m r = 0 := by
  simp only [Batch.need,batch,extend_tail _ _ _ hi]
  rw [eval_boundedMul m r _ _ _ (by simp [Expr.eval]) fits]
  simp [Expr.eval]

theorem selected (b : Batch q n) (m : Memory w) (r : Word w) (bound : n ≤ D)
    (fits : b.maxWidth < 2^w) :
    (batch D b).selected m r ↔ b.selected m r := by
  constructor
  · rintro ⟨enabled,packet,enough⟩
    refine ⟨enabled,packet,fun i => ?_⟩
    simpa only [Batch.need,batch,extend_real] using enough (inject bound i)
  · rintro ⟨enabled,packet,enough⟩
    refine ⟨enabled,packet,fun i => ?_⟩
    by_cases hi : i.val < n
    · let j : Fin n := ⟨i.val,hi⟩
      have eq : i=inject bound j := Fin.ext rfl
      simpa only [eq,Batch.need,batch,extend_real] using enough j
    · rw [tail_need b m r i (Nat.le_of_not_gt hi) fits]
      exact Nat.zero_le _

theorem valid (b : Batch q n) (m : Memory w) (r : Word w) (bound : n ≤ D)
    (fits : b.maxWidth < 2^w) :
    (batch D b).valid m r ↔ b.valid m r := by
  simp only [Batch.valid,selected b m r bound fits]; rfl

theorem committed (b : Batch q n) (m : Memory w) (r : Word w) (bound : n ≤ D)
    (fits : b.maxWidth < 2^w) :
    RepairHistogram.committed (batch D b) m r ↔ RepairHistogram.committed b m r := by
  simp only [RepairHistogram.committed,selected b m r bound fits]; rfl

theorem debit (b : Batch q n) (m : Memory w) (r : Word w) (bound : n ≤ D)
    (fits : b.maxWidth < 2^w) (qFit : q ≤ 2^w) (copyFit : b.copies < 2^w)
    (sumFit : q*b.copies < 2^w) (i : Fin D) :
    (RepairHistogram.debit (batch D b) i).eval m r =
      extend (fun j => (RepairHistogram.debit b j).eval m r) 0 i := by
  by_cases hi : i.val<n
  · let j : Fin n := ⟨i.val,hi⟩
    have eq : i=inject bound j := Fin.ext rfl
    rw [eq,extend_real,RepairHistogram.debit_eval (batch D b) _ m r qFit copyFit sumFit,
      RepairHistogram.debit_eval b _ m r qFit copyFit sumFit,real_need b bound j]
    simp only [committed b m r bound fits]
  · rw [extend_tail _ _ _ (Nat.le_of_not_gt hi),RepairHistogram.debit_eval (batch D b) i m r qFit copyFit sumFit,
      tail_need b m r i (Nat.le_of_not_gt hi) fits]
    simp

theorem wire (b : Batch q n) (m : Memory w) (r : Word w) (bound : n ≤ D)
    (fits : b.maxWidth < 2^w) (qFit : q ≤ 2^w) (copyFit : b.copies < 2^w)
    (sumFit : q*b.copies < 2^w) (table : Fin n → Fin q → Expr) (i : Fin D) :
    ((batch D b).wire (extend table (fun _ => .lit 0) i)).eval m r =
      extend (fun j => (b.wire (table j)).eval m r) 0 i := by
  by_cases hi : i.val<n
  · let j : Fin n := ⟨i.val,hi⟩
    have eq : i=inject bound j := Fin.ext rfl
    simp only [eq,extend_real,Batch.wire,Batch.eval_ifSelected,selected b m r bound fits]; rfl
  · rw [extend_tail _ _ _ (Nat.le_of_not_gt hi),extend_tail _ _ _ (Nat.le_of_not_gt hi)]
    rw [Batch.wire,Batch.eval_ifSelected,Batch.eval_ifPacket (batch D b) m r _ _ qFit copyFit sumFit]
    have zero (j : Fin q) : (boundedMul b.maxWidth (b.field j) (.lit 0)).eval m r=0 := by
      rw [eval_boundedMul m r _ _ _ (by simp [Expr.eval]) fits]
      simp [Expr.eval]
    simp [installed,zero,batch,Expr.eval]

end Hierarchy.ProtocolRAM.PortPadding

end OAI
