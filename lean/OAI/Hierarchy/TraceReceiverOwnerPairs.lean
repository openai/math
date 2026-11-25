import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Interleaving the classifier's literal owner words with group zero -/
namespace Hierarchy.TraceReceiverOwnerPairs
open ThreeFlat RAM DescriptorExpr DescriptorScan PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
variable {W : ℕ}

/-- At offset 2i the emitted word is zero; at 2i+1 it is the classifier's ith word. -/
def expression (W src dst : ℕ) : Term W 0 1 :=
  let δ := Term.binary .sub (.result 0) (.literal dst)
  .binary .mul (.binary .mod δ (.literal 2))
    (.load (.binary .add (.literal src) (.binary .div δ (.literal 2))))

def procedure (W src dst n : ℕ) : Procedure W :=
  PhysicalInputPhases.writing (expression W src dst) Fin.elim0 dst (2*n)

def image (src dst n : ℕ) (m : Memory W) :=
  fillSegment dst (2*n) (fun a=>(↑((a-dst)%2):Word W)*m (src+(a-dst)/2)) m

theorem binds (W src dst : ℕ) : (expression W src dst).binds=12 := by
  simp only [expression,Term.load,Term.binary,Term.literal,Term.binds_letThen,Term.binds_rename,Term.binds]

theorem hardware (W src dst n : ℕ) :
    (procedure W src dst n).labels=43 ∧ (procedure W src dst n).registers=16 ∧
      (procedure W src dst n).slots=0 := by
  change 6+(expression W src dst).labels=43 ∧ 4+(expression W src dst).binds=16 ∧ 0=0
  rw [Term.labels_eq,binds]
  decide

set_option maxHeartbeats 1000000 in
theorem run (src dst n : ℕ) (m : Memory W) (endFit : dst+2*n<2^W)
    (separate : dst+2*n≤ src) (sourceFit : src+n≤2^W) (two : 2<2^W) :
    (procedure W src dst n).Exec m (image src dst n m) (4+56*n) := by
  let word : ℕ → Word W := fun a => (↑((a-dst)%2):Word W)*m (src+(a-dst)/2)
  have cost : 4+2*n*(2*(expression W src dst).binds+4)=4+56*n := by rw [binds];omega
  rw [←cost]
  intro P R K M pc reg pub exit installed data cfg mem start eq
  subst mem
  refine PhysicalInputPhases.writing_spec (expression W src dst) Fin.elim0 dst (2*n) endFit
    (fun input => input=m) word ?_ M pc reg pub exit installed data cfg m start rfl
  intro m₀ init a cur lo hi hold
  change m₀=m at init
  subst m₀
  have dstVal : (dst:Word W).val=dst:=Fin.val_cast_of_lt (by omega)
  have le : (dst:Word W)≤a:=by change (dst:Word W).val≤a.val;rwa [dstVal]
  have diff : (a-(dst:Word W)).val=a.val-dst:=by rw [Fin.sub_val_of_le le,dstVal]
  have small : (2:Word W).val=2:=Fin.val_cast_of_lt two
  have div : BinaryOp.eval .div (a-(dst:Word W)) 2=(((a.val-dst)/2:ℕ):Word W) := by
    change Fin.ofNat _ (_ / _) = _
    rw [diff,small]; rfl
  have modl : BinaryOp.eval .mod (a-(dst:Word W)) 2=(((a.val-dst)%2:ℕ):Word W) := by
    change Fin.ofNat _ (_ % _) = _
    rw [diff,small]; rfl
  have addr : ((src:Word W)+BinaryOp.eval .div (a-(dst:Word W)) 2).val=src+(a.val-dst)/2 := by
    rw [div,←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
  simp only [expression,Term.eval_binary,Term.eval_load,Term.eval_literal]
  change BinaryOp.eval .mod (a-(dst:Word W)) 2 * cur ((src:Word W)+
    BinaryOp.eval .div (a-(dst:Word W)) 2).val=_
  rw [modl,addr,hold _ (.inr (by omega))]

theorem columns (src dst n : ℕ) (m : Memory W) (i : Fin n) :
    image src dst n m (dst+2*i.val)=0 ∧ image src dst n m (dst+2*i.val+1)=m (src+i.val) := by
  have h:=i.isLt
  have even : dst+2*i.val-dst=2*i.val:=by omega
  have odd : dst+2*i.val+1-dst=2*i.val+1:=by omega
  simp only [image,fillSegment,ite_eq_left (show dst≤dst+2*i.val ∧ dst+2*i.val<dst+2*n by omega),
    ite_eq_left (show dst≤dst+2*i.val+1 ∧ dst+2*i.val+1<dst+2*n by omega),even,odd,
    show (2*i.val)%2=0 by omega,show (2*i.val+1)%2=1 by omega,
    show (2*i.val+1)/2=i.val by omega,Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,true_and]

theorem outside (src dst n : ℕ) (m : Memory W) (a : ℕ) (off : a<dst ∨ dst+2*n≤a) :
    image src dst n m a=m a := by simp [image,fillSegment,show ¬(dst≤a ∧ a<dst+2*n) by omega]

end Hierarchy.TraceReceiverOwnerPairs

end OAI
