import OAI.Hierarchy.DescentRegisteredOperandFields
import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Packed physical reconstruction of the eleven original edge roles -/
namespace Hierarchy.DescentPackedRawTicket
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {a M w H G : ℕ}

theorem payload_fits {capacity : ℕ} (full : 11*capacity≤2^a) (serial : Fin capacity) (role : Fin 11) :
    11*serial.val+role.val<2^a := by have:=serial.isLt;have:=role.isLt;omega

private theorem digits {b m : ℕ} (v : Fin m→Cell b) :
    (encode b m v).val=∑i,(v i).val*(2^b)^i.val :=finFunctionFinEquiv_apply v

theorem ticket_data (old role : Fin H→Fin G→Cell a) (fits : ∀h g,11*(old h g).val+(role h g).val<2^a) (p : Row H G M) :
    (data (payload old role fits) p).val=11*(data old p).val+(data role p).val := by
  simp only [data,digits,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases alive:p.2.val*M+j.val<G
  · simp only [dite_eq_left alive,payload];ring
  · simp [alive]

def double (x : Expr) : Expr:=.op .add x x

def ticket (old role : Expr) : Expr:=.op .add (.op .add (double (double (double old))) (.op .add (double old) old)) role

theorem ticket_source (old role : Expr) (x r : Fin H→Fin G→Cell a) (mem : Memory w)
    (one : Source old x M mem) (two : Source role r M mem) (fits : ∀h g,11*(x h g).val+(r h g).val<2^a) :
    Source (ticket old role) (payload x r fits) M mem := by
  intro p
  rw [ticket_data]
  simp only [ticket,double,Expr.eval,RowOp.opcode,BinaryOp.eval,one p,two p,Nat.cast_add,Nat.cast_mul]
  ring

theorem issued (B R : Bank) (out : ℕ) (mem : Memory w) (x r : Fin H→Fin G→Cell a)
    (readable : B.Fits w out ∧ R.Fits w out) (capacity : H*chunks G M≤B.size ∧ H*chunks G M≤R.size)
    (read : ∀p : Row H G M,mem (B.base+(row H G M p).val)=((data x p).val:Word w))
    (roles : ∀p : Row H G M,mem (R.base+(row H G M p).val)=((data r p).val:Word w))
    (fits : ∀h g,11*(x h g).val+(r h g).val<2^a) (end_ : out+H*chunks G M<2^w) :
    let e:=ticket (.lookup B .row) (.lookup R .row)
    let after_:=image out (H*chunks G M) e mem
    (scan w out (H*chunks G M) e).Exec mem after_ (4+(H*chunks G M)*194) ∧
      (∀p : Row H G M,after_ (out+(row H G M p).val)=((data (payload x r fits) p).val:Word w)) ∧
      (∀j,j<out ∨ out+H*chunks G M≤j→after_ j=mem j) ∧ CheapCode (scan w out (H*chunks G M) e) := by
  intro e after_
  have old : Source (.lookup B .row) x M mem:=source_column B out readable.1 mem x capacity.1 read
  have spec : Source e (payload x r fits) M mem:=ticket_source _ _ x r mem old (source_column R out readable.2 mem r capacity.2 roles) fits
  have safe : e.Fits w out:=by simp [e,ticket,double,Expr.Fits,readable.1,readable.2]
  have cost : 2*e.work+4=194:=rfl
  refine ⟨?_,fun p=>(ProtocolRAMGeneratedWrite.read_image _ _ _ mem (row H G M p)).trans (spec p),?_,?_⟩
  · rw [←cost];exact scan_exec out _ e mem safe end_
  · intro j hj;exact ProtocolRAMGeneratedWrite.frame_image _ _ _ mem j hj
  · intro P R K pc reg pub exit i;exact scan_cheap w out (H*chunks G M) e pc reg pub exit i

end
end Hierarchy.DescentPackedRawTicket

end OAI
