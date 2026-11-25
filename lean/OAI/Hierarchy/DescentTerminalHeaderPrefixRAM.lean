import OAI.Hierarchy.ProtocolRAMSumScores
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Cheap native scans carrying one prior word of state -/

namespace Hierarchy.DescentTerminalHeaderPrefixRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Fin.CommRing

inductive Op where
  | add
  | read (bank : Bank)

def step (bits out : ℕ) (op : Op) (rowExpr : Expr) : SumScores.T bits :=
  let index:=Term.binary .add (SumScores.prior bits out) (rowExpr.compile bits out)
  match op with
  | .add=>index
  | .read b=>.load (.binary .add (.literal b.base) (.binary .bitAnd index (.literal (b.size-1))))

def value {bits : ℕ} (op : Op) (m : Memory bits) (a b : Word bits) : Word bits :=
  match op with
  | .add=>a+b
  | .read bank=>bank.read m (a+b)

def Fits (op : Op) (bits out : ℕ) : Prop := match op with
  | .add=>True
  | .read bank=>bank.Fits bits out

def program (bits out n : ℕ) (op : Op) (rowExpr : Expr) :=
  PhysicalInputPhases.writing (step bits out op rowExpr) Fin.elim0 out n

theorem cheap (bits out n : ℕ) (op : Op) (rowExpr : Expr) :
    CheapCode (program bits out n op rowExpr) := by
  apply writing_cheap
  cases op <;> simp [step,SumScores.prior,Term.select,Term.binary,Term.load,Term.literal,
    admissible_let,admissible_rename,admissible,opAllowed,allowed,good_compile]

def work (op : Op) (rowExpr : Expr) := rowExpr.work + (match op with | .add=>7 | .read _=>12)

theorem binds (bits out : ℕ) (op : Op) (rowExpr : Expr) :
    (step bits out op rowExpr).binds=work op rowExpr := by
  cases op <;> simp [step,work,SumScores.prior,Term.select,Term.binary,Term.load,Term.literal,
    Term.binds_letThen,Term.binds_rename,Term.binds] <;> omega

def file {bits : ℕ} (out : ℕ) (state : ℕ→Word bits) (addr : ℕ) := state (addr-out+1)

theorem prior_read {bits out n : ℕ} (state : ℕ→Word bits) (m : Memory bits) (a : Word bits)
    (lo : out ≤ a.val) (_hi : a.val<out+n) (_endAt : out+n<2^bits) (start : state 0=0) :
    (SumScores.prior bits out).eval Fin.elim0 (fillSegment out (a.val-out) (file out state) m) (fun _=>a)=
      state (a.val-out) := by
  let k:=a.val-out
  have near : out+k=a.val := Nat.add_sub_of_le lo
  have aval : ((out+k:ℕ):Word bits)=a := by rw [near];exact Fin.cast_val_eq_self _
  have initial : a=(out:Word bits) ↔ k=0 := by
    rw [Fin.ext_iff,Fin.val_cast_of_lt (show out<2^bits by omega)]
    omega
  simp only [SumScores.prior,Term.eval_select,Term.eval_literal,Term.eval_load,Term.eval_binary,
    BinaryOp.eval,Comparison.test,beq_iff_eq]
  change (if a=(out:Word bits) then 0 else (fillSegment out k (file out state) m) (a-1).val)=state k
  cases hk : k with
  | zero=>simp [initial.mpr hk,start]
  | succ j=>
    have ne : a≠(out:Word bits) := by intro h;have:=initial.mp h;omega
    have before : a-1=((out+j:ℕ):Word bits) := by rw [←aval,hk,Nat.add_succ,Nat.cast_succ];abel
    simp only [ite_eq_right ne,before,Fin.val_cast_of_lt (show out+j<2^bits by omega),fillSegment,file]
    simp

private theorem read_index {bits out : ℕ} (bank : Bank) (fit : bank.Fits bits out) (room : out<2^bits)
    (m : Memory bits) (j : Word bits) :
    m (BinaryOp.add.eval (bank.base:Word bits)
      (BinaryOp.bitAnd.eval j ((bank.size-1:ℕ):Word bits))).val=bank.read m j := by
  obtain ⟨pos,small,last⟩:=fit
  have mask : bank.size-1<2^bits := by omega
  have bound : bank.base+j.val%bank.size<2^bits := by
    have h:=Nat.mod_lt j.val pos;omega
  simp only [BinaryOp.eval,Fin.val_cast_of_lt mask,Bank.read]
  rw [show j.val &&& (bank.size-1)=j.val%bank.size from Nat.and_two_pow_sub_one_eq_mod _ _]
  change m ((bank.base:Word bits)+((j.val%bank.size:ℕ):Word bits)).val=_
  rw [←Nat.cast_add,Fin.val_cast_of_lt bound]

theorem spec {bits n : ℕ} (out : ℕ) (op : Op) (rowExpr : Expr) (m : Memory bits) (state : ℕ→Word bits)
    (ofit : Fits op bits out) (rfit : rowExpr.Fits bits out) (endAt : out+n<2^bits) (start : state 0=0)
    (next : ∀i : Fin n,value op m (state i.val) (rowExpr.eval m (i.val:Word bits))=state (i.val+1)) :
    (program bits out n op rowExpr).Exec m (fillSegment out n (file out state) m)
      (4+n*(2*work op rowExpr+4)) := by
  rw [←binds bits out op rowExpr]
  intro P R K M pc reg pub exit installed data cfg orig begin eq
  subst orig
  apply SumScores.writing_prefix (step bits out op rowExpr) out n endAt (·=m) (fun _=>file out state)
    ?_ M pc reg pub exit installed data cfg m begin rfl
  intro old same a lo hi
  subst old
  let i : Fin n:=⟨a.val-out,by omega⟩
  let mem:=fillSegment out i.val (file out state) m
  have diff : a-(out:Word bits)=(i.val:Word bits) := by
    conv_lhs=>rw [←Fin.cast_val_eq_self a]
    exact (Nat.cast_sub (R:=Word bits) lo).symm
  have prev := prior_read state m a lo hi endAt start
  have expr : (rowExpr.compile bits out).eval Fin.elim0 mem (fun _=>a)=rowExpr.eval m (i.val:Word bits) := by
    rw [eval_compile _ _ _ rfit (by omega),diff]
    exact eval_below rowExpr _ m mem rfit (by intro j h;simp [mem,fillSegment,not_le.mpr h])
  change (step bits out op rowExpr).eval Fin.elim0 mem (fun _=>a)=state (i.val+1)
  cases op with
  | add=>
    change (Term.binary .add (SumScores.prior bits out) (rowExpr.compile bits out)).eval Fin.elim0 mem (fun _=>a)=_
    rw [Term.eval_binary,prev,expr]
    exact next i
  | read bank=>
    have low : ∀j,bank.read mem j=bank.read m j := by
      intro v
      have f : bank.Fits bits out:=ofit
      have bounds:=Nat.mod_lt v.val f.1
      have ends:=f.2.2
      have before : bank.base+v.val%bank.size<out := by omega
      simp [Bank.read,mem,fillSegment,not_le.mpr before]
    have prev' : (SumScores.prior bits out).eval Fin.elim0 mem (fun _=>a)=state i.val:=prev
    simp only [step,Term.eval_load,Term.eval_binary,Term.eval_literal,prev',expr]
    have bankBound : bank.Fits bits out:=ofit
    have mask : (bank.size:Word bits)-1=((bank.size-1:ℕ):Word bits):=by
      simpa using (Nat.cast_sub (R:=Word bits) (show 1≤bank.size from bankBound.1)).symm
    rw [mask]
    change mem (BinaryOp.add.eval (bank.base:Word bits) (BinaryOp.bitAnd.eval (state i.val+rowExpr.eval m (i.val:Word bits))
      ((bank.size-1:ℕ):Word bits))).val=_
    rw [read_index bank ofit (by omega) mem (state i.val+rowExpr.eval m (i.val:Word bits)),low]
    exact next i

theorem at_row {bits n : ℕ} (out : ℕ) (state : ℕ→Word bits) (m : Memory bits) (i : Fin n) :
    fillSegment out n (file out state) m (out+i.val)=state (i.val+1) := by
  simp [fillSegment,file,show out+i.val<out+n by omega]

end Hierarchy.DescentTerminalHeaderPrefixRAM

end OAI
