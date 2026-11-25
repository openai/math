import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentTerminalHeaderPrefixRAM

namespace OAI
/-! # Count the real matching pairs from the retained topology words -/
namespace Hierarchy.DescentOrdinaryCountScan
open DescentSIMDLookup ProtocolRAM DescentPackedZip
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing BigOperators
noncomputable section
variable {w b : ℕ}
def table (b base : ℕ) : Bank:=⟨base,b⟩
def out (b base : ℕ) := base+2^b
def endAddress (b base n : ℕ) := out b base+n+1
def address (b base n : ℕ) := out b base+n
def body (src : Bank) (b base n : ℕ) : Expr :=
  .branch .eq .row (.lit n) (.lit 0) (.lookup (table b base) (.lookup src .row))
def literal (f : Cell b→ℕ) (i : ℕ) := f ⟨i%2^b,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
def prepared (f : Cell b→ℕ) (base : ℕ) (m : Memory w) := DescentStaticWordColumn.image base (literal f) m (2^b)
def program (w : ℕ) (src : Bank) (f : Cell b→ℕ) (base n : ℕ) :=
  (DescentStaticWordColumn.program w base (literal f) (2^b)).seq
    (DescentTerminalHeaderPrefixRAM.program w (out b base) (n+1) .add (body src b base n))
def prefix_ (src : Bank) (base n : ℕ) (f : Cell b→ℕ) (m : Memory w) (k : ℕ) : Word w :=
  ∑i∈Finset.range k,(body src b base n).eval (prepared f base m) (i:Word w)
def output (src : Bank) (f : Cell b→ℕ) (base n : ℕ) (m : Memory w) :=
  fillSegment (out b base) (n+1) (DescentTerminalHeaderPrefixRAM.file (out b base) (prefix_ src base n f m)) (prepared f base m)
def clock (b n : ℕ) := 4+10*2^b+(4+(n+1)*52)

theorem run (src : Bank) (f : Cell b→ℕ) (base n : ℕ) (m : Memory w) (prior : src.Fits w base)
    (room : endAddress b base n<2^w) : (program w src f base n).Exec m (output src f base n m) (clock b n) ∧
      (∀x,x<base ∨ endAddress b base n≤x→ output src f base n m x=m x) :=by
  have low : base≤out b base:=Nat.le_add_right ..
  have high : out b base<2^w:=(show out b base≤endAddress b base n by unfold endAddress;omega).trans_lt room
  have tFit : (table b base).Fits w (out b base):=⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt high,le_rfl⟩
  have bFit : (body src b base n).Fits w (out b base):=⟨trivial,trivial,trivial,tFit,⟨prior.1,prior.2.1,prior.2.2.trans low⟩,trivial⟩
  have init : (DescentStaticWordColumn.program w base (literal f) (2^b)).Exec m (prepared f base m) (4+10*2^b):=DescentStaticWordColumn.mount base (2^b) (literal f) m high
  have sum : (DescentTerminalHeaderPrefixRAM.program w (out b base) (n+1) .add (body src b base n)).Exec (prepared f base m) (output src f base n m) (4+(n+1)*52):=DescentTerminalHeaderPrefixRAM.spec (out b base) .add (body src b base n) (prepared f base m)
    (prefix_ src base n f m) trivial bFit (n:=n+1) (by simpa [endAddress,Nat.add_assoc] using room)
    (by simp [prefix_]) (fun i=>by simp [prefix_,Finset.sum_range_succ,DescentTerminalHeaderPrefixRAM.value])
  refine ⟨?_,?_⟩
  · intro P R K machine
    exact Procedure.Exec.then init sum machine
  · intro x away
    have outside : ¬(out b base≤x ∧ x<out b base+(n+1)):=by unfold endAddress at away;omega
    simpa [output,fillSegment,outside,prepared] using DescentStaticWordColumn.frame base (2^b) (literal f) m x
      (away.imp_right (fun hi=>(show base+2^b≤endAddress b base n by unfold endAddress out;omega).trans hi))

theorem read (src : Bank) (f : Cell b→ℕ) (base n : ℕ) (m : Memory w) (actual : Fin n→Cell b)
    (prior : src.Fits w base) (rows : n≤ src.size)
    (data_ : ∀i,m (src.base+i.val)=((actual i).val:Word w)) (room : endAddress b base n<2^w) :
    output src f base n m (address b base n) = ((∑i : Fin n, f (actual i)):Word w) :=by
  have nFit : n<2^w:=rows.trans_lt prior.2.1
  have lookup (i : Fin n) : (body src b base n).eval (prepared f base m) (i.val:Word w)=(f (actual i):Word w) :=by
    have neq : (i.val:Word w)≠(n:Word w):=by
      intro h
      have eqn:=congrArg Fin.val h
      rw [Fin.val_cast_of_lt (i.isLt.trans nFit),Fin.val_cast_of_lt nFit] at eqn
      exact i.isLt.ne eqn
    have tSmall : 2^b<2^w:=by unfold endAddress out at room;omega
    have tFit : (table b base).Fits w (out b base):=⟨Nat.two_pow_pos _,tSmall,le_rfl⟩
    have old:=(bank_read src (prepared f base m) (i.isLt.trans_le rows) prior).trans
      ((DescentStaticWordColumn.frame base (2^b) (literal f) m _
        (Or.inl ((Nat.add_lt_add_left (i.isLt.trans_le rows) _).trans_le prior.2.2))).trans (data_ i))
    simp only [body,Expr.eval,Comparison.test,beq_iff_eq,neq,ite_false,old]
    rw [bank_read _ _ (actual i).isLt tFit]
    simpa [table,prepared,literal,Nat.mod_eq_of_lt (actual i).isLt] using
      DescentStaticWordColumn.read base (2^b) (literal f) m (actual i).isLt
  have emit:=DescentTerminalHeaderPrefixRAM.at_row (out b base) (prefix_ src base n f m) (prepared f base m) (Fin.last n)
  rw [show address b base n=out b base+(Fin.last n).val from rfl]
  refine emit.trans ?_
  simp only [Fin.val_last,prefix_,Finset.sum_range_succ,body,Expr.eval,Comparison.test,beq_self_eq_true,ite_true,Nat.cast_zero,add_zero]
  rw [←Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun i _=>lookup i)

theorem hardware (w : ℕ) (src : Bank) (f : Cell b→ℕ) (base n : ℕ) :
    CheapCode (program w src f base n) ∧ DescentStaticWordColumn.names (program w src f base n)=
      15*(2^b+1)+107 :=by
  constructor
  · unfold program; apply cheap_seq
    · apply DescentStaticWordColumn.cheap
    · apply DescentTerminalHeaderPrefixRAM.cheap
  · have score : DescentStaticWordColumn.names (DescentTerminalHeaderPrefixRAM.program w
        (out b base) (n+1) .add (body src b base n))=107 :=by
      simp only [DescentStaticWordColumn.names,DescentTerminalHeaderPrefixRAM.program,
        PhysicalInputPhases.writing,Term.labels_eq,DescentTerminalHeaderPrefixRAM.binds,
        DescentTerminalHeaderPrefixRAM.work,body,Expr.work]
    rw [program,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount,score]

end
end Hierarchy.DescentOrdinaryCountScan

end OAI
