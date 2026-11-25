import OAI.Hierarchy.ProtocolRAMDateSpillColumns
import OAI.Hierarchy.ProtocolRAMTurnDirectory

namespace OAI
/-! # Moving an existing public shelf address directory to the next dated output -/
namespace Hierarchy.ProtocolRAM.DateSpill.Relocate
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAMTurnDirectory
open scoped Fin.CommRing

variable {W : ℕ}

def term (rom bits rows oldBase newBase : ℕ) (f : Fin 4) : Expr :=
  let read:=Expr.lookup (bank rom bits f) .row
  if f=1 then
    .branch .lt .row (.lit (rows*5)) (.op .add read (.lit (newBase-oldBase))) (.lit 0)
  else read

def passes (rom dst bits rows oldBase newBase : ℕ) :=
  Columns.passes dst (2^bits) (term rom bits rows oldBase newBase)

theorem entry (rows sites seats oldBase newBase : ℕ) (shift : oldBase≤newBase) (i : ℕ) :
    ProtocolRAMTurnDirectory.words (W:=W) rows sites seats newBase 1 i =
      if i<rows*5 then ProtocolRAMTurnDirectory.words (W:=W) rows sites seats oldBase 1 i+((newBase-oldBase:ℕ):Word W) else 0 := by
  split
  next live=>
    simp only [ProtocolRAMTurnDirectory.words,show (1:Fin 4).val<3 by decide,dite_eq_left,live,
      ProtocolRAMTurnDirectory.fieldWords]
    have add (v : ℕ) : newBase+v=oldBase+v+(newBase-oldBase) := by omega
    simp [add,Nat.cast_add]
  next gone=>simp [ProtocolRAMTurnDirectory.words,gone]

theorem unchanged (rows sites seats oldBase newBase : ℕ) (i : ℕ) (f : Fin 4) (h : f≠1) :
    ProtocolRAMTurnDirectory.words (W:=W) rows sites seats oldBase f i=
    ProtocolRAMTurnDirectory.words rows sites seats newBase f i := by
  fin_cases f <;> simp_all [ProtocolRAMTurnDirectory.words,ProtocolRAMTurnDirectory.fieldWords]

theorem eval (rom bits rows sites seats oldBase newBase : ℕ) (m : Memory W)
    (loaded : ∀f (i : ℕ),i<2^bits→(bank rom bits f).read m (i:Word W)=words rows sites seats oldBase f i)
    (shift : oldBase≤newBase) (word : 2^bits≤2^W) (coding : rows*5<2^W)
    (f : Fin 4) (i : Fin (2^bits)) :
    (term rom bits rows oldBase newBase f).eval m (i.val:Word W)=words rows sites seats newBase f i.val := by
  by_cases moved : f=1
  · subst f
    have small:=i.isLt.trans_le word
    rw [entry rows sites seats oldBase newBase shift]
    have test : DescriptorExpr.Comparison.lt.test (i.val:Word W) ((rows*5:ℕ):Word W) =
        decide (i.val<rows*5) := by
      simp only [DescriptorExpr.Comparison.test,Fin.lt_def,Fin.val_cast_of_lt small,
        Fin.val_cast_of_lt coding]
    change (Expr.branch .lt .row (.lit (rows*5))
      (.op .add (.lookup (bank rom bits 1) .row) (.lit (newBase-oldBase))) (.lit 0)).eval m
        (i.val:Word W)=_
    simp only [Expr.eval,test,decide_eq_true_eq,RowOp.opcode,BinaryOp.eval,Nat.cast_zero,
      loaded _ i.val i.isLt]
  · simpa only [term,ite_eq_right moved,Expr.eval,loaded _ i.val i.isLt] using
      unchanged (W:=W) rows sites seats oldBase newBase i.val f moved

theorem run (rom dst bits rows sites seats oldBase newBase : ℕ) (m : Memory W)
    (loaded : ∀f (i : ℕ),i<2^bits→(bank rom bits f).read m (i:Word W)=words rows sites seats oldBase f i)
    (before : rom+4*2^bits≤dst) (shift : oldBase≤newBase) (coding : rows*5<2^W)
    (room : dst+4*2^bits<2^W) :
    let ps:=passes rom dst bits rows oldBase newBase
    (program W ps).Exec m (result ps m) (clock ps) ∧
      (∀f (i : ℕ),i<2^bits→(bank dst bits f).read (result ps m) (i:Word W)=words rows sites seats newBase f i) ∧
      ∀a,a<dst ∨ dst+4*2^bits≤a→ result ps m a=m a := by
  have cap : 2^bits<2^W := by omega
  have fit (f : Fin 4) : (bank rom bits f).Fits W dst := by
    have le:=Nat.mul_le_mul_right (2^bits) f.isLt
    rw [Nat.succ_mul] at le
    exact ⟨Nat.two_pow_pos _,cap,by change rom+f.val*2^bits+2^bits≤dst;omega⟩
  have safe (f : Fin 4) : (term rom bits rows oldBase newBase f).Fits W dst := by
    by_cases eq : f=1 <;> simp [term,eq,Expr.Fits,fit]
  obtain ⟨exec,read,frame⟩:=Columns.run dst (term rom bits rows oldBase newBase) m safe room
  refine ⟨exec,?_,frame⟩
  intro f i hi
  change result (passes rom dst bits rows oldBase newBase) m (dst+f.val*2^bits+(i:Word W).val%(2^bits))=_
  rw [Fin.val_cast_of_lt (hi.trans cap),Nat.mod_eq_of_lt hi]
  exact (read f ⟨i,hi⟩).trans (eval rom bits rows sites seats oldBase newBase m loaded shift cap.le coding f ⟨i,hi⟩)

end Hierarchy.ProtocolRAM.DateSpill.Relocate

end OAI
