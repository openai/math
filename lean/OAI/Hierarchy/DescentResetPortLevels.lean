import OAI.Hierarchy.DescentResetStencilReaders
import OAI.Hierarchy.DescentResetWalshCutoff
import OAI.Hierarchy.DescentPackedFlowReturn

namespace OAI
/-! # Reading the live host and adjacent selected reset depths -/
namespace Hierarchy.DescentPlainTerminal.Suffix.PortLevels
open DescentPackedColony DescentSIMDLookup DescentPackedZip DescentPackedFlowReturn
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM.DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M D w : ℕ}

def self (C : Index) (depth : Bank) : Expr := .lookup depth (.lookup C.hosts .row)
def other (P : Ports D) (i : Fin D) (depth : Bank) : Expr := .lookup depth (neighborID P i)
def protect (P : Ports D) (H : ℕ) (i : Fin D) (op : Expr) : Expr :=
  .branch .eq (neighborID P i) (.lit H) (.lit 0) op

theorem read_self (C : Index) (depth : Bank) (d : Fin H→ℕ) (mem : Memory w) (out : ℕ)
    (cap : H≤depth.size) (fit : depth.Fits w out) (headers : Header C out mem D H G M)
    (selected : ∀v,mem (depth.base+v.val)=(d v:Word w)) (p : Row H G M) :
    (self C depth).eval mem ((row H G M p).val:Word w)=(d p.1:Word w) := by
  simp only [self,Expr.eval,bank_read _ _ ((row _ _ _ p).isLt.trans_le headers.rows) headers.host,
    headers.self,bank_read _ _ (p.1.isLt.trans_le cap) fit,selected]

theorem peer_id (P : Ports D) (prior : Bank) (out : ℕ) (next : Fin H→Fin D→Option (Fin H))
    (m : Memory w) (fit : Accessible P prior H G M w out) (mounted : Mounted P next m G M)
    (i : Fin D) (p : Row H G M) :
    (neighborID P i).eval m ((row H G M p).val:Word w)=(target (next p.1 i):Word w) := by
  have small : p.1.val*D+i.val<H*D := by
    calc _ < p.1.val*D+D:=Nat.add_lt_add_left i.isLt _
         _ = (p.1.val+1)*D:=(Nat.succ_mul ..).symm
         _ ≤ H*D:=Nat.mul_le_mul_right _ p.1.isLt
  simp only [neighborID,Expr.eval,bank_read _ _ ((row H G M p).isLt.trans_le (fit.idsRoom i)) (fit.ids i),
    mounted.ids,bank_read _ _ (small.trans_le fit.rosterRoom) fit.roster,mounted.roster]

theorem read_neighbor (P : Ports D) (i : Fin D) (depth : Bank) (d : Fin H→ℕ)
    (m : Memory w) (p : Word w) (v : Fin H) (out : ℕ)
    (index : (neighborID P i).eval m p=(v.val:Word w))
    (cap : H≤depth.size) (fit : depth.Fits w out) (selected : ∀v,m (depth.base+v.val)=(d v:Word w)) :
    (other P i depth).eval m p=(d v:Word w) := by
  simp only [other,Expr.eval,index,bank_read _ _ (v.isLt.trans_le cap) fit,selected]

theorem protect_word (P : Ports D) (i : Fin D) (op : Expr) (m : Memory w) (p : Word w) (v : Option (Fin H))
    (value : Fin H→ℕ) (room : H<2^w) (index : (neighborID P i).eval m p=(target v:Word w))
    (word : ∀u,v=some u→ op.eval m p=(value u:Word w)) :
    (protect P H i op).eval m p=(v.elim 0 value:ℕ) := by
  cases v with
  | none=>simp [protect,Expr.eval,index,target,Comparison.test]
  | some u=>
    have live : Comparison.eq.test (u.val:Word w) (H:Word w)=false := by
      simp [Comparison.test,Fin.ext_iff,Fin.val_cast_of_lt (u.isLt.trans room),Fin.val_cast_of_lt room,Nat.ne_of_lt u.isLt]
    simp [protect,Expr.eval,index,target,live,word u rfl]

def relative (c : ℕ) (e : Expr) : Expr := .op .sub e (.lit c)

theorem read_relative (c z : ℕ) (e : Expr) (m : Memory w) (p : Word w) (lower : c≤z)
    (value : e.eval m p=(z:Word w)) : (relative c e).eval m p=(z-c:ℕ) := by
  simp only [relative,Expr.eval,RowOp.opcode,BinaryOp.eval,value,Nat.cast_sub lower]

theorem read_level (left right : Expr) (m : Memory w) (p : Word w) (x y : ℕ)
    (a : left.eval m p=(x:Word w)) (b : right.eval m p=(y:Word w)) (small : max x y<2^w) :
    (Cutoff.level left right).eval m p=(max x y:Word w) := by
  have low: x<2^w := (le_max_left ..).trans_lt small
  have high: y<2^w := (le_max_right ..).trans_lt small
  simp only [Cutoff.level,Expr.eval,a,b,Comparison.test,decide_eq_true_eq,Fin.lt_def,
    Fin.val_cast_of_lt low,Fin.val_cast_of_lt high]
  have word_le (i j : ℕ) (hi : i < 2^w) (hj : j < 2^w) (le : i ≤ j) :
      (i : Word w) ≤ (j : Word w) := by
    change (i : Word w).val ≤ (j : Word w).val
    simpa only [Fin.val_cast_of_lt hi, Fin.val_cast_of_lt hj] using le
  by_cases less : x<y
  · simp only [ite_eq_left less, max_eq_right (word_le x y low high less.le)]
  · simp only [ite_eq_right less, max_eq_left (word_le y x high low (le_of_not_gt less))]

end
end Hierarchy.DescentPlainTerminal.Suffix.PortLevels

end OAI
