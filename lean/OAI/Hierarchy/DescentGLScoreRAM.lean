import OAI.Hierarchy.DescentIndexedRowChoice
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Physical RAM words for all candidate Walsh kernel sums -/

namespace Hierarchy.DescentGLScoreRAM
open DescentGL DescentWalshTables DescentIntegerScale ProtocolRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Fin.CommRing Classical
noncomputable section

/-- Static matrix entries are small opcode literals. The dynamic input is
the current integral difference table in the preceding RAM bank. -/
def lookupRow : (n : ℕ) → (Fin n → ℕ) → Expr
  | 0,_ => .lit 0
  | n+1,f => .branch .eq .row (.lit n) (.lit (f (Fin.last n)))
      (lookupRow n (fun i=>f i.castSucc))

theorem lookupRow_eval {w n : ℕ} (m : Memory w) (f : Fin n→ℕ) (size : n≤2^w) (i : Fin n) :
    (lookupRow n f).eval m (i.val:Word w)=(f i : Word w) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp [lookupRow,Expr.eval,Comparison.test]
    · have ne : ((j.val:ℕ):Word w)≠(n:Word w) := by
        intro eqn
        have vals := congrArg Fin.val eqn
        simp only [Fin.val_cast_of_lt (by omega : n<2^w),
          Fin.val_cast_of_lt (by omega : j.val<2^w)] at vals
        omega
      simp [lookupRow,Expr.eval,Comparison.test,ne,ih _ (by omega)]

theorem lookupRow_fits (w out n : ℕ) (f : Fin n→ℕ) : (lookupRow n f).Fits w out := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨trivial,trivial,trivial,ih _⟩

theorem lookupRow_work (n : ℕ) (f : Fin n→ℕ) : (lookupRow n f).work=5*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [lookupRow,Expr.work,ih];omega

def sumExpr : (n : ℕ) → (Fin n→Expr) → Expr
  | 0,_ => .lit 0
  | n+1,f => .op .add (sumExpr n (fun i=>f i.castSucc)) (f (Fin.last n))

theorem sumExpr_eval {w : ℕ} (m : Memory w) (row : Word w) (n : ℕ) (f : Fin n→Expr) :
    (sumExpr n f).eval m row=∑i,(f i).eval m row := by
  induction n with
  | zero => simp [sumExpr,Expr.eval]
  | succ n ih => rw [Fin.sum_univ_castSucc];simp [sumExpr,Expr.eval,RowOp.opcode,BinaryOp.eval,ih]

theorem sumExpr_work {n U : ℕ} (f : Fin n→Expr) (bound : ∀i,(f i).work≤U) :
    (sumExpr n f).work≤1+n*(U+1) := by
  induction n with
  | zero => simp [sumExpr,Expr.work]
  | succ n ih =>
    have before := ih (fun i=>f i.castSucc) (fun i=>bound i.castSucc)
    have last := bound (Fin.last n)
    simp only [sumExpr,Expr.work,Nat.succ_mul]
    omega

theorem sumExpr_fits {w out n : ℕ} (f : Fin n→Expr) (fit : ∀i,(f i).Fits w out) :
    (sumExpr n f).Fits w out := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih _ (fun i=>fit i.castSucc),fit _⟩

abbrev vec {k : ℕ} (i : Fin (2^k)) : DescentGL.Bits k := finFunctionFinEquiv.symm i

def coefficient {k : ℕ} (i d : Fin (2^k)) : ℕ := if binaryRow (vec i) (vec d)=0 then 1 else 0

def summand (k base : ℕ) (d : Fin (2^k)) : Expr :=
  .branch .eq (lookupRow (2^k) (fun i=>coefficient i d)) (.lit 1)
    (.lookup ⟨base,k⟩ (.lit d.val)) (.lit 0)

def score (k base : ℕ) : Expr :=
  let half := sumExpr (2^k) (summand k base)
  .op .add half half

theorem score_work (k base : ℕ) : (score k base).work≤3+2*2^k*(5*2^k+11) := by
  have one (d : Fin (2^k)) : (summand k base d).work≤5*2^k+10 := by
    simp [summand,Expr.work,lookupRow_work]
  have all := sumExpr_work (summand k base) one
  dsimp [score,Expr.work]
  nlinarith only [all]

theorem score_fits {w out k base : ℕ} (fit : (Bank.mk base k).Fits w out) :
    (score k base).Fits w out := by
  have one (d : Fin (2^k)) : (summand k base d).Fits w out :=
    ⟨lookupRow_fits ..,trivial,⟨fit,trivial⟩,trivial⟩
  exact ⟨sumExpr_fits _ one,sumExpr_fits _ one⟩

def program (w out k base : ℕ) := scan w out (2^k) (score k base)

theorem run {w out k base : ℕ} (m : Memory w) (fit : (Bank.mk base k).Fits w out)
    (room : out+2^k<2^w) :
    (program w out k base).Exec m (image out (2^k) (score k base) m)
      (4+2^k*(2*(score k base).work+4)) :=
  scan_exec out _ _ m (score_fits fit) room

theorem work (k base : ℕ) :
    4+2^k*(2*(score k base).work+4)≤4+2^k*(10+4*2^k*(5*2^k+11)) := by
  have cap := score_work k base
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  nlinarith only [cap]

/-- All native words are interpreted in the signed residue ring here. The
actual row input below is nonnegative, allowing the usual unsigned ordering. -/
theorem score_eval {w k base : ℕ} (m : Memory w) (t : Table ℤ k)
    (room : 2^k<2^w)
    (source : ∀d : Fin (2^k),m (base+d.val)=(t.read (vec d):Word w))
    (i : Fin (2^k)) :
    (score k base).eval m (i.val:Word w)=((scoreRows t).1.read (vec i):Word w) := by
  have wordTwo : 1<2^w := (show 1≤2^k from Nat.two_pow_pos k).trans_lt room
  have one (d : Fin (2^k)) :
      (summand k base d).eval m (i.val:Word w)=
        if binaryRow (vec i) (vec d)=0 then (t.read (vec d):Word w) else 0 := by
    have small := d.isLt.trans room
    have notzero : (1 : Word w)≠0 := by
      intro eqn
      have vals := congrArg Fin.val eqn
      change (((1:ℕ):Word w).val)=((0:Word w).val) at vals
      rw [Fin.val_cast_of_lt wordTwo] at vals
      exact Nat.one_ne_zero vals
    by_cases yes : binaryRow (vec i) (vec d)=0 <;>
      simp [summand,Expr.eval,lookupRow_eval m _ room.le i,coefficient,yes,
        Comparison.test,Bank.read,Bank.size,Fin.val_cast_of_lt small,
        Nat.mod_eq_of_lt d.isLt,source,Ne.symm notzero]
  rw [scoreRows_read,Finset.sum_filter,Int.cast_mul,Int.cast_sum]
  simp only [score,Expr.eval,RowOp.opcode,BinaryOp.eval,sumExpr_eval,one]
  have names := finFunctionFinEquiv.symm.sum_comp (fun d : DescentGL.Bits k=>
    if binaryRow (vec i) d=0 then (t.read d:Word w) else 0)
  simp only [Int.cast_ite,Int.cast_zero]
  change _+_=_*_
  rw [←two_mul]
  convert congrArg (fun z : Word w=>2*z) names using 1; norm_num
  congr 1

theorem published {w out k base : ℕ} (m : Memory w) (t : Table ℤ k)
    (room : out+2^k<2^w) (source : ∀d : Fin (2^k),m (base+d.val)=(t.read (vec d):Word w))
    (i : Fin (2^k)) :
    image out (2^k) (score k base) m (out+i.val)=((scoreRows t).1.read (vec i):Word w) := by
  simpa [ProtocolRAM.image,fillSegment,Nat.add_lt_add_left i.isLt, Nat.cast_add] using
    score_eval m t (by omega : 2^k<2^w) source i

theorem order_read {w out h r base : ℕ} (m : Memory w) (L : Layout ((h+1)+r))
    (W : Fin (r+1)→DescentGL.Bits ((h+1)+r)→ℕ) (room : out+2^((h+1)+r)<2^w)
    (source : ∀d : Fin (2^((h+1)+r)),m (base+d.val)=((rowInput L W).read (vec d):Word w))
    (small : ∀i : Fin (2^((h+1)+r)),2*rowNumerator r W (surviving L ((rowIndex _).symm i))<2^w)
    (i : Fin (2^((h+1)+r))) :
    (image out (2^((h+1)+r)) (score ((h+1)+r) base) m (out+i.val)).val=
      2*rowNumerator r W (surviving L ((rowIndex _).symm i)) := by
  rw [published m (rowInput L W) room source i,scoreRows_indexed]
  simpa using Fin.val_cast_of_lt (a:=2*rowNumerator r W (surviving L ((rowIndex _).symm i))) (small i)

end
end Hierarchy.DescentGLScoreRAM

end OAI
