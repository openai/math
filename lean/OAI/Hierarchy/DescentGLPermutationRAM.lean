import OAI.Hierarchy.DescentGLNativeSelection
import OAI.Hierarchy.ProtocolRAMRowChoice
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Native publication of a binary permutation from the selected row words -/

noncomputable section
namespace Hierarchy.DescentGLPermutationRAM

open DescentGL ProtocolRAM Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical BigOperators Fin.CommRing

variable {k w : ℕ}

private abbrev BitSpace (k : ℕ) := Fin k → ZMod 2
private abbrev BinaryLayout (k : ℕ) := BitSpace k ≃ₗ[ZMod 2] BitSpace k

/-- Fix the scalar type before applying the binary-digit equivalence. -/
def binaryCode (k : ℕ) : BitSpace k ≃ Fin (2^k) := finFunctionFinEquiv

private theorem binaryCode_val (y : BitSpace k) : ((binaryCode k) y).val=∑j,(y j).val*2^j.val :=
  finFunctionFinEquiv_apply (m:=2) (n:=k) y

/-- The instruction literals are finite binary dot products on two public indices.
No permutation-specific coefficients enter this table. -/
def weighted (a : Fin k) (r x : Fin (2^k)) : ℕ :=
  let v : BitSpace k := (binaryCode k).symm r
  let y : BitSpace k := (binaryCode k).symm x
  (∑ j, v j*y j : ZMod 2).val * 2^a.val

private theorem weighted_row (a : Fin k) (f : Row k) (x : Fin (2^k)) :
    weighted a (rowIndex k f) x =
      (f ((binaryCode k).symm x)).val*2^a.val := by
  let B := Pi.basisFun (ZMod 2) (Fin k)
  let y : BitSpace k := (binaryCode k).symm x
  have expansion := congrArg f (B.sum_repr y)
  have dot : (∑ j,B.dualBasis.equivFun f j*y j)=f y := by
    simpa only [B,Module.Basis.dualBasis_equivFun,map_sum,map_smul,smul_eq_mul,
      Pi.basisFun_repr,mul_comm] using expansion
  change (∑ j,(((binaryCode k).symm ((binaryCode k) (B.dualBasis.equivFun f))) j : ZMod 2)*y j : ZMod 2).val *
    2^a.val = (f y).val*2^a.val
  rw [Equiv.symm_apply_apply,dot]

private def total : (d : ℕ) → (Fin d → Expr) → Expr
  | 0,_ => .lit 0
  | d+1,f => .op .add (f 0) (total d (fun j => f j.succ))

private theorem eval_total (m : Memory w) (x : Word w) (d : ℕ) (f : Fin d → Expr) :
    (total d f).eval m x = ∑ j,(f j).eval m x := by
  induction d with
  | zero => simp [total,Expr.eval]
  | succ d ih =>
    rw [Fin.sum_univ_succ]
    simp [total,Expr.eval,RowOp.opcode,BinaryOp.eval,ih]

private theorem fits_total (d : ℕ) (f : Fin d → Expr) (out : ℕ) (all : ∀ i,(f i).Fits w out) :
    (total d f).Fits w out := by
  induction d with
  | zero => trivial
  | succ d ih => exact ⟨all 0,ih _ (fun j => all j.succ)⟩

private theorem work_total (d : ℕ) (f : Fin d → Expr) (c : ℕ) (h : ∀ i,(f i).work=c) :
    (total d f).work=1+d*(c+1) := by
  induction d with
  | zero => simp [total,Expr.work]
  | succ d ih =>
    simp only [total,Expr.work,h,ih _ (fun j => h j.succ),Nat.succ_mul]
    omega

theorem fits_choose (d base : ℕ) (which : Expr) (f : Fin d → Expr) {out : ℕ}
    (hi : which.Fits w out) (all : ∀ i,(f i).Fits w out) :
    (chooseField d base f which).Fits w out := by
  induction d generalizing base with
  | zero => trivial
  | succ d ih => exact ⟨hi,trivial,all 0,ih _ _ (fun j => all j.succ)⟩

theorem work_choose (d base : ℕ) (which : Expr) (f : Fin d → Expr) (c : ℕ)
    (h : ∀ i,(f i).work=c) : (chooseField d base f which).work=1+d*(which.work+c+2) := by
  induction d generalizing base with
  | zero => simp [chooseField,Expr.work]
  | succ d ih =>
    simp only [chooseField,Expr.work,h,ih _ _ (fun j=>h j.succ),Nat.succ_mul]
    omega

def rowWord (ptr : Fin k → ℕ) (a : Fin k) : Expr := .lookup ⟨ptr a,0⟩ (.lit 0)

def digit (ptr : Fin k → ℕ) (a : Fin k) : Expr :=
  chooseField (2^k) 0 (fun r =>
    chooseField (2^k) 0 (fun x => .lit (weighted a r x)) .row) (rowWord ptr a)

def expression (ptr : Fin k → ℕ) : Expr := total k (digit ptr)

theorem digit_fits_single (ptr : Fin k → ℕ) (a : Fin k) (out : ℕ)
    (wide : 1<2^w) (below : ptr a<out) : (digit ptr a).Fits w out := by
  apply fits_choose
  · exact ⟨⟨Nat.two_pow_pos _,wide,Nat.succ_le_of_lt below⟩,trivial⟩
  · intro _
    exact fits_choose _ _ _ _ trivial (fun _ => trivial)

theorem fits (ptr : Fin k → ℕ) (out : ℕ) (wide : 1<2^w) (below : ∀a,ptr a<out) :
    (expression ptr).Fits w out :=
  fits_total _ _ _ (fun a => digit_fits_single ptr a out wide (below a))

theorem digit_work (ptr : Fin k → ℕ) (a : Fin k) : (digit ptr a).work=1+2^k*(9+5*2^k) := by
  unfold digit
  rw [work_choose _ _ _ _ (1+5*2^k) (fun r => by
    rw [work_choose _ _ _ _ 1 (fun _ => rfl)]
    simp [Expr.work,Nat.mul_comm])]
  simp [rowWord,Expr.work]
 ; ring

theorem work (ptr : Fin k → ℕ) : (expression ptr).work =
    1+k*(2+2^k*(9+5*2^k)) := by
  rw [expression,work_total _ _ _ (digit_work ptr)]
  ring

def stored (ptr : Fin k → ℕ) (m : Memory w) (μ : BinaryLayout k) : Prop :=
  ∀ a, m (ptr a) = ((rowIndex k (rowFunctional μ a)).val:Word w)

theorem digit_eval_index (ptr : Fin k → ℕ) (a : Fin k) (m : Memory w)
    (r : Fin (2^k)) (atRow : m (ptr a)=(r.val:Word w)) (room : 2^k ≤ 2^w) (x : Fin (2^k)) :
    (digit ptr a).eval m (x.val:Word w) = ((weighted a r x):Word w) := by
  have storedId : ((rowWord ptr a).eval m (x.val:Word w)).val=0+r.val := by
    change (m (ptr a+((0:Word w).val % (2^0)))).val=_
    simp [atRow,Fin.val_cast_of_lt (r.isLt.trans_le room)]
  unfold digit
  rw [eval_chooseField _ _ _ _ _ _ r (by omega) storedId]
  rw [eval_chooseField _ _ _ _ _ _ x (by omega) (by
    change (x.val:Word w).val=0+x.val
    simp [Fin.val_cast_of_lt (x.isLt.trans_le room)])]; rfl

theorem digit_eval_single (ptr : Fin k → ℕ) (a : Fin k) (m : Memory w) (μ : BinaryLayout k)
    (atRow : m (ptr a)=((rowIndex k (rowFunctional μ a)).val:Word w))
    (room : 2^k ≤ 2^w) (x : Fin (2^k)) :
    (digit ptr a).eval m (x.val:Word w) =
      (((μ ((binaryCode k).symm x) a).val*2^a.val : ℕ):Word w) := by
  rw [digit_eval_index ptr a m _ atRow room x,weighted_row,rowFunctional_apply]

theorem digit_eval_zero_iff (ptr : Fin k → ℕ) (a : Fin k) (m : Memory w) (μ : BinaryLayout k)
    (atRow : m (ptr a)=((rowIndex k (rowFunctional μ a)).val:Word w))
    (room : 2^k ≤ 2^w) (x : Fin (2^k)) :
    (digit ptr a).eval m (x.val:Word w)=0 ↔ μ ((binaryCode k).symm x) a=0 := by
  let v := μ ((binaryCode k).symm x) a
  have p : 2^a.val < (2:ℕ)^k := Nat.pow_lt_pow_right (by decide) a.isLt
  have small : v.val*2^a.val < 2^w := by
    have h := ZMod.val_lt v
    have le := Nat.mul_le_mul_right (2^a.val) (show v.val ≤ 1 by omega)
    simp only [one_mul] at le
    exact le.trans_lt (p.trans_le room)
  rw [digit_eval_single ptr a m μ atRow room x,Fin.ext_iff,Fin.val_cast_of_lt small]
  change v.val*2^a.val=0 ↔ v=0
  simp [ZMod.val_eq_zero]

/-- The native program reads the code selected at each previous stage. Its result
is the little-endian numeric word for the entire layout output. -/
theorem eval (ptr : Fin k → ℕ) (m : Memory w) (μ : BinaryLayout k)
    (rows : stored ptr m μ) (room : 2^k ≤ 2^w) (x : Fin (2^k)) :
    (expression ptr).eval m (x.val:Word w) =
      (((binaryCode k) (μ ((binaryCode k).symm x))).val:Word w) := by
  rw [expression,eval_total,binaryCode_val,Nat.cast_sum]
  exact Finset.sum_congr rfl (fun a _ => digit_eval_single ptr a m μ (rows a) room x)

/-- The actual scan clock is cubic in the number of binary vectors and linear
in the number of selected rows. -/
def clock (k : ℕ) := 4+2^k*(2*(1+k*(2+2^k*(9+5*2^k)))+4)

def program (w out : ℕ) (ptr : Fin k → ℕ) := scan w out (2^k) (expression ptr)

def after (out : ℕ) (ptr : Fin k → ℕ) (m : Memory w) := image out (2^k) (expression ptr) m

theorem run (out : ℕ) (ptr : Fin k → ℕ) (m : Memory w)
    (fitsWord : out+2^k < 2^w) (before : ∀a,ptr a<out) :
    (program w out ptr).Exec m (after out ptr m) (clock k) := by
  have wide : 1<2^w := by have := Nat.two_pow_pos k; omega
  intro P R K M pc reg pub exit rom data c mem entry same
  simpa only [program,after,clock,work] using
    scan_exec out (2^k) (expression ptr) m (fits ptr out wide before) fitsWord M pc reg pub exit rom data c mem entry same

theorem read (out : ℕ) (ptr : Fin k → ℕ) (m : Memory w) (μ : BinaryLayout k)
    (rows : stored ptr m μ) (room : 2^k ≤ 2^w) (x : Fin (2^k)) :
    after out ptr m (out+x.val) = (((binaryCode k) (μ ((binaryCode k).symm x))).val:Word w) :=
  (ProtocolRAMGeneratedWrite.read_image out (2^k) (expression ptr) m x).trans (eval ptr m μ rows room x)

theorem frame (out : ℕ) (ptr : Fin k → ℕ) (m : Memory w) (a : ℕ) (outside : a<out ∨ out+2^k≤a) :
    after out ptr m a=m a := by
  exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ outside

end Hierarchy.DescentGLPermutationRAM

end
end OAI
