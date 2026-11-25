import OAI.Hierarchy.DescentGLScoreRAM
import OAI.Hierarchy.DescentGLPermutationRAM

namespace OAI
/-! # Assemble the current common-kernel numerator from previous physical rows -/

namespace Hierarchy.DescentGLInputRAM
open DescentGL DescentWalshTables DescentIntegerScale DescentGLScoreRAM DescentGLPermutationRAM ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section

/-- A program literal for multiplying one difference term by its fixed factor
2^(r−j)−1. The expansion is bounded by the common group size 2^k. -/
def difference (r k : ℕ) (bank : Fin (r+1)→ℕ) : Expr :=
  sumExpr (r+1) fun j=>sumExpr (2^(r-j.val)-1) fun _=>.lookup ⟨bank j,k⟩ .row

def checkZeros : (h : ℕ) → (Fin h→Expr) → Expr → Expr
  | 0,_,body => body
  | h+1,column,body => .branch .eq (column (Fin.last h)) (.lit 0)
      (checkZeros h (fun i=>column i.castSucc) body) (.lit 0)

theorem check_eval {h w : ℕ} (m : Memory w) (x : Word w) (read : Fin h→Expr) (body : Expr) :
    (checkZeros h read body).eval m x =
      if ∀i,(read i).eval m x=0 then body.eval m x else 0 := by
  induction h with
  | zero => simp [checkZeros]
  | succ h ih =>
    simp only [checkZeros,Expr.eval,ih,Comparison.test,beq_iff_eq,Fin.forall_fin_succ']
    split_ifs <;> simp_all

theorem check_fits {h w out : ℕ} (read : Fin h→Expr) (body : Expr)
    (good : ∀i,(read i).Fits w out) (ok : body.Fits w out) : (checkZeros h read body).Fits w out := by
  induction h with
  | zero => exact ok
  | succ h ih => exact ⟨good _,trivial,ih _ (fun i=>good i.castSucc),trivial⟩

theorem check_work {h C : ℕ} (read : Fin h→Expr) (body : Expr)
    (good : ∀i,(read i).work≤C) : (checkZeros h read body).work≤body.work+h*(C+3) := by
  induction h with
  | zero => simp [checkZeros]
  | succ h ih =>
    have fromOld := ih (fun i=>read i.castSucc) (fun i=>good i.castSucc)
    have last := good (Fin.last h)
    simp only [checkZeros,Expr.work,Nat.succ_mul]
    omega

variable {h r : ℕ}
local notation "k" => (h+1+r)
private theorem prefixLe (h r : ℕ) : h≤h+1+r := by omega
local notation "prev" => prefixLe h r

def terms (ptr : Fin k→ℕ) (bank : Fin (r+1)→ℕ) : Expr :=
  .branch .eq .row (.lit 0) (.lit 0)
    (checkZeros h (fun i=>digit ptr (i.castLE prev)) (difference r k bank))

def pass (w out : ℕ) (ptr : Fin k→ℕ) (bank : Fin (r+1)→ℕ) := scan w out (2^k) (terms ptr bank)

theorem terms_work (ptr : Fin k→ℕ) (bank : Fin (r+1)→ℕ) :
    (terms ptr bank).work ≤ 6+(r+1)*(2+8*2^r)+h*(4+2^k*(9+5*2^k)) := by
  have one (j : Fin (r+1)) : (sumExpr (2^(r-j.val)-1)
      (fun _=>Expr.lookup ⟨bank j,k⟩ .row)).work≤1+8*2^r := by
    have a := sumExpr_work (n:=2^(r-j.val)-1) (U:=7) (fun _=>Expr.lookup ⟨bank j,k⟩ .row) (by intro i; change 7≤7; exact le_rfl)
    have pow := Nat.pow_le_pow_right (n:=2) (by decide) (Nat.sub_le r j.val)
    omega
  have diff := sumExpr_work _ one
  have guards := check_work (fun i : Fin h=>digit ptr (i.castLE prev)) (difference r k bank)
    (fun i=>(digit_work ptr (i.castLE prev)).le)
  have body : (difference r k bank).work≤1+(r+1)*(2+8*2^r) := by
    simpa only [difference,show 1+8*2^r+1=2+8*2^r by omega] using diff
  rw [show 1+2^k*(9+5*2^k)+3=4+2^k*(9+5*2^k) by omega] at guards
  change 2+1+1+(checkZeros h (fun i=>digit ptr (i.castLE prev)) (difference r k bank)).work+1≤_
  omega

theorem execute {w out : ℕ} (m : Memory w) (ptr : Fin k→ℕ) (bank : Fin (r+1)→ℕ)
    (large : out+2^k<2^w) (previous : ∀i : Fin h,ptr (i.castLE prev)<out)
    (inputs : ∀j,(Bank.mk (bank j) k).Fits w out) :
    (pass w out ptr bank).Exec m (ProtocolRAM.image out (2^k) (terms ptr bank) m)
      (4+2^k*(2*(terms ptr bank).work+4)) := by
  refine @scan_exec w out (2^k) (terms ptr bank) m ?_ large
  refine ⟨trivial,trivial,trivial,check_fits _ _ (fun i=>digit_fits_single _ _ _
    (by have := Nat.two_pow_pos k;omega) (previous i)) ?_⟩
  exact sumExpr_fits _ (fun j=>sumExpr_fits _ (fun _=>⟨inputs j,trivial⟩))

theorem eval {w : ℕ} (m : Memory w) (ptr : Fin k→ℕ) (bank : Fin (r+1)→ℕ)
    (L : Layout k) (W : Fin (r+1)→DescentGL.Bits k→ℕ) (wide : 2^k<2^w)
    (rows : ∀i : Fin h,m (ptr (i.castLE prev))=
      ((rowIndex k (rowFunctional L (i.castLE prev))).val : Word w))
    (loads : ∀j (z : Fin (2^k)),m (bank j+z.val)=(W j (vec z):Word w)) (z : Fin (2^k)) :
    (terms ptr bank).eval m (z.val:Word w)=((rowInput L W).read (vec z):Word w) := by
  have read (j : Fin (r+1)) : (Expr.lookup ⟨bank j,k⟩ .row).eval m (z.val:Word w)=(W j (vec z):Word w) := by
    simp [Expr.eval,Bank.read,Bank.size,Fin.val_cast_of_lt (z.isLt.trans wide),Nat.mod_eq_of_lt z.isLt,loads]
  have diff : (difference r k bank).eval m (z.val:Word w)=(differenceNumerator r W (vec z):Word w) := by
    simp [difference,sumExpr_eval,read,differenceNumerator,mul_comm]
  have old : (∀i : Fin h,(digit ptr (i.castLE prev)).eval m (z.val:Word w)=0) ↔
      headRows prev (L (vec z))=0 := by
    constructor
    · intro zeroRows
      funext i
      exact (digit_eval_zero_iff ptr (i.castLE prev) m L (rows i) wide.le z).mp (zeroRows i)
    · intro prefixZero i
      apply (digit_eval_zero_iff ptr (i.castLE prev) m L (rows i) wide.le z).mpr
      exact congrFun prefixZero i
  have zero : ((z.val:ℕ):Word w)=0 ↔ vec z=0 := by
    constructor
    · intro hz
      have ord := congrArg Fin.val hz
      rw [Fin.val_cast_of_lt (z.isLt.trans wide)] at ord
      have ix : z=0 := Fin.ext ord
      rw [ix]
      funext i
      apply Fin.ext
      change (0:ℕ)/2^i.val%2=0
      simp
    · intro hz
      have ix : z=finFunctionFinEquiv (0 : DescentGL.Bits k) := by
        rw [←hz]
        exact (finFunctionFinEquiv.apply_symm_apply z).symm
      have ord : z.val=0 := by
        calc
          z.val = (finFunctionFinEquiv (0:DescentGL.Bits k)).val := congrArg Fin.val ix
          _ = ∑i : Fin k,((0:Fin k→Fin 2) i).val*2^i.val :=
            finFunctionFinEquiv_apply (m:=2) (n:=k) _
          _ = 0 := by simp
      simp only [ord,Nat.cast_zero]
  change (if (((z.val:Word w)==0)=true) then 0 else
    (checkZeros h (fun i=>digit ptr (i.castLE prev)) (difference r k bank)).eval m (z.val:Word w))=_
  simp only [beq_iff_eq,zero,check_eval,old,diff,rowInput,Table.tabulate_read]
  by_cases empty : vec z=0
  · simp [empty]
  · by_cases survives : headRows prev (L (vec z))=0 <;> simp [empty,survives]

theorem published {w out : ℕ} (m : Memory w) (ptr : Fin k→ℕ) (bank : Fin (r+1)→ℕ)
    (L : Layout k) (W : Fin (r+1)→DescentGL.Bits k→ℕ) (room : out+2^k<2^w)
    (rows : ∀i : Fin h,m (ptr (i.castLE prev))=
      ((rowIndex k (rowFunctional L (i.castLE prev))).val : Word w))
    (loads : ∀j (z : Fin (2^k)),m (bank j+z.val)=(W j (vec z):Word w)) (z : Fin (2^k)) :
    ProtocolRAM.image out (2^k) (terms ptr bank) m (out+z.val)=((rowInput L W).read (vec z):Word w) := by
  rw [ProtocolRAMGeneratedWrite.read_image out (2^k) (terms ptr bank) m z]
  exact eval m ptr bank L W (by omega) rows loads z

end
end Hierarchy.DescentGLInputRAM

end OAI
