import OAI.Hierarchy.ProtocolRAMSumScores
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace OAI
/-! # The four native branches of an adaptive attempt -/

namespace Hierarchy.ProtocolRAM.AttemptGate
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing BigOperators

structure Inputs where
  stop : Bank
  excess : Bank
  payload : Bank
  discrepancy : Bank
  injection : Bool
  reserve : Bool

/-- Values zero through three mean respectively no attempted update, advance the
mesh, use the disjoint failed-ball packing, or buy the disjoint sampler chains. -/
def selectMode (injection reserve stop excess payload discrepancy : Bool) : ℕ :=
  if stop then 0 else if reserve then (if discrepancy then 2 else 1)
  else if excess || (injection && payload) then (if discrepancy then 2 else 3) else 1

def nonzero (b : Bank) (yes no : Expr) : Expr := .branch .eq (.lookup b (.lit 0)) (.lit 0) no yes

def bit {w : ℕ} (b : Bank) (m : Memory w) : Bool := decide (b.read m 0≠0)

theorem nonzero_eval {w : ℕ} (b : Bank) (yes no : Expr) (m : Memory w) (r : Word w) :
    (nonzero b yes no).eval m r = if bit b m then yes.eval m r else no.eval m r := by
  by_cases z : b.read m 0=0 <;> simp [nonzero,bit,Expr.eval,Comparison.test,z]

def mode (t : Inputs) : Expr :=
  let choose := nonzero t.discrepancy (.lit 2) (.lit 3)
  nonzero t.stop (.lit 0) (if t.reserve then nonzero t.discrepancy (.lit 2) (.lit 1)
    else nonzero t.excess choose (if t.injection then nonzero t.payload choose (.lit 1) else .lit 1))

def actual {w : ℕ} (t : Inputs) (m : Memory w) :=
  selectMode t.injection t.reserve (bit t.stop m) (bit t.excess m) (bit t.payload m) (bit t.discrepancy m)

theorem mode_eval {w : ℕ} (t : Inputs) (m : Memory w) (r : Word w) :
    (mode t).eval m r=(actual t m : Word w) := by
  cases t with
  | mk stop excess payload disc inject reserve =>
    cases inject <;> cases reserve <;> simp only [mode,actual,selectMode,nonzero_eval,Bool.false_and,
      Bool.true_and,Bool.or_false,Bool.false_eq_true,ite_true,ite_false]
    all_goals split_ifs <;> simp_all [Expr.eval]

def ifMode (t : Inputs) (i : ℕ) (yes no : Expr) := Expr.branch .eq (mode t) (.lit i) yes no

def ifRepair (t : Inputs) := ifMode t 2
def ifPurchase (t : Inputs) := ifMode t 3
def ifAdvance (t : Inputs) := ifMode t 1

def repairMask (t : Inputs) (mis : Expr) := ifRepair t mis (.lit 0)
def purchaseMask (t : Inputs) (picked : Expr) := ifPurchase t picked (.lit 0)

theorem actual_lt {w : ℕ} (t : Inputs) (m : Memory w) : actual t m<4 := by
  unfold actual selectMode
  split_ifs <;> decide

theorem ifMode_eval {w : ℕ} (t : Inputs) (i : ℕ) (yes no : Expr) (m : Memory w) (r : Word w)
    (wide : 4≤2^w) (small : i<4) :
    (ifMode t i yes no).eval m r = if actual t m=i then yes.eval m r else no.eval m r := by
  have same : ((actual t m:ℕ):Word w)=(i:Word w) ↔ actual t m=i := by
    rw [Fin.ext_iff,Fin.val_cast_of_lt ((actual_lt t m).trans_le wide),Fin.val_cast_of_lt (small.trans_le wide)]
  simp only [ifMode,Expr.eval,mode_eval,Comparison.test,beq_iff_eq,same]

theorem exclusive {w : ℕ} (t : Inputs) (mis paths : Expr) (m : Memory w) (r : Word w) (wide : 4≤2^w) :
    (repairMask t mis).eval m r=0 ∨ (purchaseMask t paths).eval m r=0 := by
  by_cases hit : actual t m=2
  · right
    simp only [purchaseMask,ifPurchase,ifMode_eval t 3 _ _ m r wide (by decide),ite_eq_right (show actual t m≠3 by omega),Expr.eval,Nat.cast_zero]
  · left
    simp only [repairMask,ifRepair,ifMode_eval t 2 _ _ m r wide (by decide),ite_eq_right hit,Expr.eval,Nat.cast_zero]

theorem reserve_no_purchase {w : ℕ} (t : Inputs) (m : Memory w) (isReserve : t.reserve=true) :
    actual t m≠3 := by
  unfold actual selectMode
  simp only [isReserve,ite_true]
  split_ifs <;> decide

/-- Padded attempts after the first successful advance perform no second feed or
time change. A saturated outer repair budget switches to the crude remaining route. -/
def closeInterval (t : Inputs) : Expr :=
  ifMode t 0 (.lit 1) (ifAdvance t (.lit 1) (.lit 0))

def latchCrude (global : Bank) (last : Bool) (t : Inputs) : Expr :=
  nonzero global (.lit 1) (if last && !t.reserve then
    ifRepair t (.lit 1) (ifPurchase t (.lit 1) (.lit 0)) else .lit 0)

theorem closeInterval_eval {w : ℕ} (t : Inputs) (m : Memory w) (r : Word w) (wide : 4≤2^w) :
    (closeInterval t).eval m r = if actual t m=0 ∨ actual t m=1 then 1 else 0 := by
  rw [closeInterval,ifAdvance,ifMode_eval t 0 _ _ m r wide (by decide),ifMode_eval t 1 _ _ m r wide (by decide)]
  by_cases zero : actual t m=0 <;> by_cases one : actual t m=1 <;> simp [zero,one,Expr.eval]

theorem latchCrude_eval {w : ℕ} (global : Bank) (last : Bool) (t : Inputs)
    (m : Memory w) (r : Word w) (wide : 4≤2^w) :
    (latchCrude global last t).eval m r =
    if bit global m=true ∨ (last=true ∧ t.reserve=false ∧ (actual t m=2 ∨ actual t m=3)) then 1 else 0 := by
  cases last <;> cases reserve : t.reserve <;> cases globalFlag : bit global m <;>
    by_cases failed : actual t m=2 <;> by_cases bought : actual t m=3 <;>
    simp [latchCrude,nonzero_eval,reserve,globalFlag,ifRepair,ifPurchase,
      ifMode_eval t 2 _ _ m r wide (by decide),ifMode_eval t 3 _ _ m r wide (by decide),failed,bought,Expr.eval]

/-- One threshold word is exactly the comparison produced by the native cumulative
scan; no information about the terminal control is taken as advice. -/
theorem threshold_bit {w n : ℕ} (out bound : ℕ) (score : Fin n→ℕ) (m : Memory w)
    (wide : 0<w) :
    bit ⟨out+n,0⟩ (fillSegment out (n+1) (SumScores.word out bound score) m) =
      decide (bound≤∑ i,score i) := by
  have inside : out≤out+n ∧ out+n<out+(n+1) := by omega
  have nz : (1:Word w)≠0 := by
    intro h
    have eqn := congrArg Fin.val h
    rw [show (1:Word w).val=1 from Fin.val_cast_of_lt (Nat.one_lt_two_pow wide.ne')] at eqn
    exact Nat.one_ne_zero eqn
  simp [bit,Bank.read,fillSegment,inside,SumScores.word,nz]

/-- With nonnegative scores, a downward-rounded row word errs by less than one.
A rational threshold is rounded upwards only once, after summation over the rows. -/
theorem threshold_bounds {n : ℕ} (value : Fin n → ℝ) (pos : ∀i,0≤value i) (Q : ℕ) (qpos : 0<Q)
    (threshold : ℝ) (_nonnegative : 0≤threshold) :
    let score := fun i=>⌊(Q:ℝ)*value i⌋₊
    let bound := ⌈(Q:ℝ)*threshold⌉₊
    (bound ≤ ∑ i,score i → threshold ≤ ∑ i,value i) ∧
      (¬bound ≤ ∑ i,score i → ∑ i,value i ≤ threshold+(n:ℝ)/Q) := by
  let score (i : Fin n) := ⌊(Q:ℝ)*value i⌋₊
  let bound := ⌈(Q:ℝ)*threshold⌉₊
  have low : (∑i,(score i:ℝ))≤(Q:ℝ)*(∑i,value i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _=>Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (pos i))
  have high : (Q:ℝ)*(∑i,value i) ≤ (∑i,(score i:ℝ))+n := by
    rw [Finset.mul_sum]
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_one] using
      (Finset.sum_le_sum (s:=Finset.univ) fun i _ => (Nat.lt_floor_add_one ((Q:ℝ)*value i)).le)
  have qreal : (0:ℝ)<Q := by exact_mod_cast qpos
  constructor
  · intro hit
    have sufficient : (Q:ℝ)*threshold ≤ (∑ i,score i:ℕ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hit)
    rw [Nat.cast_sum] at sufficient
    exact (mul_le_mul_iff_of_pos_left qreal).mp (sufficient.trans low)
  · intro missed
    have hb : (∑i,score i:ℕ) < bound := Nat.lt_of_not_ge missed
    have loose : (∑i,(score i:ℝ)) < (Q:ℝ)*threshold := by
      rw [←Nat.cast_sum]
      exact Nat.lt_ceil.mp hb
    apply (mul_le_mul_iff_of_pos_left qreal).mp
    rw [mul_add,show (Q:ℝ)*((n:ℝ)/Q)=n by field_simp]
    linarith

end Hierarchy.ProtocolRAM.AttemptGate

end OAI
