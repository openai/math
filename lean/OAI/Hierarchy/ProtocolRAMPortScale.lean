import OAI.ThreeFlat.RAM.PhysicalInputPhases
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Static multiplication of a port ordinal using one or two additions per bit -/

namespace Hierarchy.ProtocolRAMPortScale

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM.DescriptorExpr
open scoped Fin.CommRing

variable {w : ℕ}

/-- Local register zero holds the previous partial product and register one the original
ordinal. Doubling binds the result just once, even when a low one-bit also adds the ordinal. -/
def digit (w : ℕ) (one : Bool) : Term w 0 2 :=
  .bind (.binary .add 0 0) (if one then .bind (.binary .add 0 2) (.result 0) else .result 0)

def scale (w : ℕ) : ℕ → ℕ → Term w 0 1
  | 0,_ => .literal 0
  | bits+1,k => (scale w bits (k/2)).letThen (digit w (k%2==1))

private theorem eval_digit (one : Bool) (m : Memory w) (vs : Fin 2→Word w) :
    (digit w one).eval Fin.elim0 m vs = vs 0 + vs 0 + (if one then vs 1 else 0) := by
  cases one <;> simp [digit,Term.eval,Op.eval,BinaryOp.eval,Fin.cons]; rfl

theorem eval_scale (bits k : ℕ) (m : Memory w) (vs : Fin 1→Word w) (fits : k<2^bits) :
    (scale w bits k).eval Fin.elim0 m vs = vs 0*(k:Word w) := by
  induction bits generalizing k with
  | zero =>
    have hz : k=0 := by simp only [pow_zero] at fits; omega
    simp [hz,scale]
  | succ bits ih =>
    have small : k/2<2^bits := by rw [pow_succ] at fits; omega
    simp only [scale,Term.eval_letThen,eval_digit,Fin.cons_zero,Fin.cons_one,ih _ small]
    by_cases h : k%2=1
    · have num : (k:Word w) = ((k/2:ℕ):Word w)+((k/2:ℕ):Word w)+1 := by
        simpa only [Nat.cast_add,Nat.cast_one] using
          congrArg (fun a:ℕ=>(a:Word w)) (show k=k/2+k/2+1 by omega)
      simp only [h,beq_self_eq_true,ite_true]
      conv_rhs => rw [num]
      ring
    · have num : (k:Word w)=((k/2:ℕ):Word w)+((k/2:ℕ):Word w) := by
        simpa only [Nat.cast_add] using congrArg (fun a:ℕ=>(a:Word w))
          (show k=k/2+k/2 by omega)
      simp only [beq_iff_eq,h,ite_false,add_zero]
      conv_rhs => rw [num]
      ring

theorem binds (w bits k : ℕ) : (scale w bits k).binds≤1+2*bits := by
  induction bits generalizing k with
  | zero => exact le_rfl
  | succ bits ih =>
    have d : (digit w (k%2==1)).binds≤2 := by generalize (k%2==1) = b; cases b <;> simp [digit,Term.binds]
    simp only [scale,Term.binds_letThen]
    have := ih (k/2)
    omega

def bitWidth (k : ℕ) := Nat.log 2 k+1

theorem fits (k : ℕ) : k<2^bitWidth k := Nat.lt_pow_succ_log_self (by decide) k


end Hierarchy.ProtocolRAMPortScale

end OAI
