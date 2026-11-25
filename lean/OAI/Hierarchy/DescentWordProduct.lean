import OAI.Hierarchy.ProtocolRAMPortScale
import OAI.Hierarchy.ProtocolRAMCheapCode
import Mathlib.Data.Nat.Bitwise

namespace OAI
/-! # Multiplying two measured words with additions, lookup-free masks and branches -/

namespace Hierarchy.DescentWordProduct
open ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing

def component (w j : ℕ) : Term w 0 2 :=
  .select .eq (.binary .bitAnd (.result 1) (.literal ((2^j:ℕ):Word w))) (.literal 0)
    (.literal 0) ((ProtocolRAMPortScale.scale w (j+1) (2^j)).rename (fun _=>0))

def product (w : ℕ) : ℕ→Term w 0 2
  | 0 => .literal 0
  | j+1 => .binary .add (product w j) (component w j)

theorem bitTest {w j : ℕ} (y : Word w) (within : j<w) :
    BinaryOp.bitAnd.eval y ((2^j:ℕ):Word w)=0 ↔ y.val/2^j%2=0 := by
  have fit : 2^j<2^w := Nat.pow_lt_pow_right (by decide) within
  change (((y.val &&& ((2^j:ℕ):Word w).val):ℕ):Word w)=0 ↔ _
  rw [Fin.val_cast_of_lt fit,Nat.and_two_pow,Nat.testBit_eq_decide_div_mod_eq]
  have two := Nat.mod_lt (y.val/2^j) (by decide : 0<2)
  by_cases one : y.val/2^j%2=1
  · have ne : ((2^j:ℕ):Word w)≠0 := by
      intro e
      have vals := congrArg Fin.val e
      rw [Fin.val_cast_of_lt fit] at vals
      exact (Nat.two_pow_pos j).ne' vals
    simpa only [one,decide_true,ite_true,Nat.one_ne_zero,iff_false,Bool.toNat_true,one_mul] using ne
  · have zero : y.val/2^j%2=0 := by omega
    simp [zero]

theorem component_eval {w j : ℕ} (m : Memory w) (v : Fin 2→Word w) (within : j<w) :
    (component w j).eval Fin.elim0 m v=
      v 0*(((2^j)*((v 1).val/2^j%2):ℕ):Word w) := by
  have p : 2^j<2^(j+1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self j)
  simp only [component,Term.eval_select,Term.eval_binary,Term.eval_literal,Term.eval,
    Comparison.test,Term.eval_rename,ProtocolRAMPortScale.eval_scale _ _ _ _ p]
  by_cases bit : (v 1).val/2^j%2=0
  · have detected : BinaryOp.bitAnd.eval (v 1) ((2^j:ℕ):Word w)=0 := (bitTest _ within).2 bit
    simpa [bit,←Nat.cast_pow] using (show (if BinaryOp.bitAnd.eval (v 1) ((2^j:ℕ):Word w)=0
        then 0 else (v 0)*((2^j:ℕ):Word w))=0 by rw [ite_eq_left detected])
  · have one : (v 1).val/2^j%2=1 := by omega
    have detected : BinaryOp.bitAnd.eval (v 1) ((2^j:ℕ):Word w)≠0 := fun h=>bit ((bitTest _ within).1 h)
    simpa [one,←Nat.cast_pow] using (show (if BinaryOp.bitAnd.eval (v 1) ((2^j:ℕ):Word w)=0
        then 0 else (v 0)*((2^j:ℕ):Word w))=(v 0)*((2^j:ℕ):Word w) by rw [ite_eq_right detected])

theorem product_eval {w : ℕ} (m : Memory w) (v : Fin 2→Word w) (n : ℕ) (size : n≤w) :
    (product w n).eval Fin.elim0 m v=v 0*(((v 1).val%2^n:ℕ):Word w) := by
  induction n with
  | zero => simp [product,Nat.mod_one]
  | succ n ih =>
    rw [product,Term.eval_binary,ih (by omega),component_eval m v (by omega),Nat.mod_pow_succ]
    simp [BinaryOp.eval,mul_add]

theorem full {w : ℕ} (m : Memory w) (v : Fin 2→Word w) :
    (product w w).eval Fin.elim0 m v=v 0*v 1 := by
  simpa [Nat.mod_eq_of_lt (v 1).isLt] using product_eval m v w le_rfl

theorem binds (w bits : ℕ) : (product w bits).binds≤1+bits*(bits+10) := by
  induction bits with
  | zero => change 1≤1;decide
  | succ j ih =>
    have cap := ProtocolRAMPortScale.binds w (j+1) (2^j)
    simp only [product,component,Term.binary,Term.select,Term.literal,Term.binds_letThen,
      Term.binds_rename,Term.binds]
    nlinarith only [ih,cap]

theorem scale_ok (w bits n : ℕ) : admissible (ProtocolRAMPortScale.scale w bits n) := by
  induction bits generalizing n with
  | zero => simp [ProtocolRAMPortScale.scale,Term.literal,admissible,opAllowed]
  | succ j ih =>
    unfold ProtocolRAMPortScale.scale
    rw [admissible_let]
    refine ⟨ih _,?_⟩
    generalize (n%2==1)=flag
    cases flag <;> simp [ProtocolRAMPortScale.digit,admissible,opAllowed,allowed]

theorem cheap (w n : ℕ) : admissible (product w n) := by
  induction n with
  | zero => trivial
  | succ j ih =>
    simp [product,component,Term.binary,Term.select,Term.literal,
      admissible,opAllowed,allowed,ih,scale_ok]

end Hierarchy.DescentWordProduct

end OAI
