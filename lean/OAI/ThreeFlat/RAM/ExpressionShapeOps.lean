import OAI.ThreeFlat.RAM.ExpressionLiteralBank
import OAI.ThreeFlat.RAM.PhysicalPinsExpr

namespace OAI
/-! # Instruction shape commutes with native expression composition -/

namespace ThreeFlat.RAM.DescriptorExpr
open private bindInputs skipInputs frontInput from OAI.ThreeFlat.RAM.DescriptorExpr
namespace LiteralBank
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr
variable {W K n m : ℕ}

@[simp] theorem shape_result (i : Fin n) : shape (.result i : Term W K n)=.result i := rfl
@[simp] theorem shape_literal (a : Word W) : shape (Term.literal a : Term W K n)=Term.literal 0 := rfl
@[simp] theorem shape_parameter (i : Fin K) : shape (Term.parameter i : Term W K n)=Term.parameter i := rfl

private theorem op_rename (o : Op W K n) (f : Fin n→Fin m) : opShape (o.rename f)=(opShape o).rename f := by cases o <;> rfl

@[simp] theorem shape_rename (e : Term W K n) (f : Fin n→Fin m) : shape (e.rename f)=(shape e).rename f := by
  induction e generalizing m with
  | result => rfl
  | bind op body ih => simp only [Term.rename,shape,op_rename,ih]

@[simp] theorem shape_letThen (e : Term W K n) (next : Term W K (n+1)) :
    shape (e.letThen next)=(shape e).letThen (shape next) := by
  induction e with
  | result => exact shape_rename _ _
  | bind op body ih => simp only [Term.letThen,shape,ih,shape_rename]

@[simp] theorem shape_binary (op : BinaryOp) (a b : Term W K n) :
    shape (Term.binary op a b)=Term.binary op (shape a) (shape b) := by
  simp [Term.binary,shape_letThen,shape_rename,shape,opShape]
@[simp] theorem shape_select (q : Comparison) (a b yes no : Term W K n) :
    shape (Term.select q a b yes no)=Term.select q (shape a) (shape b) (shape yes) (shape no) := by
  simp [Term.select,shape_letThen,shape_rename,shape,opShape]
@[simp] theorem shape_load (x : Term W K n) : shape (Term.load x)=Term.load (shape x) := by
  simp [Term.load,shape_letThen,shape,opShape]

private theorem shape_feed (args : Fin n→Term W K m) (body : Term W K (m+n)) :
    shape (bindInputs args body)=bindInputs (fun i => shape (args i)) (shape body) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bindInputs,ih,shape_letThen,shape_rename]; rfl

@[simp] theorem shape_instantiate (e : Term W K n) (args : Fin n→Term W K m) :
    shape (e.instantiate args)=(shape e).instantiate (fun i => shape (args i)) := by
  simp only [Term.instantiate,shape_feed,shape_rename]

@[simp] theorem compile_shape (f : Formula n) (p : Param→Fin K) :
    shape (f.compile p : Term W K n)=(f.compile p : Term 0 K n) := by
  induction f with
  | reg | param => rfl
  | lit a => exact congrArg (fun v : Word 0 => (Term.literal v : Term 0 K n)) (Fin.eq_zero _).symm
  | op o x y ih jh => simp [Formula.compile,ih,jh]
  | cut x y ih jh => simp [Formula.compile,ih,jh]
  | load x ih => simp [Formula.compile,ih]
  | select c x y a b hx hy ha hb => simp [Formula.compile,hx,hy,ha,hb]

end LiteralBank
end ThreeFlat.RAM.DescriptorExpr

end OAI
