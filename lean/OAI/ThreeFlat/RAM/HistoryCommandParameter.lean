import OAI.ThreeFlat.RAM.PhysicalScanLink

namespace OAI
/-! # Reading a selected command's operands from its live record -/

namespace ThreeFlat.RAM.HistoryCommandParameter

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr
variable {w k K n : ℕ}

/-- Dynamic operand slots can be memory reads or ordinary immutable words.
The row's input registers remain available to the original expression. -/
def replace (arg : Fin k → Term w K 0) : {a : ℕ} → Term w k a → Term w K a
  | _, .result i => .result i
  | _, .bind (.literal v) body => .bind (.literal v) (replace arg body)
  | _, .bind (.parameter i) body => ((arg i).rename Fin.elim0).letThen (replace arg body)
  | _, .bind (.binary op a b) body => .bind (.binary op a b) (replace arg body)
  | _, .bind (.load a) body => .bind (.load a) (replace arg body)
  | _, .bind (.select cmp a b u v) body => .bind (.select cmp a b u v) (replace arg body)

theorem eval_replace (arg : Fin k → Term w K 0) (e : Term w k n)
    (data : Fin K → Word w) (mem : Memory w) (vs : Fin n → Word w) :
    (replace arg e).eval data mem vs=e.eval (fun i => (arg i).eval data mem Fin.elim0) mem vs := by
  induction e with
  | result i => rfl
  | bind op body ih =>
    have empty : vs ∘ (Fin.elim0 : Fin 0 → _) = Fin.elim0 := Subsingleton.elim _ _
    cases op <;> simp only [replace,Term.eval,Term.eval_letThen,Term.eval_rename,ih,Op.eval,empty]

theorem binds_replace (arg : Fin k → Term w K 0) (e : Term w k n) (cost : ℕ)
    (unit : 1≤cost) (size : ∀ i, (arg i).binds≤cost) : (replace arg e).binds≤e.binds*cost := by
  induction e with
  | result i => simp [replace,Term.binds]
  | bind op body ih =>
    cases op <;> simp only [replace,Term.binds,Term.binds_letThen,Term.binds_rename,Nat.add_mul,Nat.one_mul] <;>
      first | omega | exact (Nat.add_le_add (size _) ih).trans_eq (Nat.add_comm ..)

variable (control : Fin K)

/-- The global cursor points to a seven-word command; word zero of that
command points to the operation's private contiguous argument block. -/
def operandBlock : Term w K 0 := (Term.parameter control).load.load

/-- The first original public word is the dynamic operand address. -/
def onlyBlock (e : Term w 1 n) : Term w K n := replace (fun _ => operandBlock control) e

theorem onlyBlock_eval (e : Term w 1 n) (data : Fin K → Word w) (mem : Memory w) (vs : Fin n → Word w) :
    (onlyBlock control e).eval data mem vs=e.eval (fun _ => mem (mem (data control).val).val) mem vs := by
  rw [onlyBlock,eval_replace]; rfl

theorem onlyBlock_binds (e : Term w 1 n) : (onlyBlock (w:=w) control e).binds≤e.binds*3 := by
  exact binds_replace _ e 3 (by decide) (fun _ => by change 3≤3; exact le_rfl)

end ThreeFlat.RAM.HistoryCommandParameter

end OAI
