import OAI.Computability.BorderVNP.CellSparseGenerator

/-! # Boolean constraints in the bounded-loop cell compiler

A formula leaves one result above the original bank. Every argument is evaluated once.
Negation duplicates the result by a read of stack offset zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro

/-- Boolean expressions used in a sparse guard, with parameter-dependent static addresses. -/
inductive Term where
  | lit (b : Bool)
  | wire (a : NatExpr)
  | paramBit (a i : NatExpr)
  | not (a : Term)
  | and (a b : Term)
  | or (a b : Term)
  deriving DecidableEq

/-- Value of a guard at its lexical counters and immutable wire bank. -/
def Term.eval (env : List ℕ) (bank : ℕ → Bool) : Term → Bool
  | .lit b => b
  | .wire a => bank (a.eval env)
  | .paramBit a i => (a.eval env).testBit (i.eval env)
  | .not a => !(a.eval env bank)
  | .and a b => a.eval env bank && b.eval env bank
  | .or a b => a.eval env bank || b.eval env bank

/-- Value of the named wire, with the zero extension used by the private machine. -/
def lookup (v : List Bool) (i : ℕ) : Bool := (v.drop i).head?.getD false

/-- Negate the top of the value stack. -/
def flip : Stmt := .seq (.fixed (.read 0)) (.fixed .nand)

/-- Emit an arithmetic-indexed Boolean expression above `d` scratch values. -/
def Term.emit : Term → ℕ → Stmt
  | .lit b, _ => .fixed (.literal b)
  | .wire a, d => .read (.add (.lit d) a)
  | .paramBit a i, _ => .bit a i
  | .not a, d => .seq (a.emit d) flip
  | .and a b, d => sequence [a.emit d, b.emit (d + 1), .fixed .nand, flip]
  | .or a b, d => sequence [a.emit d, flip, b.emit (d + 1), flip, .fixed .nand]

private theorem value_flip (ops : List Op) (f : Flags) (b : Bool) (v : List Bool) :
    value (.read 0 :: .nand :: ops) f (b :: v) = value ops f ((!b) :: v) := by
  cases b <;> rfl

private theorem drop_prefix (tmp v : List Bool) (i : ℕ) :
    (tmp ++ v).drop (tmp.length + i) = v.drop i := by
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega)]
  simp

/-- The emitted instructions produce exactly one result and restore every earlier
stack bit. The continuation can be arbitrary, including further private choices. -/
theorem Term.value_emit (a : Term) (env : List ℕ) (ops : List Op)
    (f : Flags) (tmp bank : List Bool) :
    value (((a.emit tmp.length).expand env) ++ ops) f (tmp ++ bank) =
      value ops f (a.eval env (lookup bank) :: (tmp ++ bank)) := by
  induction a generalizing tmp ops with
  | lit b => rfl
  | paramBit a i => rfl
  | wire a =>
    change value ops f (((tmp ++ bank).drop (tmp.length + a.eval env)).head?.getD false :: _) = _
    rw [drop_prefix]
    rfl
  | not a ih =>
    simp only [emit, Stmt.expand, List.append_assoc, flip, List.singleton_append, eval]
    rw [ih]
    apply value_flip
  | and a b ha hb =>
    simp only [emit, expand_sequence, List.flatMap_cons, List.flatMap_nil, Stmt.expand,
      flip, List.append_nil, List.append_assoc, List.cons_append, List.nil_append, eval]
    rw [ha]
    have h := hb (.nand :: .read 0 :: .nand :: ops) (a.eval env (lookup bank) :: tmp)
    simp only [List.length_cons, List.cons_append] at h
    rw [h]
    cases a.eval env (lookup bank) <;> cases b.eval env (lookup bank) <;> rfl
  | or a b ha hb =>
    simp only [emit, expand_sequence, List.flatMap_cons, List.flatMap_nil, Stmt.expand,
      flip, List.append_nil, List.append_assoc, List.cons_append, List.nil_append, eval]
    rw [ha, value_flip]
    have h := hb (.read 0 :: .nand :: .nand :: ops) ((!(a.eval env (lookup bank))) :: tmp)
    simp only [List.length_cons, List.cons_append] at h
    rw [h, value_flip]
    cases a.eval env (lookup bank) <;> cases b.eval env (lookup bank) <;> rfl

/-- Boolean equality, used for cable and transcript checks. -/
def Term.equal (a b : Term) : Term := .or (.and a b) (.and (.not a) (.not b))

/-- Boolean implication, used to guard a routing equality by a selector code. -/
def Term.implies (a b : Term) : Term := .or (.not a) b

/-- Conjunction of a list of local tests. -/
def Term.all (xs : List Term) : Term := xs.foldr Term.and (.lit true)

/-- Disjunction of a list of local tests. -/
def Term.any (xs : List Term) : Term := xs.foldr Term.or (.lit false)

@[simp] theorem Term.eval_equal (a b : Term) (env : List ℕ) (bank : ℕ → Bool) :
    (a.equal b).eval env bank = decide (a.eval env bank = b.eval env bank) := by
  simp only [equal, eval]
  cases a.eval env bank <;> cases b.eval env bank <;> rfl

@[simp] theorem Term.eval_all (xs : List Term) (env : List ℕ) (bank : ℕ → Bool) :
    (Term.all xs).eval env bank = xs.all (Term.eval env bank) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [Term.all, eval] at ih ⊢; rw [ih]

@[simp] theorem Term.eval_any (xs : List Term) (env : List ℕ) (bank : ℕ → Bool) :
    (Term.any xs).eval env bank = xs.any (Term.eval env bank) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [Term.any, eval] at ih ⊢; rw [ih]

/-- Compile a guard while preserving the immutable bank. -/
def Term.guard (a : Term) : Stmt := .seq (a.emit 0) (.fixed .guard)

/-- Multiply the private sign by minus one exactly when the expression holds. -/
def Term.sign (a : Term) : Stmt := .seq (a.emit 0) (.fixed .sign)

/-- Failed guards propagate to the signed halt, with all input bits restored. -/
theorem Term.value_guard (a : Term) (env : List ℕ) (ops : List Op) (f : Flags) (v : List Bool) :
    value ((a.guard.expand env) ++ ops) f v =
      value ops ⟨f.ok && a.eval env (lookup v), f.minus⟩ v := by
  simpa [guard, Stmt.expand, List.append_assoc, value, Op.effect] using
    a.value_emit env (.guard :: ops) f [] v

/-- A sign instruction toggles parity without consuming a wire assignment. -/
theorem Term.value_sign (a : Term) (env : List ℕ) (ops : List Op) (f : Flags) (v : List Bool) :
    value ((a.sign.expand env) ++ ops) f v =
      value ops ⟨f.ok, f.minus ^^ a.eval env (lookup v)⟩ v := by
  simpa [sign, Stmt.expand, List.append_assoc, value, Op.effect] using
    a.value_emit env (.sign :: ops) f [] v

end CellSparse

end BorderVNP
end Computability
end OAI
