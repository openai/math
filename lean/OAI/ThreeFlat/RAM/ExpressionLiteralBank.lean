import OAI.ThreeFlat.RAM.ExpressionPublicParams

namespace OAI
/-! # A common instruction stream with literals supplied in public words -/

namespace ThreeFlat.RAM.DescriptorExpr.LiteralBank
open Computability.VPVNP.BurstRAM PrivateRAM

variable {W K n C : ℕ}

/-- Width zero leaves exactly one scalar value, hence retains only the
operator and its operand indices in the instruction skeleton. -/
def opShape : Op W K n → Op 0 K n
  | .literal _ => .literal 0
  | .parameter i => .parameter i
  | .binary op i j => .binary op i j
  | .load i => .load i
  | .select c i j a b => .select c i j a b

def shape : {n : ℕ} → Term W K n → Term 0 K n
  | _,.result i => .result i
  | _,.bind op rest => .bind (opShape op) (shape rest)

def opWord : Op W K n → Word W
  | .literal v => v
  | _ => 0

def words : {n : ℕ} → Term W K n → List (Word W)
  | _,.result _ => []
  | _,.bind op rest => opWord op :: words rest

private def readOp (slot : Fin C) : Op 0 K n → Op W (K+C) n
  | .literal _ => .parameter (Fin.natAdd K slot)
  | .parameter i => .parameter (i.castAdd C)
  | .binary op i j => .binary op i j
  | .load i => .load i
  | .select c i j a b => .select c i j a b

/-- Slot numbers may wrap on unreachable code, allowing this common program
to be defined before the public capacity certificate is supplied. -/
def withSlots (slot : ℕ→Fin C) : {n : ℕ} → Term 0 K n → ℕ → Term W (K+C) n
  | _,.result i,_ => .result i
  | _,.bind op e,off => .bind (readOp (slot off) op) (withSlots slot e (off+1))

@[simp] theorem shape_binds (e : Term W K n) : (shape e).binds=e.binds := by
  induction e with
  | result => rfl
  | bind op body ih => simp [shape,Term.binds,ih]

@[simp] theorem words_length (e : Term W K n) : (words e).length=e.binds := by
  induction e with
  | result => rfl
  | bind op body ih => simp [words,Term.binds,ih]

@[simp] theorem withSlots_binds (e : Term 0 K n) (slot : ℕ→Fin C) (off : ℕ) :
    (withSlots (W:=W) slot e off).binds=e.binds := by
  induction e generalizing off with
  | result => rfl
  | bind op body ih => simp [withSlots,Term.binds,ih]

private theorem readOp_eval (op : Op W K n) (slot : Fin C) (data : Fin K→Word W)
    (table : Fin C→Word W) (vs : Fin n→Word W) (m : Memory W)
    (atSlot : table slot=opWord op) :
    (readOp slot (opShape op)).eval (Fin.append data table) vs m=op.eval data vs m := by
  cases op <;> simp [opShape,readOp,Op.eval,opWord,Fin.append_left,Fin.append_right] at *; assumption

theorem eval_withSlots (e : Term W K n) (slot : ℕ→Fin C) (off : ℕ)
    (data : Fin K→Word W) (table : Fin C→Word W) (vs : Fin n→Word W) (m : Memory W)
    (loaded : ∀ i : Fin (words e).length, table (slot (off+i.val))=(words e)[i]) :
    (withSlots slot (shape e) off).eval (Fin.append data table) m vs=e.eval data m vs := by
  induction e generalizing off with
  | result => rfl
  | bind op rest ih =>
    have head := loaded ⟨0,by simp [words]⟩
    simp only [words,Nat.add_zero] at head
    simp only [shape,withSlots,Term.eval,readOp_eval op _ _ _ _ _ head]
    apply ih
    intro i
    simpa [words,Nat.add_assoc,Nat.add_comm 1 _,Nat.add_left_comm] using
      loaded (⟨i.val+1,by simpa [words] using i.isLt⟩)

/-- One fixed skeleton with a public parameter bank realizes every member
of a family having that instruction stream. There is one word per bind. -/
theorem correct {e : Term W K n} {skeleton : Term 0 K n} (same : shape e=skeleton)
    (limit : e.binds<C) (data : Fin K→Word W) (vs : Fin n→Word W) (m : Memory W) :
    let slot := fun j : ℕ => (⟨j%C,Nat.mod_lt _ (by omega)⟩ : Fin C)
    let table := fun j : Fin C => (words e)[j.val]?.getD 0
    (withSlots slot skeleton 0).eval (Fin.append data table) m vs=e.eval data m vs := by
  intro slot table
  rw [←same]
  apply eval_withSlots
  intro i
  have small : i.val<C := i.isLt.trans_le (by simpa using limit.le)
  simp [slot,table,Nat.mod_eq_of_lt small,List.getElem?_eq_getElem i.isLt]

end ThreeFlat.RAM.DescriptorExpr.LiteralBank

end OAI
