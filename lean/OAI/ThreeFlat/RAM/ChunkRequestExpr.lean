import OAI.ThreeFlat.RAM.DescriptorExpr

namespace OAI
/-! # Native checks of one live request against a chunk's endpoints

Each four-word request stores a chunk tag, mode, bit offset, and expected bit.
The old and new endpoint arrays store one bit per external-memory word.
Modes zero and one check old and new bits, respectively. Mode two checks
equality of the two endpoint bits at an untouched position.
-/

namespace ThreeFlat.RAM.ChunkRequests

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr

variable {w k : ℕ}

structure Request (w : ℕ) where
  chunk : Word w
  mode : Word w
  offset : Word w
  expected : Word w

def readRow (m : Memory w) (cursor : Word w) : Request w :=
  ⟨m cursor.val, m (cursor+1).val, m (cursor+2).val, m (cursor+3).val⟩

def bitAt (m : Memory w) (base offset : Word w) : Word w := m (base+offset).val

def rowMatches (m : Memory w) (r : Request w) (chunk oldBase newBase : Word w) : Prop :=
  r.chunk = chunk →
    bitAt m (if r.mode = 1 then newBase else oldBase) r.offset =
      (if r.mode = 2 then bitAt m newBase r.offset else r.expected)

instance (m : Memory w) (r : Request w) (chunk oldBase newBase : Word w) :
    Decidable (rowMatches m r chunk oldBase newBase) := by unfold rowMatches; infer_instance

private def fieldTerm (j : Word w) : Term w k 5 :=
  (Term.binary .add (.result 0) (.literal j)).load

/-- Input registers hold cursor, tag, old base, new base, and accumulator in order. -/
def rowTerm (w k : ℕ) : Term w k 5 :=
  let base := Term.select .eq (fieldTerm 1) (.literal 1) (.result 3) (.result 2)
  let actual := (Term.binary .add base (fieldTerm 2)).load
  let alt := (Term.binary .add (.result 3) (fieldTerm 2)).load
  let target := Term.select .eq (fieldTerm 1) (.literal 2) alt (fieldTerm 3)
  let checked := Term.select .eq actual target (.result 4) (.literal 0)
  Term.select .eq (fieldTerm 0) (.result 1) checked (.result 4)

theorem rowTerm_binds : (rowTerm w k).binds = 29 := by
  simp [rowTerm, fieldTerm, Term.binary, Term.select, Term.literal, Term.load, Term.binds]

theorem rowTerm_steps : (rowTerm w k).steps = 59 := by rw [Term.steps_eq, rowTerm_binds]

theorem rowTerm_eval (data : Fin k → Word w) (m : Memory w) (vs : Fin 5 → Word w) :
    (rowTerm w k).eval data m vs =
      if rowMatches m (readRow m (vs 0)) (vs 1) (vs 2) (vs 3) then vs 4 else 0 := by
  simp only [rowTerm, fieldTerm, Term.eval_select, Term.eval_load, Term.eval_binary,
    Term.eval_literal, Term.eval, Comparison.test, BinaryOp.eval, beq_iff_eq,
    rowMatches, readRow, bitAt]
  by_cases h : m (vs 0).val = vs 1 <;> simp [h]; split_ifs <;> simp_all

attribute [irreducible] rowTerm

end ThreeFlat.RAM.ChunkRequests

end OAI
