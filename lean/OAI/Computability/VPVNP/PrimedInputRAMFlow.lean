import OAI.Computability.VPVNP.PrimedStackRAMCode
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Structured finite jump tables for the auxiliary burst RAM

A straight-line instruction, a branch, a sequence and a loop all have
finite sets of instruction labels. A loop introduces one test and a back
edge to that test. Neither the width of a word nor the number of iterations
affects the table size. Compilation maps local labels to ordinary bounded
program counters of the fixed burst RAM template.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {r k : ℕ}

/-- Fixed program text. A test reads two register words. `branch` makes one
binary choice even when its two continuations have identical effects. -/
inductive Flow (r k : ℕ) where
  | line (op : Op r k)
  | seq (a b : Flow r k)
  | ifEq (lhs rhs : Fin r) (yes no : Flow r k)
  | ifLt (lhs rhs : Fin r) (yes no : Flow r k)
  | branch (yes no : Flow r k)
  | whileLt (lhs rhs : Fin r) (body : Flow r k)

namespace Flow

/-- Instruction addresses are local labels. `none` designates the common
exit and can later be linked to the next block or a return instruction. -/
inductive Jump (pc : Type) (r k : ℕ) where
  | line (op : Op r k) (next : pc)
  | ifEq (lhs rhs : Fin r) (yes no : pc)
  | ifLt (lhs rhs : Fin r) (yes no : pc)
  | branch (yes no : pc)

/-- Relabel the successor targets of a jump while preserving its instruction, operands and
choice branches. -/
def Jump.map {A B : Type} (f : A → B) : Jump A r k → Jump B r k
  | .line op next => .line op (f next)
  | .ifEq l q yes no => .ifEq l q (f yes) (f no)
  | .ifLt l q yes no => .ifLt l q (f yes) (f no)
  | .branch yes no => .branch (f yes) (f no)

theorem Jump.map_map {A B C : Type} (f : A → B) (g : B → C) (i : Jump A r k) :
    (i.map f).map g = i.map (g ∘ f) := by cases i <;> rfl

/-- Compile a jump with bounded program counters to a burst instruction, sending failed guards
to the supplied rejection address. -/
def Jump.emit {p : ℕ} (bad : Fin p) : Jump (Fin p) r k → Instr 2 p r k
  | .line op next => op.emit next bad
  | .ifEq l q yes no => .jumpEq l q yes no
  | .ifLt l q yes no => .jumpLt l q yes no
  | .branch yes no => .choose yes no

/-- Local program-counter type. In a compound block the sum tags identify
the instruction's enclosing branch, body or test. -/
def Label : Flow r k → Type
  | .line _ => Unit
  | .seq a b => a.Label ⊕ b.Label
  | .ifEq _ _ a b | .ifLt _ _ a b | .branch a b => Unit ⊕ (a.Label ⊕ b.Label)
  | .whileLt _ _ a => Unit ⊕ a.Label

/-- Number of labeled instructions in the structured program, counting the tests of branches
and loops. -/
def length : Flow r k → ℕ
  | .line _ => 1
  | .seq a b => a.length + b.length
  | .ifEq _ _ a b | .ifLt _ _ a b | .branch a b => 1 + (a.length + b.length)
  | .whileLt _ _ a => 1 + a.length

private def unitFin : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := Subsingleton.elim _ i

/-- Numerical labels for the fixed instruction table. -/
def labels : (a : Flow r k) → a.Label ≃ Fin a.length
  | .line _ => unitFin
  | .seq a b => ((labels a).sumCongr (labels b)).trans finSumFinEquiv
  | .ifEq _ _ a b | .ifLt _ _ a b | .branch a b =>
    (unitFin.sumCongr (((labels a).sumCongr (labels b)).trans finSumFinEquiv)).trans finSumFinEquiv
  | .whileLt _ _ a => (unitFin.sumCongr (labels a)).trans finSumFinEquiv

/-- First label executed when entering the structured control-flow program. -/
def entry : (a : Flow r k) → a.Label
  | .line _ => ()
  | .seq a _ => .inl a.entry
  | .ifEq .. | .ifLt .. | .branch .. | .whileLt .. => .inl ()

private def link {A B : Type} (f : A → B) (exit : Option B) : Option A → Option B
  | none => exit
  | some a => some (f a)

private def branchCode {A B : Type} (test : Jump (Option (Unit ⊕ (A ⊕ B))) r k)
    (yes : A → Jump (Option A) r k) (no : B → Jump (Option B) r k) :
    Unit ⊕ (A ⊕ B) → Jump (Option (Unit ⊕ (A ⊕ B))) r k
  | .inl _ => test
  | .inr (.inl i) => (yes i).map (Option.map (Sum.inr ∘ Sum.inl))
  | .inr (.inr j) => (no j).map (Option.map (Sum.inr ∘ Sum.inr))

/-- The complete control graph. Body exits of a loop are wired back to its
test; exits of the first member of a sequence enter its second member. -/
def code : (a : Flow r k) → a.Label → Jump (Option a.Label) r k
  | .line op, _ => .line op none
  | .seq a b, .inl i => (code a i).map (link Sum.inl (some (.inr b.entry)))
  | .seq _ b, .inr j => (code b j).map (Option.map Sum.inr)
  | .ifEq l q a b, i =>
    branchCode (.ifEq l q (some (.inr (.inl a.entry))) (some (.inr (.inr b.entry))))
      (code a) (code b) i
  | .ifLt l q a b, i =>
    branchCode (.ifLt l q (some (.inr (.inl a.entry))) (some (.inr (.inr b.entry))))
      (code a) (code b) i
  | .branch a b, i =>
    branchCode (.branch (some (.inr (.inl a.entry))) (some (.inr (.inr b.entry))))
      (code a) (code b) i
  | .whileLt l q body, .inl _ => .ifLt l q (some (.inr body.entry)) none
  | .whileLt _ _ body, .inr i => (code body i).map (link Sum.inr (some (.inl ())))

/-- Bounded counter of a real instruction label. -/
def pc (a : Flow r k) (i : a.Label) : Fin (a.length + 2) :=
  Fin.castAdd 2 (a.labels i)

/-- Program counter reserved for normal exit from the structured code. -/
def exitPC (a : Flow r k) : Fin (a.length + 2) := ⟨a.length, by omega⟩
/-- Program counter reserved for rejecting a failed guard in the structured code. -/
def rejectPC (a : Flow r k) : Fin (a.length + 2) := ⟨a.length+1, by omega⟩

/-- Translate an optional local successor to its compiled program counter, mapping the absent
successor to normal exit. -/
def target (a : Flow r k) : Option a.Label → Fin (a.length + 2)
  | none => a.exitPC
  | some i => a.pc i

/-- The table emits exactly one finite private-RAM instruction per label,
plus a normal exit and a rejecting exit. -/
def template (a : Flow r k) (result : Option (Fin r)) : Template (a.length+2) r k where
  literalWidth := 2
  entry := a.pc a.entry
  code i :=
    if h : i.val < a.length then
      ((a.code (a.labels.symm ⟨i.val,h⟩)).map a.target).emit a.rejectPC
    else if i = a.exitPC then (match result with | none => .accept | some reg => .returnState reg)
    else .reject

theorem template_at (a : Flow r k) (result : Option (Fin r)) (i : a.Label) :
    (a.template result).code (a.pc i) = ((a.code i).map a.target).emit a.rejectPC := by
  simp [template, pc, (a.labels i).isLt]

theorem template_exit (a : Flow r k) (result : Option (Fin r)) :
    (a.template result).code a.exitPC = (match result with | none => .accept | some j => .returnState j) := by
  simp [template, exitPC]

theorem template_reject (a : Flow r k) (result : Option (Fin r)) :
    (a.template result).code a.rejectPC = .reject := by
  simp [template, rejectPC, exitPC, Fin.ext_iff, show ¬ a.length+1 < a.length by omega]

/-- A block may occupy labels in a larger table. Its local normal and bad
exits need not be the enclosing table's own exits. -/
structure Linked {w p : ℕ} (M : Machine w p r k) (a : Flow r k)
    (label : a.Label → Fin p) (stop bad : Fin p) : Prop where
  atLabel : ∀ i, M.code (label i) =
    (((a.code i).map (fun t ↦ (t.map label).getD stop)).emit bad).resize w

theorem template_linked {w : ℕ} (a : Flow r k) (result : Option (Fin r)) (pub : Fin k → Word w) :
    Linked ((a.template result).instantiate w pub) a a.pc a.exitPC a.rejectPC := by
  constructor
  intro i
  change ((a.template result).code (a.pc i)).resize w = _
  rw [template_at]
  have htarget : a.target = fun t ↦ (t.map a.pc).getD a.exitPC := by funext t; cases t <;> rfl
  rw [htarget]
  rfl

theorem Linked.seqLeft {w p : ℕ} {M : Machine w p r k} {a b : Flow r k}
    {label : (a.seq b).Label → Fin p} {stop bad : Fin p}
    (h : Linked M (a.seq b) label stop bad) :
    Linked M a (label ∘ Sum.inl) (label (.inr b.entry)) bad := by
  constructor
  intro i
  change M.code (label (.inl i)) = _
  rw [h.atLabel (.inl i)]
  simp only [code, Jump.map_map]
  congr 3
  funext t
  cases t <;> rfl

theorem Linked.seqRight {w p : ℕ} {M : Machine w p r k} {a b : Flow r k}
    {label : (a.seq b).Label → Fin p} {stop bad : Fin p}
    (h : Linked M (a.seq b) label stop bad) : Linked M b (label ∘ Sum.inr) stop bad := by
  constructor
  intro j
  change M.code (label (.inr j)) = _
  rw [h.atLabel (.inr j)]
  simp only [code, Jump.map_map]
  congr 3
  funext t
  cases t <;> rfl

theorem Linked.loopBody {w p : ℕ} {M : Machine w p r k} {body : Flow r k} {l q : Fin r}
    {label : (Flow.whileLt l q body).Label → Fin p} {stop bad : Fin p}
    (h : Linked M (.whileLt l q body) label stop bad) :
    Linked M body (label ∘ Sum.inr) (label (.inl ())) bad := by
  constructor
  intro j
  change M.code (label (.inr j)) = _
  rw [h.atLabel (.inr j)]
  simp only [code, Jump.map_map]
  congr 3
  funext t
  cases t <;> rfl

end Flow
end PrimedInputRAM

end VPVNP
end Computability
end OAI
