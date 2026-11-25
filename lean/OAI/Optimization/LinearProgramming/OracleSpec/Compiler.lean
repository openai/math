import OAI.Optimization.LinearProgramming.OracleSpec.Machine
import Mathlib.Logic.Equiv.Fin.Basic

/-! A finite structured language for programs that read one bit and write one bit at a
 time. The compiler numbers every control location before it is run. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec

variable {k : ℕ} {α β : Type}

inductive BitCode (k : ℕ) where
  | skip
  | push (s : Fin k) (b : Bool)
  | emit (b : Bool)
  | ask
  | seq (first second : BitCode k)
  | cases (s : Fin k) (empty ff tt : BitCode k)
  | loop (s : Fin k) (ff tt : BitCode k)

namespace BitCode

structure Memory (k : ℕ) where
  store : Fin k → Word
  bufferRev : Word
  transcript : Transcript

def Memory.push (m : Memory k) (s : Fin k) (b : Bool) : Memory k :=
  { m with store := Function.update m.store s (b :: m.store s) }

def Memory.pop (m : Memory k) (s : Fin k) : Memory k :=
  { m with store := Function.update m.store s (m.store s).tail }

def Memory.emit (m : Memory k) (b : Bool) : Memory k :=
  { m with bufferRev := b :: m.bufferRev }

def Memory.receive (m : Memory k) (s : Fin k) (answer : Word) : Memory k :=
  { store := Function.update m.store s answer, bufferRev := [],
    transcript := (m.bufferRev.reverse, answer) :: m.transcript }

/-- An execution counts every primitive stack operation, every branch/loop test, every
emitted bit and the lengths of both words at the oracle boundary. -/
inductive Executes (answer : Fin k) (o : WordOracle) :
    BitCode k → Memory k → Memory k → ℕ → Prop where
  | skip (m) : Executes answer o .skip m m 1
  | push (m s b) : Executes answer o (.push s b) m (m.push s b) 1
  | emit (m b) : Executes answer o (.emit b) m (m.emit b) 1
  | ask (m) : Executes answer o .ask m (m.receive answer (o m.transcript m.bufferRev.reverse))
      (1 + m.bufferRev.reverse.length + (o m.transcript m.bufferRev.reverse).length)
  | seq {p q m mid out a b} : Executes answer o p m mid a → Executes answer o q mid out b →
      Executes answer o (.seq p q) m out (a+b)
  | casesNil {s p q r m out a} : m.store s = [] → Executes answer o p m out a →
      Executes answer o (.cases s p q r) m out (1+a)
  | casesFalse {s p q r m out xs a} : m.store s = false :: xs → Executes answer o q (m.pop s) out a →
      Executes answer o (.cases s p q r) m out (1+a)
  | casesTrue {s p q r m out xs a} : m.store s = true :: xs → Executes answer o r (m.pop s) out a →
      Executes answer o (.cases s p q r) m out (1+a)
  | loopNil {s p q m} : m.store s = [] → Executes answer o (.loop s p q) m m 1
  | loopFalse {s p q m mid out xs a b} : m.store s = false :: xs →
      Executes answer o p (m.pop s) mid a → Executes answer o (.loop s p q) mid out b →
      Executes answer o (.loop s p q) m out (1+(a+b))
  | loopTrue {s p q m mid out xs a b} : m.store s = true :: xs →
      Executes answer o q (m.pop s) mid a → Executes answer o (.loop s p q) mid out b →
      Executes answer o (.loop s p q) m out (1+(a+b))

def Node : BitCode k → Type
  | .skip | .push _ _ | .emit _ | .ask => Unit
  | .seq p q => Node p ⊕ Node q
  | .cases _ p q r => Unit ⊕ (Node p ⊕ (Node q ⊕ Node r))
  | .loop _ p q => Unit ⊕ (Node p ⊕ Node q)

def entry : (c : BitCode k) → c.Node
  | .skip | .push _ _ | .emit _ | .ask => ()
  | .seq p _ => .inl p.entry
  | .cases _ _ _ _ | .loop _ _ _ => .inl ()

/-- A computable enumeration, independent of all inputs, identifies structured labels
with the `Fin` program counters of the machine. -/
structure Numbering (α : Type) where
  count : ℕ
  index : α ≃ Fin count

def Numbering.one : Numbering Unit :=
  ⟨1, ⟨fun _ => 0, fun _ => (), fun _ => rfl, fun i => Subsingleton.elim _ i⟩⟩

def Numbering.sum (a : Numbering α) (b : Numbering β) : Numbering (α ⊕ β) :=
  ⟨a.count + b.count, (a.index.sumCongr b.index).trans finSumFinEquiv⟩

def numbering : (c : BitCode k) → Numbering c.Node
  | .skip | .push _ _ | .emit _ | .ask => .one
  | .seq p q => p.numbering.sum q.numbering
  | .cases _ p q r => Numbering.one.sum (p.numbering.sum (q.numbering.sum r.numbering))
  | .loop _ p q => Numbering.one.sum (p.numbering.sum q.numbering)

structure Line (Q : Type) (k : ℕ) where
  scan : Fin k
  op : Option Bool → BitInstruction Q (Fin k)

/-- In `cases` and `loop` one instruction both examines and consumes the selected bit. -/
def line {Q : Type} (defaultStack : Fin k) :
    (c : BitCode k) → Q → (c.Node → Q) → c.Node → Line Q k
  | .skip, dest, _, _ => ⟨defaultStack, fun _ => .jump dest⟩
  | .push s b, dest, _, _ => ⟨defaultStack, fun _ => .push s b dest⟩
  | .emit b, dest, _, _ => ⟨defaultStack, fun _ => .emit b dest⟩
  | .ask, dest, _, _ => ⟨defaultStack, fun _ => .ask dest⟩
  | .seq p q, _, w, .inl i => line defaultStack p (w (.inr q.entry)) (w ∘ Sum.inl) i
  | .seq _ q, d, w, .inr i => line defaultStack q d (w ∘ Sum.inr) i
  | .cases s p q r, _, w, .inl _ => ⟨s, fun
      | none => .jump (w (.inr (.inl p.entry)))
      | some false => .pop s (w (.inr (.inr (.inl q.entry))))
      | some true => .pop s (w (.inr (.inr (.inr r.entry))))⟩
  | .cases _ p _ _, d, w, .inr (.inl i) => line defaultStack p d (w ∘ Sum.inr ∘ Sum.inl) i
  | .cases _ _ q _, d, w, .inr (.inr (.inl i)) =>
      line defaultStack q d (w ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl) i
  | .cases _ _ _ r, d, w, .inr (.inr (.inr i)) =>
      line defaultStack r d (w ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr) i
  | .loop s p q, d, w, .inl _ => ⟨s, fun
      | none => .jump d
      | some false => .pop s (w (.inr (.inl p.entry)))
      | some true => .pop s (w (.inr (.inr q.entry)))⟩
  | .loop _ p _, _, w, .inr (.inl i) =>
      line defaultStack p (w (.inl ())) (w ∘ Sum.inr ∘ Sum.inl) i
  | .loop _ _ q, _, w, .inr (.inr i) =>
      line defaultStack q (w (.inl ())) (w ∘ Sum.inr ∘ Sum.inr) i

def labels (c : BitCode k) := c.numbering.sum Numbering.one

def address (c : BitCode k) (i : c.Node) := c.labels.index (.inl i)

def exitAddress (c : BitCode k) := c.labels.index (.inr ())

def table (c : BitCode k) (input : Fin k) (q : Fin c.labels.count) : Line (Fin c.labels.count) k :=
  match c.labels.index.symm q with
  | .inl i => line input c c.exitAddress c.address i
  | .inr _ => ⟨input, fun _ => .halt⟩

def compile (c : BitCode k) (input answer : Fin k) : BitProgram where
  states := c.labels.count
  stackCount := k
  start := c.address c.entry
  inputStack := input
  answerStack := answer
  scan := fun s => (c.table input s).scan
  instruction := fun s => (c.table input s).op

end BitCode
end OracleSpec
end LinearProgramming
end Optimization
end OAI
