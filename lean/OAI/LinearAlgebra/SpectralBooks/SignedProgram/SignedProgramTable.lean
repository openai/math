import OAI.LinearAlgebra.SpectralBooks.SignedWitness
import Mathlib.Data.Fintype.Pi

/-! # Bounded transition tables for the signed universal machine -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram

open SignedMachine

/-- One candidate transition, padded to the input length. -/
structure Move (n : ℕ) where
  state : Fin (n+1)
  inputMove : Direction
  work : Fin n → Symbol × Direction

/-- Kind zero halts, kind one steps, kind two branches. -/
structure Row (n : ℕ) where
  state : Fin (n+1)
  input : Symbol
  reads : Fin n → Symbol
  kind : Fin 3
  out : Output
  next : Bool → Move n

structure Table (n : ℕ) where
  tapes : Fin (n+1)
  rows : Fin (n+1)
  row : Fin n → Row n

/-- Read the active prefix of a padded array. -/
def activeList {α : Type*} {n : ℕ} (k : Fin (n+1)) (v : Fin n → α) : List α :=
  List.ofFn fun i : Fin k.val ↦ v (i.castLE (Nat.le_of_lt_succ k.isLt))

def Move.transition {n : ℕ} (m : Move n) (tapes : Fin (n+1)) : Transition :=
  ⟨m.state, m.inputMove, activeList tapes m.work⟩

def Row.action {n : ℕ} (r : Row n) (tapes : Fin (n+1)) : Action :=
  if r.kind = 0 then .halt r.out
  else if r.kind = 1 then .step ((r.next false).transition tapes)
  else .branch ((r.next false).transition tapes) ((r.next true).transition tapes)

def Row.rule {n : ℕ} (r : Row n) (tapes : Fin (n+1)) : Rule :=
  ⟨r.state, r.input, activeList tapes r.reads, r.action tapes⟩

def Table.program {n : ℕ} (t : Table n) : Program :=
  ⟨t.tapes, activeList t.rows fun i ↦ (t.row i).rule t.tapes⟩

end SignedProgram

end SpectralBooks
end LinearAlgebra
end OAI
