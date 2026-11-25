import OAI.Computability.VPVNP.RAMProgram
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI
/-! # Linking native finite instruction tables with a continuation

A block emits native instructions in a caller's register and label spaces.
Sequential composition allocates disjoint labels, sends the first exit directly
to the second entry, and shares the register frame. Operand reindexing allows
each constituent to use its own scratch bank or designated shared registers.
-/

namespace ThreeFlat.RAM.ContinuationLink

open Computability.VPVNP.BurstRAM PrivateRAM

/-- A finite instruction table whose last jump is supplied by its caller. -/
structure Block (w p r k : ℕ) where
  first : Fin p
  emit {P R K : ℕ} (pc : Fin p ↪ Fin P) (reg : Fin r ↪ Fin R)
    (pub : Fin k → Fin K) (exit : Fin P) : Fin p → Instr w P R K

variable {w p q r k P R K s l : ℕ}

/-- Allocate the block's register and public operands in a common frame. -/
def Block.reindex (b : Block w p r k) (frame : Fin r ↪ Fin s) (params : Fin k → Fin l) :
    Block w p s l where
  first := b.first
  emit pc reg pub exit := b.emit pc (frame.trans reg) (pub ∘ params) exit

/-- Concatenate two label banks. Control transfers directly across their boundary. -/
def Block.seq (a : Block w p r k) (b : Block w q r k) : Block w (p+q) r k where
  first := a.first.castAdd q
  emit pc reg pub exit := Fin.addCases
    (a.emit ((Fin.castAddEmb q).trans pc) reg pub (pc (Fin.natAdd p b.first)))
    (b.emit ((Fin.natAddEmb p).trans pc) reg pub exit)

/-- Every emitted row can be fetched at its assigned counter in the machine. -/
def Block.Installed (b : Block w p r k) (M : Machine w P R K)
    (pc : Fin p ↪ Fin P) (reg : Fin r ↪ Fin R) (pub : Fin k → Fin K) (exit : Fin P) : Prop :=
  ∀ i, M.code (pc i) = b.emit pc reg pub exit i

/-- The exact installed tables of both constituents, including their destinations. -/
theorem Block.seq_installed (a : Block w p r k) (b : Block w q r k)
    (M : Machine w P R K) (pc : Fin (p+q) ↪ Fin P) (reg : Fin r ↪ Fin R)
    (pub : Fin k → Fin K) (exit : Fin P) :
    (a.seq b).Installed M pc reg pub exit ↔
      a.Installed M ((Fin.castAddEmb q).trans pc) reg pub (pc (Fin.natAdd p b.first)) ∧
      b.Installed M ((Fin.natAddEmb p).trans pc) reg pub exit := by
  constructor
  · intro installed
    exact ⟨fun i => by simpa [Block.seq] using installed (i.castAdd q),
      fun i => by simpa [Block.seq] using installed (Fin.natAdd p i)⟩
  · rintro ⟨ha,hb⟩ i
    exact Fin.addCases (fun j => by simpa [Block.seq] using ha j)
      (fun j => by simpa [Block.seq] using hb j) i

theorem Block.reindex_installed (b : Block w p r k) (frame : Fin r ↪ Fin s)
    (params : Fin k → Fin l) (M : Machine w P R K) (pc : Fin p ↪ Fin P)
    (reg : Fin s ↪ Fin R) (pub : Fin l → Fin K) (exit : Fin P) :
    (b.reindex frame params).Installed M pc reg pub exit ↔
      b.Installed M pc (frame.trans reg) (pub ∘ params) exit := Iff.rfl

/-- Install a block and a continuation in a single ROM. Continuation rows have
the full caller counter space and can jump to either label bank. -/
def close (b : Block w p r k) (next : Fin q)
    (tail : (Fin q ↪ Fin (p+q)) → Fin q → Instr w (p+q) r k) (data : Fin k → Word w) :
    Machine w (p+q) r k where
  entry := b.first.castAdd q
  code := Fin.addCases
    (b.emit (Fin.castAddEmb q) (Function.Embedding.refl _) id (Fin.natAdd p next))
    (tail (Fin.natAddEmb p))
  publicData := data

theorem close_installed (b : Block w p r k) (next : Fin q)
    (tail : (Fin q ↪ Fin (p+q)) → Fin q → Instr w (p+q) r k) (data : Fin k → Word w) :
    b.Installed (close b next tail data) (Fin.castAddEmb q) (Function.Embedding.refl _) id
      (Fin.natAdd p next) := by
  intro i
  simp [close]

@[simp] theorem close_tail (b : Block w p r k) (next : Fin q)
    (tail : (Fin q ↪ Fin (p+q)) → Fin q → Instr w (p+q) r k) (data : Fin k → Word w)
    (i : Fin q) : (close b next tail data).code (Fin.natAdd p i) = tail (Fin.natAddEmb p) i := by
  simp [close]

end ThreeFlat.RAM.ContinuationLink

end OAI
