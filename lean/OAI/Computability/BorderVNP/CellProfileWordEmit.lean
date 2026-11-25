import OAI.Computability.BorderVNP.CellProfileTermEmit
import OAI.Computability.BorderVNP.CellEmitBoolean
import OAI.Computability.QuantumFactoring.BitStackBoundedUnary
import OAI.Computability.QuantumFactoring.BitStackTestBit

/-! # Uniform serialization of a little-endian selector equality

The public label has a canonical binary encoding. Reading its digit first clips
the index to the length of this encoding. The terminal test reads the bit length
of the whole label, so an out-of-width label fails the same high-bit check as
the source compiler.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure (boolCode)

/-- Count the digits in the canonical binary encoding. -/
noncomputable def digitCount : Procedure Nat.bits unaryCode Nat.size :=
  (Procedure.length.precompose Nat.bits).congrFun Nat.size_eq_bits_len

/-- Read a binary digit after clipping the index to the encoded length. -/
noncomputable def binaryDigit : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun x => x.1.testBit x.2) := by
  let j := Procedure.first Nat.bits Nat.bits
  let i := Procedure.second Nat.bits Nat.bits
  let k := Procedure.clippedUnary.comp ((digitCount.comp j).pair i)
  refine (Procedure.testBit.comp (j.pair k)).congrFun ?_
  intro x
  change x.1.testBit (min x.1.size x.2) = x.1.testBit x.2
  by_cases hi : x.2 ≤ x.1.size
  · rw [min_eq_right hi]
  · rw [min_eq_left (by omega), Nat.testBit_lt_two_pow (Nat.size_le.mp (le_refl _)),
      Nat.testBit_lt_two_pow (Nat.size_le.mp (by omega))]

variable {α : Type} {ea : α → List Bool}

/-- Read the public digit at the current lane of the operand pass. -/
noncomputable def wordDigitFor {j : α → ℕ} (hj : Procedure ea Nat.bits j) :
    Procedure (prodCode ea Nat.bits) boolCode (fun x => (j x.1).testBit x.2) :=
  binaryDigit.comp ((hj.comp (Procedure.first ea Nat.bits)).pair (Procedure.second ea Nat.bits))

/-- Check the remaining high digits in one call after the operand pass. -/
noncomputable def wordTerminal {n j : α → ℕ} (hn : Procedure ea unaryCode n) (hj : Procedure ea Nat.bits j) :
    Procedure ea boolCode (fun x => decide ((j x).size ≤ n x)) :=
  Procedure.unaryLe.comp ((digitCount.comp hj).pair hn)

/-- Emit one wire comparison at the supplied temporary depth. -/
noncomputable def wordLaneTest {j : α → ℕ} {a : α → ℕ → NatExpr}
    (hj : Procedure ea Nat.bits j) (ha : Address (prodCode ea Nat.bits) (fun z => a z.1 z.2)) :
    Boolean (prodCode ea Nat.bits) (fun x => (Term.wire (a x.1 x.2)).equal (.lit ((j x.1).testBit x.2))) :=
  equalBool (wireBool ha) (literalBool (wordDigitFor hj))

/-- Print the word equality for a unary width, with a binary label and one
address supplied per original lane. -/
noncomputable def wordIsRange {n j : α → ℕ} {a : α → ℕ → NatExpr}
    (hn : Procedure ea unaryCode n) (hj : Procedure ea Nat.bits j)
    (ha : Address (prodCode ea Nat.bits) (fun z => a z.1 z.2)) :
    Boolean ea (fun x => wordIs ((List.range (n x)).map (a x)) (j x)) := by
  let code := foldRange (t := fun (x : α) i => (Term.wire (a x i)).equal (.lit ((j x).testBit i)))
    false hn (wordTerminal hn hj) (wordLaneTest hj ha)
  exact code.congrFun (fun x => congrArg (fun t : Term => CellMacro.Generator.serialized 8 (t.emit x.2))
    (TermFold.wordIs_range (n x.1) (j x.1) (a x.1)).symm)

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
