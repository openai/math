import OAI.Computability.BorderVNP.CellProfileTermFold
import OAI.Computability.BorderVNP.CellEmitRange
import OAI.Computability.BorderVNP.CellEmitWord
import OAI.Computability.QuantumFactoring.BitStackAdder

/-! # Uniform cell descriptor procedures for Boolean folds

The list count is supplied in unary. Each visit supplies its binary index and the
number of live temporary stack entries to the child emitter. The output is the
framed generator input, including the NAND and temporary-read fragments.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram CellMacro.Generator
open ExactQuantumFactoring.BitStackProgram.Procedure (boolCode)

variable {α : Type} {ea : α → List Bool} {n : α → ℕ} {t : α → ℕ → Term}

/-- Form the indexed child input together with its live temporary-stack depth. -/
noncomputable def foldInput (ea : α → List Bool) :
    Procedure (prodCode (prodCode ea Nat.bits) Nat.bits) (prodCode (prodCode ea Nat.bits) Nat.bits)
      (fun x => ((x.1.1,x.2),x.1.2+x.2)) := by
  let env := Procedure.first (prodCode ea Nat.bits) Nat.bits
  let i := Procedure.second (prodCode ea Nat.bits) Nat.bits
  let tmp := (Procedure.second ea Nat.bits).comp env
  exact (((Procedure.first ea Nat.bits).comp env).pair i).pair (Procedure.binaryAdd.comp (tmp.pair i))

/-- Emit the left operand and the command fragment that precedes the right operand. -/
noncomputable def foldBefore (disj : Bool)
    (ht : Boolean (prodCode ea Nat.bits) (fun x => t x.1 x.2)) :
    Word (prodCode (prodCode ea Nat.bits) Nat.bits) (fun x =>
      serialized 8 ((t x.1.1 x.2).emit (x.1.2+x.2)) ++ TermFold.between 8 disj) :=
  wordAppend (ht.comp (foldInput ea)) (constWord (TermFold.between 8 disj))

/-- Count visits on the source input, dropping the temporary-stack depth. -/
noncomputable def foldVisits (hn : Procedure ea unaryCode n) :
    Procedure (prodCode ea Nat.bits) unaryCode (fun x => n x.1) :=
  hn.comp (Procedure.first ea Nat.bits)

/-- Emit the terminal bit at the center of the two passes. -/
noncomputable def foldMiddle {terminal : α → Bool} (hz : Procedure ea boolCode terminal) :
    Word (prodCode ea Nat.bits) (fun x => serialized 8 (.fixed (.literal (terminal x.1)))) :=
  (Procedure.ofBool id (fun b => serialized 8 (.fixed (.literal b)))).comp
    (hz.comp (Procedure.first ea Nat.bits))

/-- A right fold may end with a data-dependent bit, as required for the upper
digits of a selector word. -/
noncomputable def foldRange (disj : Bool) {terminal : α → Bool}
    (hn : Procedure ea unaryCode n) (hz : Procedure ea boolCode terminal)
    (ht : Boolean (prodCode ea Nat.bits) (fun x => t x.1 x.2)) :
    Boolean ea (fun x => ((List.range (n x)).map (t x)).foldr (TermFold.join disj)
      (.lit (terminal x))) := by
  let visits := foldVisits hn
  let left := flatRange (f := fun (x : α × ℕ) i => serialized 8 ((t x.1 i).emit (x.2+i)) ++
    TermFold.between 8 disj) visits (foldBefore disj ht)
  let right := flatRange (f := fun _ _ => TermFold.finish 8 disj) visits
    (constWord (TermFold.finish 8 disj))
  exact (wordAppend (wordAppend left (foldMiddle hz)) right).congrFun
    (fun x => (TermFold.emit_range 8 x.2 (n x.1) disj (terminal x.1) (t x.1)).symm)

/-- Compile the finite disjunction over all labels, carrying the exact scratch
offset for every operand. -/
noncomputable def anyRange (hn : Procedure ea unaryCode n)
    (ht : Boolean (prodCode ea Nat.bits) (fun x => t x.1 x.2)) :
    Boolean ea (fun x => Term.any ((List.range (n x)).map (t x))) :=
  foldRange true hn (Procedure.constant ea boolCode false) ht

/-- Compile the finite conjunction in the same operand order. -/
noncomputable def allRange (hn : Procedure ea unaryCode n)
    (ht : Boolean (prodCode ea Nat.bits) (fun x => t x.1 x.2)) :
    Boolean ea (fun x => Term.all ((List.range (n x)).map (t x))) :=
  foldRange false hn (Procedure.constant ea boolCode true) ht

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
