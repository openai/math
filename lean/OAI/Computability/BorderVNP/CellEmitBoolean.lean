import OAI.Computability.BorderVNP.CellEmitStatement
import OAI.Computability.QuantumFactoring.BitStackNaturals

/-! # Private construction of Boolean test fragments

Both the expression parameters and the number of temporary stack bits may be
computed from the packet. The resulting physical generator performs precisely
the sequence of reads and NAND instructions specified by `Term.emit`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {f : β → α} {a b : α → Term} {v i : α → NatExpr}

/-- Change the typed input source while retaining the physical temporary depth. -/
noncomputable def preBool (p : Boolean ea a) (q : Procedure eb ea f) : Boolean eb (fun x => a (f x)) :=
  p.comp ((q.comp (Procedure.first eb Nat.bits)).pair (Procedure.second eb Nat.bits))

/-- Print a dynamic Boolean literal, independent of the number of temporary bits. -/
noncomputable def literalBool {b : α → Bool} (p : Procedure ea Procedure.boolCode b) :
    Boolean ea (fun x => .lit (b x)) :=
  (Procedure.ofBool id (fun bit => CellMacro.Generator.serialized 8 (.fixed (.literal bit)))).comp
    (p.comp (Procedure.first ea Nat.bits))

/-- Read a physical assignment bank bit below the current temporary stack. -/
noncomputable def wireBool (p : Address ea v) : Boolean ea (fun x => .wire (v x)) :=
  readStmt (addAddr (litAddr (Procedure.second ea Nat.bits)) (preAddr p (Procedure.first ea Nat.bits)))

/-- Compute one Boolean digit of a parameter from two dynamically generated addresses. -/
noncomputable def paramBool (p : Address ea v) (q : Address ea i) :
    Boolean ea (fun x => .paramBit (v x) (i x)) :=
  bitStmt (preAddr p (Procedure.first ea Nat.bits)) (preAddr q (Procedure.first ea Nat.bits))

/-- Emit a second operand after the first operand has pushed one value. -/
noncomputable def nextTemp (p : Boolean ea a) :
    Statement (prodCode ea Nat.bits) (fun x => (a x.1).emit (x.2+1)) :=
  p.comp ((Procedure.first ea Nat.bits).pair (Procedure.successor.comp (Procedure.second ea Nat.bits)))

/-- Private compiler for negation. -/
noncomputable def notBool (p : Boolean ea a) : Boolean ea (fun x => .not (a x)) :=
  seqStmt p (constStmt _ flip)

/-- Private compiler for conjunction, retaining the concrete stack offset of the right operand. -/
noncomputable def andBool (p : Boolean ea a) (q : Boolean ea b) :
    Boolean ea (fun x => .and (a x) (b x)) :=
  seqStmt p (seqStmt (nextTemp q) (seqStmt (constStmt _ (.fixed .nand)) (seqStmt (constStmt _ flip) (constStmt _ .nil))))

/-- Private compiler for disjunction. -/
noncomputable def orBool (p : Boolean ea a) (q : Boolean ea b) :
    Boolean ea (fun x => .or (a x) (b x)) :=
  seqStmt p (seqStmt (constStmt _ flip) (seqStmt (nextTemp q)
    (seqStmt (constStmt _ flip) (seqStmt (constStmt _ (.fixed .nand)) (constStmt _ .nil)))))

/-- Compile an arbitrary fixed Boolean formula at a dynamic scratch depth. -/
noncomputable def constBool (ea : α → List Bool) : (a : Term) → Boolean ea (fun _ => a)
  | .lit b => constStmt _ (.fixed (.literal b))
  | .wire w => wireBool (constAddr ea w)
  | .paramBit x k => paramBool (constAddr ea x) (constAddr ea k)
  | .not x => notBool (constBool ea x)
  | .and x y => andBool (constBool ea x) (constBool ea y)
  | .or x y => orBool (constBool ea x) (constBool ea y)

/-- Equality and implication reuse the exact source Boolean formulas. -/
noncomputable def equalBool (p : Boolean ea a) (q : Boolean ea b) :
    Boolean ea (fun x => (a x).equal (b x)) :=
  orBool (andBool p q) (andBool (notBool p) (notBool q))

/-- Emit a conditional guard test on the same assignment bank. -/
noncomputable def impliesBool (p : Boolean ea a) (q : Boolean ea b) :
    Boolean ea (fun x => (a x).implies (b x)) := orBool (notBool p) q

private noncomputable def startTerm (p : Boolean ea a) : Statement ea (fun x => (a x).emit 0) :=
  p.comp ((Procedure.identity ea).pair (Procedure.constant ea Nat.bits 0))

/-- Emit the complete Boolean test and consume its value with a guard. -/
noncomputable def guardBool (p : Boolean ea a) : Statement ea (fun x => (a x).guard) :=
  seqStmt (startTerm p) (constStmt _ (.fixed .guard))

/-- Emit the test and update the signed path parity with its value. -/
noncomputable def signBool (p : Boolean ea a) : Statement ea (fun x => (a x).sign) :=
  seqStmt (startTerm p) (constStmt _ (.fixed .sign))

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
