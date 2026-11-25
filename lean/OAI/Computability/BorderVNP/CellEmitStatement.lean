import OAI.Computability.BorderVNP.CellEmitAddress

/-! # Physically printing sparse statement constructors -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open CellMacro.Generator (serialized wire exprBits)
open ExactQuantumFactoring.BitStackProgram
open RationalHitting.StackLanguage (codeWord)

variable {α : Type} {ea : α → List Bool} {a b : α → NatExpr} {s t : α → Stmt}

/-- Emit a constant command or subprogram. -/
noncomputable def constStmt (ea : α → List Bool) (s : Stmt) : Statement ea (fun _ => s) :=
  constWord (serialized 8 s)

/-- Adjacent blocks are physically concatenated with no recursive sequence overhead. -/
noncomputable def seqStmt (p : Statement ea s) (q : Statement ea t) :
    Statement ea (fun x => .seq (s x) (t x)) :=
  (wordAppend p q).congrFun (fun x => by simp [serialized,wire,records_append])

/-- Emit a physical stack read with a computed sparse address. -/
noncomputable def readStmt (p : Address ea a) : Statement ea (fun x => .read (a x)) :=
  singleRecord (wordPrepend [false,false,true] (p 8))

/-- Emit the instruction that extracts one bit of a computed parameter. -/
noncomputable def bitStmt (p : Address ea a) (q : Address ea b) :
    Statement ea (fun x => .bit (a x) (b x)) :=
  singleRecord (wordPrepend [false,true] (wordAppend (framed (p 8)) (q 8)))

/-- Store a loop body once, with its dynamic iteration count in a separate binary field. -/
noncomputable def loopStmt (p : Address ea a) (q : Statement ea s) :
    Statement ea (fun x => .loop (a x) (s x)) :=
  singleRecord (wordPrepend [true,false] (wordAppend (framed (p 8)) q))

/-- Store both alternative sparse blocks and the native arithmetic equality test. -/
noncomputable def ifEqStmt (p : Address ea a) (q : Address ea b) (yes : Statement ea s)
    (no : Statement ea t) : Statement ea (fun x => .ifEq (a x) (b x) (s x) (t x)) :=
  let delta := addAddr (subAddr p q) (subAddr q p)
  singleRecord (wordPrepend [true,true] (wordAppend (framed (delta 8)) (wordAppend (framed yes) no)))

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
