import OAI.Computability.BorderVNP.CellEmitWord

/-! # Printing native arithmetic-address layouts on private stacks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram
open CellMacro.Generator (exprBits)
open RationalHitting.StackLanguage (codeWord)

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {f : β → α} {a b : α → NatExpr} {n : α → ℕ}

/-- Change the source of an address computation by an actual preprocessing procedure. -/
noncomputable def preAddr (p : Address ea a) (q : Procedure eb ea f) :
    Address eb (fun x => a (f x)) := fun d => (p d).comp q

/-- Print a fixed lexical index or other constant address template. -/
noncomputable def constAddr (ea : α → List Bool) (a : NatExpr) : Address ea (fun _ => a) :=
  fun d => constWord (exprBits d a)

private noncomputable def litHead (p : Procedure ea Nat.bits n) : Word ea (fun x => exprBits 0 (.lit (n x))) :=
  let raw : Word ea (fun x => (n x).bits) := p.result (fun _ => rfl)
  (wordPrepend (codeWord [false] ++ codeWord [false] ++ codeWord [false]) (framed raw)).congrFun (by
    intro x
    change _ = codeWord [false] ++ (codeWord [false] ++ (codeWord [false] ++ (codeWord (n x).bits ++ [])))
    simp [List.append_assoc])

/-- The private source field supplies the binary literal at every chosen output depth. -/
noncomputable def litAddr (p : Procedure ea Nat.bits n) : Address ea (fun x => .lit (n x))
  | 0 => litHead p
  | d+1 => (wordAppend (framed (litHead p))
      (constWord (codeWord (exprBits d (.lit 0)) ++ exprBits d (.lit 0)))).congrFun (fun _ => rfl)

private noncomputable def binAddr (op : NatExpr → NatExpr → NatExpr)
    (h0 : ∀ u v, exprBits 0 (op u v) = exprBits 0 (op (.lit 0) (.lit 0)))
    (hs : ∀ d u v, exprBits (d+1) (op u v) =
      codeWord (exprBits 0 (op (.lit 0) (.lit 0))) ++ (codeWord (exprBits d u) ++ exprBits d v))
    (p : Address ea a) (q : Address ea b) : Address ea (fun x => op (a x) (b x))
  | 0 => (constWord _).congrFun (fun _ => (h0 ..).symm)
  | d+1 => (wordPrepend (codeWord (exprBits 0 (op (.lit 0) (.lit 0))))
      (wordAppend (framed (p d)) (q d))).congrFun (fun _ => (hs ..).symm)

/-- Native expression serialization for a sum of two dynamic addresses. -/
noncomputable def addAddr (p : Address ea a) (q : Address ea b) : Address ea (fun x => .add (a x) (b x)) :=
  binAddr NatExpr.add (fun _ _ => rfl) (fun _ _ _ => rfl) p q

/-- Native expression serialization for a product of two dynamic addresses. -/
noncomputable def mulAddr (p : Address ea a) (q : Address ea b) : Address ea (fun x => .mul (a x) (b x)) :=
  binAddr NatExpr.mul (fun _ _ => rfl) (fun _ _ _ => rfl) p q

/-- Native expression serialization for truncated subtraction. -/
noncomputable def subAddr (p : Address ea a) (q : Address ea b) : Address ea (fun x => .sub (a x) (b x)) :=
  binAddr NatExpr.sub (fun _ _ => rfl) (fun _ _ _ => rfl) p q

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
