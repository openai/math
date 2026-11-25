import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Nested physical digit indices for terminal pointer words -/
namespace Hierarchy.DescentTerminalPointerDigits
open DescentSIMDLookup
noncomputable section
variable {N A : ℕ}

structure Widths where
  nodes : ℕ
  arity : ℕ
  pointer : Fin 4→ℕ
  /-- The physical archive holds all retained nodes in the inner lane of a group word. -/
  nodeCapacity : Option ℕ := none

def Widths.nodeDigit (s : Widths) (width node group word : ℕ) : ℕ :=
  match s.nodeCapacity with
  | none=>digit width group word
  | some n=>digit width node (digit (width*n) group word)

def nodeOf (i : Fin (N*A)) : Fin N := ((finProdFinEquiv (m:=N) (n:=A)).symm i).1

end
end Hierarchy.DescentTerminalPointerDigits

end OAI
