import OAI.Computability.VPVNP.RankCursorRegisters
import OAI.Computability.VPVNP.RankQueryStackEngineSpec

/-! # Stack layout of a complete rank scan

The arithmetic cursor and the Schur engine use separate banks. The row
count and balanced product depth supply two constant fields of every root
request. The scalar output is read from the engine's result port.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

open RAMTape BurstRAM Dispatch

/-- Ports of the rectangular rank scan. The cursor and Schur engine have separate stack banks
alongside the row count, product depth, and copy scratch. -/
inductive ScanPort (K : Type) where
  | cursor (p : Registers.Port)
  | engine (p : Engine.Port K)
  | rows | depth | scratch
  deriving DecidableEq, Fintype

variable {K : Type} {w : ℕ}

/-- A bank with independently specified engine and arithmetic registers. -/
def scanBank (n : ℕ) (persistent : Word w) (rs : Regs Registers.R w)
    (flags : List Bool) (work : Stacks (Engine.Port K)) (scratch : List Bool := []) : Stacks (ScanPort K)
  | .cursor k => Registers.bank persistent rs flags k
  | .engine k => work k
  | .rows => UniversalCountStack.digits w n
  | .depth => UniversalCountStack.digits w (Nat.clog 2 n)
  | .scratch => scratch

/-- All frame and query stacks are empty between requests; the auxiliary
engine bank retains the matrix and field description. -/
def idle (aux : Stacks K) : Stacks (Engine.Port K) :=
  Engine.store (fun _ => []) (fun _ => []) [] [] aux

/-- At the scalar check boundary the Schur result occupies its result port. -/
def yielded (aux : Stacks K) (bits : List Bool) : Stacks (Engine.Port K) :=
  Engine.store (fun _ => []) (fun _ => []) [] bits aux

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI
