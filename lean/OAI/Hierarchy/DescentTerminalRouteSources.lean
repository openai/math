import OAI.Hierarchy.DescentTerminalAddressPlan
import OAI.Hierarchy.DescentTerminalBookTokens
import OAI.Hierarchy.DescentTerminalBookedGates

namespace OAI
/-! # Five attained allocator columns and the eight shared book and route tables -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.RouteSources
open DescentTerminalEmitter.Compact DescentTerminalLocalPortBook DescentTerminalRowArena
open DescentTerminalRouteRows DescentTerminalRouteLedger Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section

structure Tables where
  groups : ℕ
  vertices : ℕ
  maximum : ℕ
  arity : ℕ
  tokenBits : ℕ
  width : ℕ
  lanes : ℕ
  bins : ℕ

namespace Tables
variable (T : Tables)
def bytes := Book.Bytes T.groups T.vertices T.maximum T.arity T.tokenBits
def nameWidth := Nat.clog 2 (T.width*2^T.tokenBits)
def line := rowBits T.lanes T.nameWidth
def buffer := T.width*T.line
def extent := T.bins*T.width
def menuSize := T.width*(T.width*T.bytes)

def columns (A : Arena) (other : Columns) (j : Fin 43) : Column :=
  match j.val with
  | 24 => .attained A.row.locate.active
  | 25 => .attained A.row.locate.owner
  | 26 => .attained A.row.books
  | 27 => .attained A.row.locate.localRow
  | 28 => .attained A.offset.offsets
  | 29 => .literal T.width
  | 30 => .literal T.width
  | 31 => .literal T.menuSize
  | 32 => .literal (2^T.line)
  | 33 => .literal T.extent
  | 34 => .literal (radix T.width T.line)
  | 35 => .literal (3*T.extent)
  | 36 => .literal (2^T.buffer)
  | _ => other j

/-- The five route table domains are the actual packed row, phase index, update key,
three-word gate row and full within-bin packed state. -/
def value (prior : Fin 43 → ℕ → ℕ) (j : Fin 43) (u : ℕ) : ℕ :=
  match j.val with
  | 29 => T.bytes*u
  | 30 => T.width*T.bytes*u
  | 31 => if h:u<T.menuSize then
      (Book.menu (G:=T.groups) (V:=T.vertices) (M:=T.maximum) (A:=T.arity)
        (a:=T.tokenBits) T.lanes (⟨u,h⟩:Fin T.menuSize)).val else 0
  | 32 => 2^T.buffer*u
  | 33 => if h:u<T.extent then
      2^T.buffer*(2^T.line*(finProdFinEquiv.symm (⟨u,h⟩:Fin T.extent):Fin T.bins×Fin T.width).2.val)
    else 0
  | 34 => if h:u<radix T.width T.line then (stepROM (W:=T.width) (c:=T.line) ⟨u,h⟩).val else 0
  | 35 => if h:u/3<T.extent then
      (finProdFinEquiv.symm (⟨u/3,h⟩:Fin T.extent):Fin T.bins×Fin T.width).1.val*T.width+T.width-1
    else 0
  | 36 => if h:u<2^T.buffer then
      (lookup (W:=T.width) (q:=T.lanes) (a:=T.nameWidth) ⟨u,h⟩).val else 0
  | _ => prior j u

def data (A : Arena) (other : Columns) (prior : Fin 43 → ℕ → ℕ) :
    Literals (T.columns A other) := fun j u => T.value prior j u.val

def input (S : Shape) (J : Input) (base : ℕ) : Input :=
  {J with sources:=T.columns (rowArena S J base) J.sources}

/-- Changing the emitter's declarations preserves the allocator that produced its inputs. -/
theorem allocator (S : Shape) (J : Input) (base : ℕ) :
    rowArena S (T.input S J base) base = rowArena S J base := rfl

theorem phase (prior : Fin 43→ℕ→ℕ) (i : Fin T.extent) :
    T.value prior 33 i.val=2^T.buffer*(2^T.line*(finProdFinEquiv.symm i:Fin T.bins×Fin T.width).2.val) := by
  simp [value,i.isLt]

theorem last (prior : Fin 43→ℕ→ℕ) (i : Fin T.extent) :
    T.value prior 35 (3*i.val)=(finProdFinEquiv.symm i:Fin T.bins×Fin T.width).1.val*T.width+T.width-1 := by
  have div : 3*i.val/3=i.val := by omega
  simp [value,div,i.isLt]

end Tables
end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.RouteSources

end OAI
