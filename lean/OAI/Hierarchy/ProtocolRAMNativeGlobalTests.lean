import OAI.Hierarchy.ProtocolRAMStripTableTypes
import OAI.Hierarchy.ProtocolRAMPurchaseInventory
import OAI.Hierarchy.ProtocolRAMGuardAdvice

namespace OAI
/-! # Native potential and payload scans for the public test board -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar

def scoreCut (n : ℕ) (baseline : ℝ) := (baseline+3/8)*(n:ℝ)

namespace GlobalTests
open Computability.VPVNP.BurstRAM PrivateRAM AttemptGate AdaptiveProbe
open ThreeFlat.RAM
open scoped Fin.CommRing Classical BigOperators

def kinds (N k : ℕ) := 1+N*(2*k)
abbrev rows (z N k : ℕ) := PurchaseInventory.footprint z N k

def offsets (l : Layout) : Bank := ⟨l.base,l.indexBits⟩
def span (l : Layout) (N k : ℕ) := kinds N k*l.stride
def table (l : Layout) (z N k : ℕ) (payload : Bool) : Bank :=
  ⟨l.base+rows z N k+(if payload then span l N k else 0),l.indexBits⟩
def stop (l : Layout) (z N k : ℕ) := l.base+rows z N k+2*span l N k

/-- Geometry, word width, tap count and the bound are literals in this three-read
program. Indices refer to exactly the same canonical slots as the commodity commit. -/
def check (l : Layout) (z N k : ℕ) (p : Bool) (out bound : ℕ) (stocks : Bank) : Check :=
  ⟨out,rows z N k,bound,valueTerm (table l z N k p) (offsets l) stocks⟩

def bound (l : Layout) (z : ℕ) (baseline : ℝ) :=
  ⌈(l.precision:ℝ)*scoreCut (2^z) baseline⌉₊

/-- Install the two real word scans in the controller's test board. The subsequent
layout pass relocates only their output banks, so the ROM and dynamic stock indices
here remain the indices read by the launched machine. -/
def board (l : Layout) (z N k : ℕ) (b : TestBoard) (stock : Bank)
    (baseline : ℝ) : TestBoard :=
  {b with
    excess:=check l z N k false b.excess.out (bound l z baseline) stock
    payload:=check l z N k true b.payload.out (bound l z 1) stock}

theorem rowCount (z N k : ℕ) : rows z N k=kinds N k*2^z := rfl

end GlobalTests
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
