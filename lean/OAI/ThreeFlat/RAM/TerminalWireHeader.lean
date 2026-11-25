import Mathlib.Data.Nat.Basic

namespace OAI
/-! # The eight public terminal wire archive locations -/
namespace ThreeFlat.RAM.TerminalWireArchive
/-- At the final stage the number of outgoing wire bits is term-dependent. The directory
still knows the number of width entries, the suffix capacity and the two raw source bases. -/
structure Layout where
  current : ℕ
  phase : ℕ
  oldSource : ℕ
  newSource : ℕ
  capacity : ℕ
  widthBase : ℕ
  edges : ℕ
  prefixBase : ℕ

/-- The terminal directory is appended to the static rectangular stage headers. -/
def header (x : Layout) : ℕ → ℕ
  | 0 => x.capacity+1
  | 1 => x.prefixBase
  | 2 => x.edges+1
  | _ => 0

end ThreeFlat.RAM.TerminalWireArchive

end OAI
