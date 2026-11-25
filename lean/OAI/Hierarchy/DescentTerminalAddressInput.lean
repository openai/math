import OAI.Hierarchy.DescentTerminalBookPublish
import OAI.Hierarchy.DescentPackedPrivateSum

namespace OAI
/-! # Physical input banks and columns of the terminal address plan -/
namespace Hierarchy.DescentTerminalEmitter.Compact
open ProtocolRAM

/-- An attained column continues at its existing address. A literal column purchases
new space for its fixed table. -/
inductive Column where
  | attained (bank : Bank)
  | literal (words : ℕ)

abbrev Columns := Fin 43 → Column

end Hierarchy.DescentTerminalEmitter.Compact

namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open ProtocolRAM

/-- The field declarations give the actual preceding row-plan controls, six
public packet columns, and width tuples from the sparse real cable/public headers. -/
structure Input where
  parts : DescentTerminalLocalPortBook.Book.Parts
  totals : Bank
  boundaries : ℕ
  modulo : Bank
  homes : Bank
  directory : Fin 8→Bank
  sources : DescentTerminalEmitter.Compact.Columns
  publicTapes : Fin 6→Bank
  cable : Fin 5→Bank
  exterior : Fin 5→Bank
  candidate : Bank
  indexEvents : ℕ
  formatEvents : ℕ
  blank : ℕ
  legacy : DescentPackedPrivateSum.Layout
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open ProtocolRAM
/-- The reached input supplies the terminal operands from the native preflight.
The auxiliary packed-counter layout starts at the first address. -/
def fixedFallback : Input :=
  let origin : Bank := ⟨0,0⟩
  { parts := fun _ => ⟨origin,origin⟩
    totals := origin
    boundaries := 0
    modulo := origin
    homes := origin
    directory := fun _ => origin
    sources := fun _ => .literal 0
    publicTapes := fun _ => origin
    cable := fun _ => origin
    exterior := fun _ => origin
    candidate := origin
    indexEvents := 0
    formatEvents := 0
    blank := 0
    legacy := ⟨origin,origin,0,0⟩ }

/-- Every fallback emitter column has an empty literal table. -/
theorem fixedFallback_sources (i : Fin 43) : fixedFallback.sources i = .literal 0 := rfl

end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
