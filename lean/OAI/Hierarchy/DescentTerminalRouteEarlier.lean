import OAI.Hierarchy.DescentTerminalRouteSources
import OAI.Hierarchy.DescentTerminalScalarLiterals

namespace OAI
/-! # Every attained route input precedes the shared source shelf -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.RouteSources
open DescentTerminalEmitter.Compact DescentTerminalLocalPortBook DescentTerminalRowArena ProtocolRAM

theorem earlier (T:Tables) (A:Arena) (other:Columns) {end_:ℕ}
    (old:DescentTerminalEmitter.Compact.Earlier end_ other) (above:A.finish≤end_) :
    DescentTerminalEmitter.Compact.Earlier end_ (T.columns A other) := by
  intro j b live
  have saved (i) (before:i<22) : (A.bank i).base+(A.bank i).size≤end_ :=
    (A.band_after before).trans above
  unfold Tables.columns at live
  split at live <;> first | exact old j b live | cases live
  · exact saved 10 (by decide)
  · exact saved 11 (by decide)
  · exact saved 2 (by decide)
  · exact saved 12 (by decide)
  · exact saved 13 (by decide)

theorem scalar_earlier (q t H N A p v W B pool:ℕ) {end_:ℕ} (other:Columns)
    (old:DescentTerminalEmitter.Compact.Earlier end_ other) :
    DescentTerminalEmitter.Compact.Earlier end_ (ScalarLiterals.columns q t H N A p v W B pool other) := by
  intro j b live
  unfold ScalarLiterals.columns at live
  split at live <;> first | contradiction | skip
  split at live <;> first | contradiction | skip
  split at live <;> first | contradiction | skip
  split at live <;> first | contradiction | exact old j b live

end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.RouteSources

end OAI
