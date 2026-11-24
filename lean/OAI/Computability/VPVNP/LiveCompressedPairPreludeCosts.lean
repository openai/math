import OAI.Computability.VPVNP.PairTerminalSelectedPrefixCosts

/-! # The source charges of the forced terminal prelude -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM Compression CursorNetwork CompressorRecords PairSimulation LocalHistory

variable {a g a' g' w : ℕ} {workers : TerminalLink.Stage → PairTable} {clk : ℕ} {input : Memory w}

/-- The forced prefix of the five-stage terminal table. Its row budget comes
from the actual selected history-directory execution. -/
structure PreludeCosts (X : State a g) (Y : State a' g') (pub : Fin 11 → Word w)
    (trace : TerminalLink.FiveTrace workers pub clk input) (steps limit T bound : ℕ) where
  /-- The single source report that initializes the terminal header. -/
  boot : Report w
  initialRow : trace.bootstrap.logs.map Prod.snd = [boot]
  bootWork : boot.events.length ≤ bound
  /-- The selected final state's physical incidence directory. -/
  dir : IncidenceDirectory w
  /-- Address of the first entry of the wire-offset table. -/
  prefixBase : Word w
  /-- Memory read by the wire-width scan after the bootstrap. -/
  prefixMemory : Memory w
  scan : TerminalPrefix.Segment.Run pub Y dir prefixBase prefixMemory (trace.prefixRows.logs.map Prod.snd)
  arenaTotal : RAMBuckets.cost Report.probes (trace.traversalRows.logs.map Prod.snd) ≤
    (2*limit+1294)*(((steps+1)*T+1)*X.positions)
  arenaRow : ∀ r ∈ trace.traversalRows.logs.map Prod.snd, r.probes ≤ r.events.length ∧
    r.events.length < TraversalController.callFuel limit

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
