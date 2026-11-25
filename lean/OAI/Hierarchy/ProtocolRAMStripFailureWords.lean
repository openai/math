import OAI.Hierarchy.ProtocolRAMHistogram
import OAI.Hierarchy.ProtocolRAMStripTableTypes
import OAI.Hierarchy.ProtocolRAMFailureWords

namespace OAI
/-! # The native failure bank, threshold and price lookup of the strip test -/
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
def StripTest.failure {digits : ℕ} (s : StripTest digits) : FailureWords :=
  ⟨s.base,s.rowBits,s.rows,s.live,menuLookup s.table s.radix (List.ofFn s.quoted),
    ⌊2*s.tolerance*s.precision⌋₊,⌈4*s.tolerance*s.population*s.precision⌉₊⟩

end
end Hierarchy.ProtocolRAM

end OAI
