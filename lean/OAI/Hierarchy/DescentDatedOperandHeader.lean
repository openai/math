import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Addresses and public widths for a native ordinary date -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPackedColony ProtocolRAM

/-- Addresses of earlier paid rows. Natural-number selectors keep these same
public definitions available at every reached world, including a padded row. -/
structure Operands where
  roster : Bank
  ids : ℕ→Bank
  offsets : Bank
  chunks : Bank
  actors : Bank
  wire : ℕ→ℕ→Bank
  hubs : Bank
  atoms : ℕ→Expr

def Operands.ports (i : Operands) (D : ℕ) : Ports D :=
  ⟨fun j=>i.ids j.val,i.roster,i.offsets,i.chunks⟩

/-- Only public integer parameters, the gadget and the fixed incoming addresses
enter the instructions and the billed clock. -/
structure Measures where
  wire : ℕ
  z : ℕ
  hist : ℕ
  deriving DecidableEq

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated

end OAI
