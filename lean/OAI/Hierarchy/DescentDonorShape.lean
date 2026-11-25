import OAI.Hierarchy.DescentDonorWidths
import OAI.Hierarchy.DescentPackedMatchedInput

namespace OAI
/-! # Widths of the bounded packed donor fields -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Owners
open DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {r D p d : ℕ}
def register (l : Bool) (u : Panel r D p d) : Cell (inputBits r D p d) :=
  finCongr (pow_add 2 1 (d*fields r D p)).symm (finProdFinEquiv ((l.toNat:Cell 1),encodePanel u))
end
end Hierarchy.DescentPacking.PackedMatch.Local.Owners

end OAI
