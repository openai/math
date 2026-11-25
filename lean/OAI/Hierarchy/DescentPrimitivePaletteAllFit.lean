import OAI.Hierarchy.DescentPrimitivePaletteToken

namespace OAI
/-! Every original primitive label fits its physical palette codec. -/
namespace Hierarchy.DescentPrimitivePalette
open DescentSixParty DescentEpochTagKeys
variable {F : Type} [Field F] {s Z : ℕ} {G : PoweredGadget F} (op : RotorSpec)

theorem all_fit (x : Label G s Z op) : (codec (G:=G) op).fits x := by
  rcases x with x|x|x|x
  · exact census_fits _ x
  · exact gadget_fits _ _ x
  · trivial
  · trivial

end Hierarchy.DescentPrimitivePalette

end OAI
