import OAI.Hierarchy.DescentSixPartyGadget
import OAI.Hierarchy.DescentRotorAlphabet

namespace OAI
/-! # The fixed finite labels shared by the original, newborn, and reset coefficients -/
namespace Hierarchy.DescentKernelHistory
open DescentSixParty
variable {F : Type*} [Field F] (G : PoweredGadget F)

abbrev CensusTag (s : ℕ) := Σ m : Fin 4,(Fin m.val→Bool)→Fin (s+1)
abbrev SeedTag (s : ℕ) := CensusTag s ⊕ Unit
abbrev GadgetTag (Z : ℕ) := Fin (Z+1) × Profile G.C × Fin 6

end Hierarchy.DescentKernelHistory

namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty DescentResetGates
variable {F : Type} [Field F]
abbrev Label (G : PoweredGadget F) (s Z : ℕ) (op : RotorSpec) :=
  SeedTag s ⊕ (GadgetTag G Z ⊕ (Unit ⊕ CanonicalTag (2^op.n)))

end Hierarchy.DescentPrimitivePalette

end OAI
