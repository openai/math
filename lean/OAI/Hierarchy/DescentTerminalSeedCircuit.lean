import OAI.Hierarchy.DescentSeedScalarSelectors
import OAI.Hierarchy.DescentTerminalLocalFactors
import OAI.Hierarchy.TaggedRadixPins

namespace OAI
/-! # The actual radix circuit for the original seed and its gate count -/
namespace Hierarchy.DescentTerminalSeedChip
open Catalyst Tagged DescentSeedRoot DescentTerminalLocalFactors
open ThreeFlat Routing
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {k data R s : ℕ} (X : Approximation F k data) {B : Type} [Fintype B]
  (input : Select X R s→B)
local notation "D" => digitsNeeded s
local notation "T" => Fintype.card (CountKey X R)

def coeff (i : Fin T) := originalScalar X ((Fintype.equivFin (CountKey X R)).symm i)
def pin : Pin Empty T D→B⊕Bool :=
  Sum.elim (fun i=>i.2.elim) (fun i=>.inl (input ((Fintype.equivFin (CountKey X R)).symm i.1,i.2)))
def circuit : BitNetwork F (Fintype.card B) :=
  RadixStage.pullPins (network F Empty D (coeff X (R:=R))) (pin X input)

theorem size : (circuit X input).cells+(circuit X input).internal=T*D := by
  simp [circuit,RadixStage.pullPins,BitNetwork.glue_cells,BitNetwork.glue_internal,
    network_cells,network_internal]

end
end Hierarchy.DescentTerminalSeedChip

end OAI
