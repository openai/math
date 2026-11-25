import OAI.Hierarchy.DescentOrderedReentryBasic
import OAI.Hierarchy.DescentResetEdgeTape
import OAI.Hierarchy.DescentNormalize

namespace OAI
/-! # Restoring ordinary cable units on a chronologically addressed reentry -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentChosenRouter DescentResetTrunks DescentMixedRouter
open Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d L : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
  {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z) (key : A.graph.Edge↪Fin L)
local notation "W" => reenter Z T

local notation "U" => orderedReentry Z T key
local notation "cnt" => (fun e => Computability.BorderVNP.Crossing.Network.width (World.graph (MarkedWorld.toWorld W)) e / Z.unit)

def orderedOrdinary : MarkedWorld F d P bits := (U).pieces Z.unit cnt (counts_fit Z T)

theorem orderedOrdinary_value (x : Ports bits) : (orderedOrdinary Z T key).value x=A.value x :=
  ((U).pieces_value Z.unit cnt (counts_fit Z T) x).trans (orderedReentry_value Z T key x)

/-- The actual physical post-reset normalization is one split of its marked
wires into the uniform phase unit. Tethers stay as the original wires. -/
def orderedReblock : Normalize (orderedReentry Z T key) :=
  .split (U) Z.unit cnt (counts_fit Z T) (.done (orderedOrdinary Z T key))

@[simp] theorem orderedReblock_result : (orderedReblock Z T key).result=orderedOrdinary Z T key := rfl

/-- Replacing only local scalar tables preserves every piece of the certified
geometry, down to the old record lists, the loaded hub blocks and the paid roots. -/
def orderedStage {G : PoweredGadget F} {q budget : ℝ} {J V : Type} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {k : ℕ}
    (stage : GroupStage (ordinaryWorld Z T) G q budget J V k) :
    GroupStage (orderedOrdinary Z T key) G q budget J V k :=
  {stage with incidence := ⟨stage.incidence.inside, stage.incidence.outside⟩}

theorem orderedStage_coordinates {G : PoweredGadget F} {q budget : ℝ} {J V : Type} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {k : ℕ} (stage : GroupStage (ordinaryWorld Z T) G q budget J V k)
    (unique : Function.Injective (fun v=>(stage.pos v,stage.block v))) :
    Function.Injective (fun v=>((orderedStage Z T key stage).pos v,(orderedStage Z T key stage).block v)) := unique

def orderedCableOrder (vertex : Z.V↪ℕ) :
    (orderedOrdinary Z T key).graph.Edge ≃ Fin (Fintype.card (orderedOrdinary Z T key).graph.Edge) :=
  outgoingTape Z T vertex (key.trans DescentResetWireTags.digit)

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
