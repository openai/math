import OAI.Hierarchy.DescentPackedInputNumber
import OAI.Hierarchy.DescentTerminalPairedOrders

namespace OAI
/-! # Rank every input profile by its actual pre-profile key, host, group and local unit -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSixParty DescentStageEdgeReceipt DescentTerminalEpochDecoder DescentTerminalEpochFlags
open DescentKernelHistory.BitDescription Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {d k H groups : ℕ} {bs : P→ℕ} {W : MarkedWorld F d P bs} {G : PoweredGadget F} {price ε : ℝ}
variable (he : 0≤ε) (A : GroupStage W G price ε J V k) (gid : J↪Fin groups) (host : V↪Fin H)
set_option quotPrecheck false
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "rank" => (sourceChart he A gid host).trans Fin.valEmbedding

theorem consumes (choice : (A.stage.result he).Choice) (c : ScanColonies he A.stage)
    (e : Matched T A.cap (thinList home color c) (thickList home color c)) :
    let p:=(scannedRows he A.stage).profile choice
    let j:=(pairNumber (amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val
    profileAt (inputNumber he A gid host) p (beforeSource he A gid host c+j)=encode (p ⟨c,e⟩) := by
  dsimp only
  rw [←rank_address he A gid host c e]
  exact profileAt_row _ _ _

end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
