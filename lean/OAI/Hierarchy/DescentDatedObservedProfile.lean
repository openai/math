import OAI.Hierarchy.DescentDatedStageObserved
import OAI.Hierarchy.DescentNamedProfileSeatFit
import OAI.Hierarchy.DescentPackedMatchPins
import OAI.Hierarchy.DescentTerminalEpochLocalProfiles

namespace OAI
/-! # Equality of the original selected profile and the scores read at padded physical hosts -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentPacking.PackedMatch.Local DescentTerminalEpochDecoder DescentPackedProfileWindow
open DescentKernelHistory.BitDescription DescentStageEdgeReceipt
noncomputable section
variable {F P : Type} [Field F] {d k i z D wire hist z' D' : ℕ} {bits:P→ℕ} {G:PoweredGadget F}
    {W:MarkedWorld F d P bits} {ε q u : ℝ} {S:DescentCompiler.AtomSchedule} {source:Reached W G q ε S k i z D wire hist}
    {he:0≤ ε} {T:StageInput W G u ε} {p : (T.result he).Choice}
    {n:Normalize ((T.result he).state p)} {target:Reached n.result G q ε S k (i+1) z' D' wire hist}
    (link : OrdinaryLink source he T p n target)
set_option quotPrecheck false
set_option maxHeartbeats 1200000
local notation "A" => source.placement
local notation "e" => Equiv.refl (Fin (S.groupCount i))

theorem OrdinaryLink.counted_selection :
    selectionCount G link.selection=Fintype.card (scannedRows he (A).stage).pairs :=by
  obtain rfl:=link.sourceRate
  obtain rfl:=eq_of_heq link.placement
  rfl

theorem OrdinaryLink.padded_profile {H : ℕ} (host : source.V↪Fin H)
    (cap : Fintype.card source.V≤ H) (num : ∀x,(host x).val=(source.vertex x).val) :
    ∃actual : ((A).stage.result he).Choice, HEq p actual ∧
      ∀j,issuedProfile G ⟨link.selection,link.inputPair⟩ j=
        profileAt (inputNumber he A (e).toEmbedding host) ((scannedRows he (A).stage).profile actual) j :=by
  obtain rfl:=link.sourceRate
  obtain rfl:=eq_of_heq link.placement
  have key : link.inputPair=inputNumbers he source:=eq_of_heq link.inputRows
  have padded := Stage.Prepared.padded_inputNumber A he (Function.Embedding.refl _) source.vertex (e).toEmbedding host le_rfl cap
    (fun _=>rfl) num
  refine ⟨p,HEq.rfl,?_⟩
  change ∀j,profileAt link.inputPair ((scannedRows he (A).stage).profile p) j=_
  rw [key]
  change ∀j,profileAt (inputNumber he A (Function.Embedding.refl _) source.vertex) _ j=_
  rw [padded]
  exact fun _=>rfl

end
end Hierarchy.DescentSixParty.Chronology

end OAI
