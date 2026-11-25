import OAI.Hierarchy.DescentCalendarMatrixOrigins
import OAI.Hierarchy.DescentResetOppositeRectangle

namespace OAI
/-! # The original sender and the old peer scans agree on every padded slot -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentGroupPeerOrder DescentResetOppositePayload
open DescentPacking.PackedMatch.Local.Stage
open scoped Classical
noncomputable section
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist : ℕ}
  (input : Reached W G q ε S k i z D wire hist)
set_option quotPrecheck false
local notation "A₀" => input.placement
local notation "N₀" => Fintype.card input.V
local notation "pad" => input.valid.host
local notation "chart" => input.vertex.trans (Fin.castLEEmb pad)

/-- Names outside the reached old population have empty rows in both real operand arrays. -/
theorem sender_roster :
    PackedFlow.Padded.roster (D:=(A₀).degree) (A₀) (Recorded.oldName input) pad=
      hostRotor chart (hostRoster (A₀) ((chart).trans Fin.valEmbedding)) :=by
  funext v j
  by_cases live : v.val<N₀
  · let a:=(Recorded.oldName input).symm ⟨v.val,live⟩
    have named : chart a=v:=by
      apply Fin.ext
      exact congrArg (fun h : Fin (Fintype.card input.V) => h.val) ((Recorded.oldName input).apply_symm_apply ⟨v.val,live⟩)
    rw [←named]
    exact (Recorded.peer_at (input:=input) a j).trans
      (host_at (A₀) chart a j).symm
  · have absent : ¬∃a,chart a=v:=by
      rintro ⟨a,rfl⟩
      exact live (input.vertex a).isLt
    simp only [hostRotor,dite_eq_right absent,PackedFlow.Padded.roster,DescentPackedFlowPair.Padded.next,
      DescentPackedFlowPair.Padded.project,dite_eq_right live]
    rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
