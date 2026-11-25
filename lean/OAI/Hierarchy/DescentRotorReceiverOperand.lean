import OAI.Hierarchy.DescentRotorCandidateIssue
import OAI.Hierarchy.DescentClosedRosterCoverage

namespace OAI
/-! # A native rotor pointer is an authentic local receiver record ordinal -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical BigOperators
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))


open DescentResetLocalRoster DescentRotorOperandTicket
local notation "r" => (Z).k-(T).commonDepth
local notation "sz" => 2^(Z).n


/-- The short numerical row is the exact index consumed by the authenticated eight-column
    publisher at this receiver, including its three public sectors. -/
theorem rotor_receiver_row (u : Host) (s : Bool) (g₀ : (placement).Good) (e : (DescentCommonPalette.rotor (Z).graph).Edge)
    (active : DescentResetLocalRoster.active (blocks B) u (privateWire B (goodOccurrence B s g₀ e))) :
    (localRoster B u ⟨privateWire B (goodOccurrence B s g₀ e),active⟩).val=
      stemsCount B+1+contactCount B+(candidate (Z).graph height r sz s ((Z).goodLabel T g₀) e).val := by
  rw [private_number,good_ticket]

/-- At a genuine operation the local three-input issuer writes exactly the one-based suffix
    of the true row. This equation also proves the resulting combined query is within the
    receiver's finite row capacity. Both the prefix and suffix are independent of absolute host IDs. -/
theorem issued_receiver_row {p₀ field : ℕ} (proof : B.Recorded p₀) (u : Host) (s : Bool) (g₀ : (placement).Good)
    (e : (DescentCommonPalette.rotor (Z).graph).Edge) (m stop : ℕ)
    (x : Fin 3→DescentSIMDLookup.Cell field) (capRead : (x 0).val=input.placement.cap)
    (hit : (x 1).val=((Z).goodLabel T g₀).val.1+1 ∧ (x 2).val%2=0)
    (active : DescentResetLocalRoster.active (blocks B) u (privateWire B (goodOccurrence B s g₀ e)))
    (layer : Fin ((Z).circuit s g₀).layers) (batch : Fin m) (room : layer.val*m+batch.val<stop) :
    stemsCount B+1+contactCount B+
      DescentSIMDLookup.digit (DescentSharedCableNames.Packed.bits (DescentRotorCandidateIssue.bound (Z).graph height r sz))
        (layer.val*m+batch.val) (DescentRotorCandidateIssue.panel (Z).graph height (Z).width f m stop s
          ((Z).goodLabel T g₀) e x).val=
      (localRoster B u ⟨privateWire B (goodOccurrence B s g₀ e),active⟩).val+1 := by
  have heightOk:=(DescentRecordedRotorLayers.from_prior_cap B proof s g₀ _ capRead).1
  rw [DescentRotorCandidateIssue.present (Z).graph height (Z).width f m stop s ((Z).goodLabel T g₀) e x
    hit _ heightOk layer batch room,rotor_receiver_row]
  omega

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
