import OAI.Hierarchy.DescentResetReceiverPitch
import OAI.Hierarchy.DescentResetEmissionPalette
import OAI.Hierarchy.DescentNextStagePitch

namespace OAI
/-! # Public reset locations and register pitches across consecutive dates -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentCompiler DescentSixParty DescentPacking.PackedMatch.Local.Stage ProtocolRAM
noncomputable section
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec)
    (s Z operandLanes primitiveLanes : ℕ) (old : StageVenueTail.Date)
    (addr : ℕ→ℕ→Bank) (roster : Bank)

local notation "oldExp" => NativePitch.resetCut S k tail p f h age
local notation "nextM" => NativePitch.incoming S k tail p f h ordinary (age+1)
local notation "token" => DescentPrimitivePalette.printedBits G s Z op

/-- The preceding venue emits reset input at the estimator pitch. The next venue is
normalized for the next chronological instruction, including the terminal read. -/
def scheduled (floor : ℕ) : PhysicalReset :=
  selected G S board k tail age p f gain drift degree h (oldExp) (nextM) op.C op.w operandLanes
    primitiveLanes (token) old addr roster floor

local notation "a" => scheduled G S board k tail age p f gain drift degree h ordinary op s Z operandLanes primitiveLanes old addr roster

theorem scheduled_pitches (floor : ℕ) :
    (a floor).ingress.sourceLanes=old.lanes ∧
    (a floor).ingress.targetLanes=2^(oldExp) ∧
    (a floor).successor.venue.next.lanes=(nextM) ∧
    (a floor).successor.primitive.chart.bits=(token) :=⟨rfl,rfl,rfl,rfl⟩

theorem scheduled_slots (floor : ℕ) :
    (a floor).successor.nodes=S.retainedNodes ∧
    (a floor).successor.argumentSlots=S.retainedArgumentsAt G drift ∧
    (a floor).successor.setup.retained.previousArgs=
      (if age=0 then 3*(S.firstWidth G.b p/p) else S.retainedArgumentsAt G drift) :=⟨rfl,rfl,rfl⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
