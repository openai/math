import OAI.Computability.VPVNP.PairShrinkJobPrepared
import OAI.Computability.VPVNP.PairShrinkRoleMapWitness

/-!
# The native shrinking party and its selected kernel witness

The same placed old factors, independently supplied new halves and once-guessed
absorbed labels give the same entry input in the executable map and in the
local polynomial witness.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open BurstRAM Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open CompressorRecords CompressorRecords.ShrinkSlots

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (S.degreeExponent i.castSucc)
  (packingLaneBits (S.degreeExponent i.castSucc) g))
variable (sel : X.ShrinkSelection B.shrink)
/-- Classical decidable equality on the compression state’s base vertices for identifying the
native map input with the selected kernel input. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "side" => selectedLayout X B.shrink sel

variable (v : (X.Base × BitWord (packingTagBits (2 ^ S.degreeExponent i.castSucc))) × BitWord g)
variable (old : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
  X.packingInputIso.site.symm) X.network.Half v)
variable (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)
variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
  (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel)) v)
variable (q : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v)
variable (J : Job X B.shrink (S.shrink i) sel q.1.1 q.1.2 w)

set_option maxHeartbeats 1000000 in
-- Reindexing the local arguments unfolds the dependent half-wire type of the chosen layout.
/-- Reading the stored parent and its placed child packets gives the input
whose accepted name list appears in the shrinking kernel's monomial witness. -/
theorem Job.entryInput_eq_witness
    (children : J.old = Eq.rec (motive := fun y _ ↦ Placed (X.packingData.shrinkPlace side)
      (X.packingData.oldWireNetwork X.packingWidth).Half y)
      (ShrinkRole.MapWitness.placedOld B i X sel v old) q.2.symm)
    (newHalf : J.parent = Eq.rec (motive := fun y _ ↦
      (X.shrinkNext B.shrink (S.shrink i) sel).network.Half y) parent q.2.symm) :
    Job.entryInput B X (S.shrink i) sel q.1.1 q.1.2 J (q.2.symm ▸ hidden) =
      ShrinkRole.MapWitness.input B i X sel v old parent hidden q := by
  unfold Job.entryInput ShrinkPreparedCall.input
  rw [children, newHalf]
  rfl

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
