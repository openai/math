import OAI.Computability.VPVNP.PairShrinkCanonicalJob
import OAI.Computability.VPVNP.PairShrinkMapJobInput
import OAI.Computability.VPVNP.PairShrinkCallFrameLive

/-!
# The resident map jobs of a selected shrinking vertex

One old assignment and one parent packet determine the inputs of every
resident occurrence. Their placement equalities reindex those arguments
without changing any bit. Every job in the bank uses the same private
arena and the two row bases of this actual shrinking substep.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSiteBank

open BurstRAM Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open CompressorRecords CompressorRecords.ShrinkBlockInputs CompressorRecords.ShrinkSlots
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
private noncomputable local instance bankBase : DecidableEq X.Base := Classical.decEq _
local notation "side" => selectedLayout X B.shrink sel
local notation "Y" => X.shrinkNext B.shrink (S.shrink i) sel
variable (workspace : Word w) (positions blocks cur : ℕ)
variable (bounds : ShrinkResidentSources.Bounds B i X workspace positions blocks cur)
variable (n rowEnd older later : ℕ)
variable (v : (X.Base × BitWord (packingTagBits (2 ^ a i))) × BitWord g)
variable (old : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
  X.packingInputIso.site.symm) X.network.Half v)
variable (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)
variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
  (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel)) v)

/-- The actual fixed job for any motif and party assigned to this popped site. -/
noncomputable def jobs (q : X.packingData.ResidentMap side v) :
    ShrinkPartyNative.Job X B.shrink (S.shrink i) sel q.1.1 q.1.2 w :=
  ShrinkCanonicalJob.job B i X (S.shrink i) sel q.1.1 q.1.2 workspace positions blocks cur
    bounds n rowEnd older later
    (Eq.rec (motive := fun y _ ↦ Placed (X.packingData.shrinkPlace side)
      (X.packingData.oldWireNetwork X.packingWidth).Half y)
      (ShrinkRole.MapWitness.placedOld B i X sel v old) q.2.symm)
    (Eq.rec (motive := fun y _ ↦ (Y).network.Half y) parent q.2.symm)

local notation "J" => jobs B i X sel workspace positions blocks cur bounds n rowEnd older later
  v old parent

set_option maxHeartbeats 1800000 in
-- The two kernel arguments have dependent site indices in both network presentations.
/-- The concrete resident read has exactly the demand and supply bit vectors
of its selected local tensor witness. -/
theorem input_eq (q : X.packingData.ResidentMap side v) :
    ShrinkPartyNative.Job.entryInput B X (S.shrink i) sel q.1.1 q.1.2 (J q)
      (q.2.symm ▸ hidden) = ShrinkRole.MapWitness.input B i X sel v old parent hidden q :=
  ShrinkPartyNative.Job.entryInput_eq_witness B i X sel v old parent hidden q (J q) rfl rfl

/-- The five shared input registers used at every resident of the site. -/
noncomputable def pub (level node : Word w) (regions : LeafArena.Regions) (n : ℕ) :
    Fin 5 → Word w :=
  ![level, node, (NativeFrame.frameBase regions : Word w), (regions.histBase : Word w),
    (ShrinkCallABI.hiddenBase regions n : Word w)]

/-- The loaded node number is independent of the resident chosen by the row. -/
theorem node_eq (q : X.packingData.ResidentMap side v) :
    (J q).node = later + (B.recordLimit + 2) * PortRefresh.ArgumentAddress.siteOrdinal (Y) v := by
  change later + (B.recordLimit + 2) * PortRefresh.ArgumentAddress.siteOrdinal (Y)
    (X.packingData.shrinkPartySite side q.1.1 q.1.2) = _
  rw [q.2]

end PairSimulation.ShrinkSiteBank

end VPVNP
end Computability
end OAI
