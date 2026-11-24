import OAI.Computability.VPVNP.PairShrinkRoleMapLabels
import OAI.Computability.VPVNP.PairShrinkMapJobInput
import OAI.Computability.VPVNP.PairShrinkVertexImage
import OAI.Computability.VPVNP.PairSimulationShrinkRowAction
import OAI.Computability.VPVNP.PairSimulationResidentMapLoopExact

/-!
# Native map actions of the selected shrinking site

The packed row enumerates all resident motif-party occurrences. The gathers
and matrix routines use the current scratch in order, and their success
bits are determined by the typed inputs at those occurrences.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole.MapWitness

open BurstRAM DFS Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open CompressorRecords CompressorRecords.ShrinkSlots ShrinkMapImage.Registers
open ResidentMapLoop.Exact MapResidentRows

variable {g : ℕ} {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
  {t w endAddr : ℕ} (ord : B.Entry → Fin t) (i : Fin S.steps)
  (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
  (sel : X.ShrinkSelection B.shrink) (v : MapResidentRows.Site X)

private noncomputable local instance acceptanceBase : DecidableEq X.Base := Classical.decEq _

local notation "side" => selectedLayout X B.shrink sel
local notation "F" => ShrinkVertexImage.matrixFamily B ord i
local notation "G" => ShrinkVertexImage.gatherFamily B ord i

variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
  (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel)) v)
  (jobs : (q : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v) →
    ShrinkPartyNative.Job X B.shrink (S.shrink i) sel q.1.1 q.1.2 w)

set_option maxHeartbeats 1500000 in
-- The party index transports the hidden assignment to the selected occurrence.
/-- Matrix-entry input of a resident party job, with the site's hidden assignment transported
along the party's placement equality. -/
noncomputable abbrev jobInput (q : X.packingData.ResidentMap side v) :=
  ShrinkPartyNative.Job.entryInput B X (S.shrink i) sel q.1.1 q.1.2 (jobs q) (q.2.symm ▸ hidden)

variable (m : Memory w) (level term : Word w)
  (R : MapRowSource X sel (selectedLayout X B.shrink sel) m level term)
  (hw : MapConstants.widthThreshold B.shrink ≤ w)
  (pub : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v → Fin 5 → Word w)
  (workspace : (q : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v) →
    MapHandlerOperand.Workspace (w := w) (ShrinkVertexImage.matrixFamily B ord i)
      demandMass_pos (jobInput B i X sel v hidden jobs q))

set_option maxHeartbeats 2500000 in
-- The job and its workspace depend on the row index of the selected gathering routine.
/-- The native actions in the actual selected row order. Every later action
receives the scratch returned by its predecessor. -/
noncomputable def actions : List (Action w endAddr) :=
  List.ofFn fun j : Fin (order X side v).length => fun _ saved =>
    let q := rowEquiv X side v j
    rowAction (F) (G) X sel v m level term R j (jobInput B i X sel v hidden jobs q) (jobs q)
      hw (pub q) (workspace q) saved

end PairSimulation.ShrinkRole.MapWitness

end VPVNP
end Computability
end OAI
