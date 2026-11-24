import OAI.Computability.VPVNP.PairShrinkRoleMapActions
import OAI.Computability.VPVNP.PairSimulationMapScanAcceptance

/-!
# Acceptance of the selected shrinking site's native map scan

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

private noncomputable local instance acceptanceProofBase : DecidableEq X.Base := Classical.decEq _

local notation "side" => selectedLayout X B.shrink sel
local notation "F" => ShrinkVertexImage.matrixFamily B ord i
local notation "G" => ShrinkVertexImage.gatherFamily B ord i

variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
  (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel)) v)
  (jobs : (q : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v) →
    ShrinkPartyNative.Job X B.shrink (S.shrink i) sel q.1.1 q.1.2 w)

variable (m : Memory w) (level term : Word w)
  (R : MapRowSource X sel (selectedLayout X B.shrink sel) m level term)
  (hw : MapConstants.widthThreshold B.shrink ≤ w)
  (pub : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v → Fin 5 → Word w)
  (workspace : (q : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v) →
    MapHandlerOperand.Workspace (w := w) (ShrinkVertexImage.matrixFamily B ord i)
      demandMass_pos (jobInput B i X sel v hidden jobs q))

variable (old : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
    X.packingInputIso.site.symm) X.network.Half v)
  (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)

set_option maxHeartbeats 2500000 in
-- The native input is indexed simultaneously by the site, party and the scheduled matrix family.
/-- The actual shrinking map scan succeeds on any starting scratch exactly
when the scheduled kernel's interpreters accept every resident occurrence. -/
theorem scan_accepts
    (children : ∀ q, (jobs q).old = Eq.rec (motive := fun u _ => Placed
      (X.packingData.shrinkPlace side) (X.packingData.oldWireNetwork X.packingWidth).Half u)
      (placedOld B i X sel v old) q.2.symm)
    (newHalf : ∀ q, (jobs q).parent = Eq.rec (motive := fun u _ =>
      (X.shrinkNext B.shrink (S.shrink i) sel).network.Half u) parent q.2.symm)
    (node : Word w) (saved : Scratch w endAddr) :
    (scan node (actions B ord i X sel v hidden jobs m level term R hw pub workspace) saved).isSome ↔
      ∀ q, (names B (input B i X sel v old parent hidden q)).isSome := by
  let idx := rowEquiv X side v
  let accept (q : X.packingData.ResidentMap side v) :=
    (names B (input B i X sel v old parent hidden q)).isSome = true
  unfold actions
  refine (scan_ofFn_iff node _ (fun j => accept (idx j)) ?_ saved).trans idx.forall_congr_right
  intro j scratch
  let q := idx j
  let I := jobInput B i X sel v hidden jobs q
  change (rowAction (F) (G) X sel v m level term R j I (jobs q) hw (pub q) (workspace q)
    scratch).isSome = true ↔ _
  have native := rowAction_isSome (g := g) (ready := S.shrink i) (jobMotif := q.1.1)
    (F) (G) X sel v m level term R j I (jobs q) hw (pub q) (workspace q) scratch
  have equal : I = input B i X sel v old parent hidden q :=
    ShrinkPartyNative.Job.entryInput_eq_witness B i X sel v old parent hidden q (jobs q)
      (children q) (newHalf q)
  have labels : (MapHandlerOperand.names (F) demandMass_pos I).isSome =
      (names B (input B i X sel v old parent hidden q)).isSome := by
    change ((names B I).map (List.map (F).ordinal)).isSome = _
    rw [Option.isSome_map, equal]
  exact Iff.of_eq (congrArg (· = true) (native.trans labels))

end PairSimulation.ShrinkRole.MapWitness

end VPVNP
end Computability
end OAI
