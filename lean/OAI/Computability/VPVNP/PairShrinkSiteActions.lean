import OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader
import OAI.Computability.VPVNP.PairShrinkLiveOperands
import OAI.Computability.VPVNP.PairShrinkGatherQuiet

/-!
# Determinism and live operands of a scheduled shrinking site

All occurrences share a single hidden region and argument arena. The loop
carries its initial public registers, the argument words below the histogram
and the shared hidden words. Each occurrence gathers and evaluates its own
selected input.
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

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

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

set_option maxHeartbeats 1300000 in
-- Each action gathers from the row's selected party, then runs its local matrix.
/-- The packed resident action list is deterministic for every public row and map workspace. -/
theorem quiet (act : Action w endAddr)
    (ha : act ∈ actions B ord i X sel v hidden jobs m level term R hw pub workspace) :
    NoChoices act := by
  unfold actions at ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
  let q := rowEquiv X side v j
  let I := jobInput B i X sel v hidden jobs q
  let key := MapHandlerOperand.index demandMass_pos I
  intro _ saved es updated got
  exact rowAction_noChoices (F) (G) X sel v m level term R j I (jobs q) hw (pub q)
    (workspace q) saved ((jobs q).trace_noChoices ((G).operands key) ((G).node key) (pub q)
      (rowOrdinalWord (w := w) X side v j) m) got

end PairSimulation.ShrinkRole.MapWitness

namespace PairSimulation.ShrinkSiteBank

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open NetworkKernel CompressorRecords DescriptorSpace ShrinkBlockInputs ShrinkSlots
open ShrinkVertexImage ShrinkMapImage.Registers MapResidentRows ShrinkRole ShrinkRole.MapWitness
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates} {i : Fin S.steps}
variable {g w n t : ℕ} {X : State (a i) (packingLaneBits (a i) g)}
variable {sel : SelectedScore.Selection B X} {v : Site X}
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
variable (site : CanonicalSite B i X sel v w n t) (ord : B.Entry → Fin t)
variable (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)
variable (old : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
    X.packingInputIso.site.symm) X.network.Half v)
variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
    (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel)) v)
local notation "side" => selectedLayout X B.shrink sel
local notation "J" => jobs B i X sel site.workspace site.positions site.blocks site.cur site.bounds
  n site.rowEnd site.older site.later v old parent
local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)

/-- The row reader, interval gather and selected local matrix consume no choice bits. -/
theorem actions_quiet (act : ResidentMapLoop.Exact.Action w n)
    (inRow : act ∈ canonicalBank site ord parent old hidden) :
    ResidentMapLoop.Exact.NoChoices act := by
  unfold canonicalBank at inRow
  exact MapWitness.quiet B ord i X sel v hidden (J) site.mem site.level site.term site.source
    site.width _ _ act inRow

variable {p r : ℕ} (common : Fin 24 ↪ Fin r) (initial : Config w p r)

/-- Register and physical operand invariant, independent of the resident
currently selected by the cursor. -/
noncomputable abbrev siteInvariant (_ : Word w) (c : Config w p r) : Prop :=
  ShrinkResidentMemory.Invariant
    (ShrinkCallHeader.scratch X (ShrinkCallABI.hiddenBase regions n) (n ^ 2) (regions).histBase)
    initial.privateMem (residentLive common) initial.reg c

theorem siteInvariant_start (u : Word w) : siteInvariant site common initial u initial :=
  ShrinkResidentMemory.Invariant.start _ initial _

theorem siteInvariant_stable
    (pc : Fin (shrinkSegment B ord).count → Fin p)
    (reg : Fin (shrinkSegment B ord).privateRegs ↪ Fin r) (done : Fin p) (u : Word w) :
    (mapLoop B ord i pc reg done).Stable
      (siteInvariant site (shared B ord i reg) initial u) :=
  ShrinkResidentMemory.Invariant.stable _ _ _ _ _ (residentLive_cursor _)

end PairSimulation.ShrinkSiteBank

end VPVNP
end Computability
end OAI
