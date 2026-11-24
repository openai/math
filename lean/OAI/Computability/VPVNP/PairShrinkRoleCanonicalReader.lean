import OAI.Computability.VPVNP.PairShrinkCanonicalSite
import OAI.Computability.VPVNP.PairShrinkRoleMapActions
import OAI.Computability.VPVNP.PairShrinkRoleParent
import OAI.Computability.VPVNP.PairShrinkRoleTypedActions
import OAI.Computability.VPVNP.PairShrinkRoleSelectedChildren
import OAI.Computability.VPVNP.PairShrinkRolePhysicalHidden
import OAI.Computability.VPVNP.PairShrinkRoleMapStart
import OAI.Computability.VPVNP.PairShrinkSiteBank

/-!
# The canonical parser for a selected shrinking site

The parent packet, the child descriptors and the absorbed fields select the
concrete jobs for one physical shrinking site. Each job gathers from the
site's arena and runs the selected matrix in the fitted private workspace.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM DFS Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open CompressorRecords CompressorRecords.ShrinkBlockInputs CompressorRecords.ShrinkSlots
open LocalHistory NodeArguments NodeArguments.ChildScan ShrinkHiddenGuess
open ShrinkVertexImage ShrinkMapImage.Registers MapResidentRows ResidentMapLoop.Exact
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
  (i : Fin S.steps) {g : ℕ} (X : State (a i) (packingLaneBits (a i) g))
  (sel : X.ShrinkSelection B.shrink) (v : MapResidentRows.Site X)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

local notation "side" => selectedLayout X B.shrink sel
local notation "widths" => ShrinkPreparedCall.width B.shrink X sel
local notation "Y" => X.shrinkNext B.shrink (S.shrink i) sel
local notation "Old" => Placed (X.packingData.shrinkPlace side ∘ X.packingInputIso.site.symm)
  X.network.Half v
local notation "Hidden" => Placed (X.packingData.shrinkInternalOwner side)
  (internalLabel widths side) v

variable {B i X sel v} {t w n : ℕ}
  (site : CanonicalSite B i X sel v w n t) (ord : B.Entry → Fin t)

local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "jobs" => ShrinkSiteBank.jobs B i X sel site.workspace site.positions site.blocks
  site.cur site.bounds n site.rowEnd site.older site.later v
private noncomputable abbrev jobPublic (old : Old) (parent : (Y).network.Half v)
    (q : X.packingData.ResidentMap side v) : Fin 5 → Word w :=
  ShrinkSiteBank.pub site.level ((jobs old parent q).node : Word w) regions n

section

-- Keep the selected input intact when checking the type of its fitted workspace.
attribute [local irreducible] ShrinkPartyNative.Job.entryInput
/-- The physical row's ordered resident jobs with their actual map operands. -/
noncomputable def canonicalBank (parent : (Y).network.Half v) (old : Old) (hidden : Hidden) :
    List (Action w n) :=
  MapWitness.actions (g := g) (w := w) (endAddr := n) B ord i X sel v hidden (jobs old parent)
    site.mem site.level site.term site.source site.width (jobPublic site old parent) fun q => by
      unfold MapWitness.jobInput matrixFamily
      exact ShrinkPartyNative.Job.mapWorkspace (a := a i) (b := b i) (g := g) (t := t) (w := w)
        (n := n) (limit := site.limit) B (slotDegree S) ord X (S.shrink i) sel q.1.1 q.1.2
        (jobs old parent q) (q.2.symm ▸ hidden) (site.fits q.1.1)

end

variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
open private termAt readerAt childOrder from OAI.Computability.VPVNP.PairShrinkRoleScheduledSuffix
local notation "chosen" => termAt B f hf i X sel
local notation "readers" => readerAt B f hf i X sel
local notation "orderAt" => childOrder B f hf i X sel v

/-- Index the row's jobs by the physical child and hidden reader outputs. -/
noncomputable def canonicalActions (parent : (Y).network.Half v) :
    List (Child X) → List Row → List (Action w n) :=
  typedActions (term := chosen) X v orderAt side widths v site.seed
    (canonicalBank site ord parent)

local notation "childLoad" => selectedChildSetup site.publicData site.mem site.levels site.passIndex
  S.steps i.val (a i)
local notation "hiddenLoad" => physicalHiddenSetup B.shrink.selectorBits (hiddenStride i)
  site.level.val site.mem
local notation "mapLoad" => mapStartSetup site.mem site.level (Fin.val (siteIndex X v) : Word w)

/-- The shrinking visit with its parent fixed and the incoming tape unrestricted. -/
noncomputable def canonicalFamily (parent : (Y).network.Half v) : HookParser w n :=
  hook (visitReader (regions).arguments site.incidence site.mem site.older B.recordLimit
    site.descriptor (fun _ => site.hiddenArgs)
    (fun _ => ShrinkHiddenSlots.rows X side widths v site.seed)
    (canonicalActions site ord f hf parent) childLoad (fun _ => hiddenLoad) (fun _ _ => mapLoad))

/-- Decode the parent at the popped address and then run its selected shrinking visit. -/
noncomputable def canonicalParent : HookParser w n :=
  parentParser (Y) v (regions).arguments (canonicalFamily site ord f hf)

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
