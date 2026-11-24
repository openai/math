import OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader
import OAI.Computability.VPVNP.PairShrinkRoleMapAcceptance

/-! # Exact suffix of the canonical shrinking parser at a prepared parent -/

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
local notation "Y" => X.shrinkNext B.shrink (S.shrink i) sel
variable {B i X sel v} {t w n : ℕ}
  (site : CanonicalSite B i X sel v w n t) (ord : B.Entry → Fin t)

local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "jobs" => ShrinkSiteBank.jobs B i X sel site.workspace site.positions site.blocks
  site.cur site.bounds n site.rowEnd site.older site.later v
variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
open private termAt readerAt childOrder from OAI.Computability.VPVNP.PairShrinkRoleScheduledSuffix
local notation "readers" => readerAt B f hf i X sel
local notation "orderAt" => childOrder B f hf i X sel v

local notation "childLoad" => selectedChildSetup site.publicData site.mem site.levels site.passIndex
  S.steps i.val (a i)
local notation "hiddenLoad" => physicalHiddenSetup B.shrink.selectorBits (hiddenStride i)
  site.level.val site.mem
local notation "mapLoad" => mapStartSetup site.mem site.level (Fin.val (siteIndex X v) : Word w)

open private jobPublic from OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader

attribute [local irreducible] ResidentMapLoop.Exact.scan MapWitness.actions

set_option maxHeartbeats 1000000 in
-- Align the selected physical stage's placement and half types with the scheduled term.
theorem canonicalParent_suffix (parent : (Y).network.Half v) (node : Word w) (saved : Scratch w n)
    (stored : (Packet.mk node.val (packed (Y) v parent)).Stored (regions).arguments saved)
    (positive : 0 < w)
    (order : (site.descriptor node).sites = List.ofFn fun j => ((orderAt).entries j).val)
    (bits : List Bool) :
    ((canonicalParent site ord f hf).read node saved bits).map Prod.snd =
      ((TreeDecode.nodeReader readers v parent).read bits).map Prod.snd := by
  have read := parentParser_read (Y) v (regions).arguments (canonicalFamily site ord f hf)
    node saved parent stored positive bits
  refine (congrArg (Option.map Prod.snd) read).trans ?_
  unfold canonicalFamily
  refine scheduledSuffix B f hf i X sel v parent site.seed (regions).arguments site.incidence
    site.mem site.older B.recordLimit site.descriptor (fun _ => site.hiddenArgs)
    (canonicalActions site ord f hf parent) childLoad (fun _ => hiddenLoad) (fun _ _ => mapLoad)
    node saved order ?_ bits
  intro old hidden tail out xs _ value
  have same : canonicalActions site ord f hf parent xs out.value =
      canonicalBank site ord parent old hidden := by
    rw [value]
    exact typedActions_encoded (term := termAt B f hf i X sel) X v orderAt side
      (ShrinkPreparedCall.width B.shrink X sel) v site.seed
      (canonicalBank site ord parent) old hidden
  rw [same]
  unfold canonicalBank
  exact MapWitness.scan_accepts (g := g) (t := t) (w := w) (endAddr := n) B ord i X sel v hidden
    (jobs old parent) site.mem site.level
    site.term site.source site.width (jobPublic site old parent) _ old parent
    (fun _ => rfl) (fun _ => rfl) node _

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
