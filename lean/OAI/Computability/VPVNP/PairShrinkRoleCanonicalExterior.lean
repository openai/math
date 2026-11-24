import OAI.Computability.VPVNP.PairShrinkMapExterior
import OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader
import OAI.Computability.VPVNP.PairShrinkSiteSources

/-!
# Exterior scratch at a selected shrinking site

The site's resident jobs share a histogram and hidden storage base. Every
successful scan therefore preserves each cell below the hidden storage and
outside the histogram, for any old, parent and hidden assignments.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM DFS Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open CompressorRecords CompressorRecords.ShrinkBlockInputs CompressorRecords.ShrinkSlots
open ShrinkMapImage.Registers ResidentMapLoop.Exact MapResidentRows NodeArguments
open scoped Fin.CommRing
open private jobPublic from OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates}
  {i : Fin S.steps} {g n w t packetEnd : ℕ}
  {X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g)}
  {sel : X.ShrinkSelection B.shrink} {v : MapResidentRows.Site X}
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

local notation "side" => selectedLayout X B.shrink sel
variable (site : CanonicalSite B i X sel v w n t) (ord : B.Entry ≃ Fin t)
  (old : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
    X.packingInputIso.site.symm) X.network.Half v)
  (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)
  (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
    (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel)) v)
local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "jobs" => ShrinkSiteBank.jobs B i X sel site.workspace site.positions site.blocks
  site.cur site.bounds n site.rowEnd site.older site.later v old parent
set_option quotPrecheck false in
local notation:max "pubAt" q:max => ShrinkSiteBank.pub site.level (((jobs q).node : ℕ) : Word w)
  regions n
local notation "row" => MapWitness.rowEquiv (a := S.degreeExponent i.castSucc) (g := g) X side v
local notation "heap" => ShrinkCallABI.hiddenBase regions n

attribute [local irreducible] MapWitness.actions ShrinkPartyNative.Job.entryInput

set_option maxHeartbeats 2200000 in
-- Identify the fitted workspaces and published operands with those in the site's ordered bank.
/-- The selected resident bank preserves every exterior cell below the hidden fields. -/
theorem canonicalBank_exterior (baseline : Word w → Word w)
    (packets : ∀ q, (jobs q).Packets packetEnd baseline)
    {T : IncidenceDirectory w} {origin : ℕ}
    (headers : ∀ j : Fin (order X side v).length, let q := row j
      (jobs q).OldPublished (ShrinkCallABI.operands (slotDegree S)) (pubAt q)
        (rowOrdinalWord (a := S.degreeExponent i.castSucc) (g := g) (w := w) X side v j)
        site.mem site.level T origin)
    (node : Word w) {initial final : Scratch w n} {es : List (Event w)}
    (run : scan node (canonicalBank site ord parent old hidden) initial = some (es, final))
    (address : Word w) (low : address.val < heap)
    (exterior : address.val < (regions).histBase ∨ (regions).histBase + t ≤ address.val) :
    rawScratch final address = rawScratch initial address := by
  have labels : t ≤ (regions).histWords := by
    change t ≤ Fintype.card B.Entry
    simpa only [Fintype.card_fin] using (Fintype.card_congr ord).ge
  exact MapWitness.scan_exterior (g := g) (w := w) (n := n) (t := t) (limit := site.limit)
    (packetEnd := packetEnd) (T := T) (origin := origin) (events := es) (out := final)
    B ord i X sel v hidden jobs site.mem site.level site.term
    site.source site.width (fun q ↦ pubAt q) (fun q ↦ site.fits q.1.1) regions node initial
    labels (fun _ ↦ rfl) (fun _ ↦ rfl) baseline packets headers (by
      simpa only [canonicalBank, MapWitness.fittedActions, MapWitness.mapWorkspaces, jobPublic, id]
        using run) address low exterior

local notation "layout" => BlockProgram.layout B site.workspace.val site.positions site.blocks
local notation "head" => DescriptorSpace.levelStart layout site.cur

set_option maxHeartbeats 2200000 in
-- Transport the popped node and chronological level into each row's physical source certificate.
/-- Physical source certificates at the producing level supply the old headers for the scan. -/
theorem canonicalBank_exterior_of_sources (baseline : Word w → Word w)
    (packets : ∀ q, (jobs q).Packets packetEnd baseline) (H : Word w)
    (here : site.level = (head : Word w))
    (sources : ∀ q, ShrinkSiteBank.RowSources B i X sel site.workspace site.positions site.blocks
      site.cur site.bounds n site.rowEnd site.older site.later v old parent site.mem H q)
    (node : Word w) {initial final : Scratch w n} {es : List (Event w)}
    (run : scan node (canonicalBank site ord parent old hidden) initial = some (es, final))
    (address : Word w) (low : address.val < heap)
    (exterior : address.val < (regions).histBase ∨ (regions).histBase + t ≤ address.val) :
    rawScratch final address = rawScratch initial address := by
  apply canonicalBank_exterior (T := DescriptorSpace.packedIncidence layout w site.cur
    (DemandRAM.oldCount X)) (origin := DescriptorSpace.tableBase layout site.cur (0 : Fin 6))
    site ord old parent hidden baseline packets _ node run address low exterior
  intro j
  dsimp only
  rw [here, ShrinkSiteBank.node_eq]
  exact (sources (row j)).old

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
