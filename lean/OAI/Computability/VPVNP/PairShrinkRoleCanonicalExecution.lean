import OAI.Computability.VPVNP.PairShrinkRoleCanonicalItems
import OAI.Computability.VPVNP.PairShrinkRolePhysicalSite
import OAI.Computability.VPVNP.PairShrinkRoleCanonicalData

/-!
# The canonical shrinking parser in the installed vertex image

A published site supplies the level, child, hidden and resident directories.
The parent packet supplies its half assignment. The physical stage switch
and the linked gathers implement the parser on all tapes and all compatible
incoming configurations.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open NetworkKernel CompressorRecords DescriptorSpace LocalHistory ShrinkBlockInputs ShrinkSlots
open VertexImage ShrinkVertexImage ShrinkMapImage.Registers MapResidentRows
open TraversalRows TraversalRoles TraversalControllerInputs NodeArguments NodeArguments.ChildScan
open ShrinkHiddenGuess
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates}
  {i : Fin S.steps} {g w n p r : ℕ} {Z : State (a i) (packingLaneBits (a i) g)}
  {sel : SelectedScore.Selection B Z} {v : MapResidentRows.Site Z}
  (site : CanonicalSite B i Z sel v w n (Fintype.card B.Entry))
  (ord : B.Entry → Fin (Fintype.card B.Entry))
  (geometry rootFields leaf refresh : Segment)
  (A : Placement (vertexParts B ord geometry rootFields leaf refresh) p r)
  (M : Machine w p r 11)
  {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
  {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes)
  (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT X).Choices)
  (j : Fin (executeLevels B f hf T hT X z).length)
  (id : Fin (executeLevels B f hf T hT X z)[j].outputSites) (base : ℕ)

private noncomputable local instance : DecidableEq Z.Base := Classical.decEq _
local notation "vs" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "side" => selectedLayout Z B.shrink sel
local notation "widths" => ShrinkPreparedCall.width B.shrink Z sel
local notation "Y" => Z.shrinkNext B.shrink (S.shrink i) sel
local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "heap" => ShrinkCallABI.hiddenBase regions n
local notation "seed" => ShrinkHiddenSlots.rows Z side widths v site.seed
local notation "nodeAddr" => site.later + (B.recordLimit + 2) *
  PortRefresh.ArgumentAddress.siteOrdinal (Y) v
local notation "rowAddr" => address B.recordLimit (layerBase B.recordLimit base tags (j.val + 1))
  id.val
local notation "jobs" => ShrinkSiteBank.jobs B i Z sel site.workspace site.positions site.blocks
  site.cur site.bounds n site.rowEnd site.older site.later v
set_option quotPrecheck false in
local notation "readerAt" => (shrinkPassReaders B f hf i rfl Z).termParsers sel

variable {first pitch offset publicH : ℕ} {raw : Memory w}
  (ds : (k : Fin (executeLevels B f hf T hT X z).length) →
    LevelDirectory (executeLevels B f hf T hT X z)[k] raw base)
  (resident : Resident M.publicData site.mem publicH first pitch offset B.recordLimit base
    ⟨leafLayer (siteOrder X), .cursor⟩ (levelFibers (executeLevels B f hf T hT X z) ds))

local notation "prv" => A.localRegs VertexImage.Part.shrink

private theorem source_cursor {left right : Word w} (eqn : left = right)
    (src : MapRowSource Z sel side site.mem left site.term) :
    firstMap B i (eqn ▸ src : MapRowSource Z sel side site.mem right site.term) v =
      firstMap B i src v := by cases eqn; rfl

private theorem source_published {left right : Word w} (eqn : left = right)
    (src : MapRowSource Z sel side site.mem left site.term)
    (published : MapResidentInputs.Published site.mem left
      ((ShrinkResidentLayout.layout Z src.first).params (a i) true w 3)
      ((ShrinkResidentLayout.layout Z src.first).params (a i) true w 5) site.term 10) :
    let aligned : MapRowSource Z sel side site.mem right site.term := eqn ▸ src
    MapResidentInputs.Published site.mem right
      ((ShrinkResidentLayout.layout Z aligned.first).params (a i) true w 3)
      ((ShrinkResidentLayout.layout Z aligned.first).params (a i) true w 5) site.term 10 := by
  cases eqn
  exact published

set_option maxHeartbeats 4000000 in
-- The fixed term, site directory and register banks are shared by all physical subprograms.
include resident in
/-- All child and hidden guesses, resident map reads, histogram stores and rejections
are those of the canonical family on the actual vertex host. -/
theorem canonicalFamily_exactOn (installed : Contains A M)
    (data : CanonicalSiteData site M f hf T hT X z j id base)
    (H : Word w) (parent : (Y).network.Half v) (mapData : CanonicalMapData site H parent)
    (ready : DFS.Scratch w n → Prop)
    (frame : ∀ priv, ready (DFS.scratch n priv) → ShrinkCallFrameLive.Stored regions n priv)
    (stored : ∀ s, ready s →
      (Packet.mk nodeAddr (packed (Y) v parent)).Stored (regions).arguments s) :
    (canonicalFamily site ord f hf parent).ExactOn (fun node s => node.val = rowAddr ∧ ready s)
      M (A.entry .shrink) (A.dfsPC 3) A.dfs site.mem := by
  let rows := vertex_rows B ord geometry rootFields leaf refresh A M installed
  have dreg (k l) : prv k ≠ A.dfs l := fun h =>
    vertex_dfs_apart B ord geometry rootFields leaf refresh A l ⟨k,h⟩
  have sreg (k l) : prv k ≠ A.saved l := fun h =>
    vertex_saved_apart B ord geometry rootFields leaf refresh A l ⟨k,h⟩
  let invariant := canonicalInv (p := p) site ord A.dfs prv ready
  have exactRows xs es := canonicalInv_items site ord f hf parent A.dfs prv ready xs es M
    (A.stage .shrink) A.saved (A.dfsPC 3) rows dreg sreg H mapData.terminalRoom data.levelEq
    mapData.sources mapData.space data.oldNodes data.parentFit data.earlier data.wire
    data.hiddenWidth data.hiddenRoom data.baseEq data.strideEq stored data.orderAt
  let source : MapRowSource Z sel side site.mem (levelHead M.publicData site.mem j.val)
      site.term := data.level ▸ site.source
  have cursor : firstMap B i source v = firstMap B i site.source v :=
    source_cursor site data.level site.source
  have physical := physicalSite_exactOn B ord M (A.stage .shrink) A.dfs A.saved prv (A.dfsPC 3)
    rows (fun l _ k => (dreg k l).symm) f hf T hT X z ds resident j id data.shrinking i
    data.index data.fit Z regions site.incidence site.older site.descriptor data.incidence
    data.strideFit site.hiddenArgs seed sel side v site.term source ready
    (canonicalActions site ord f hf parent) invariant frame data.above data.frameRoom
    (fun node atRow => by
      obtain ⟨dir, row⟩ := data.directory node (atRow.trans data.siteAddr.symm)
      exact ⟨dir.trans (congrArg (· + 14) data.level), row⟩)
    (fun _ _ u _ => ⟨data.oldNodes u, data.abovePointer u⟩) data.selectors data.rowStride
    (data.level ▸ data.headRoom) (data.level ▸ data.headers) data.countFit data.count data.valid
    data.baseEq (data.strideEq.trans (pow_two n)) (data.ownerEq.trans data.siteOrdinal)
    data.siteOrdinal (source_published site data.level site.source data.words)
    (canonicalActions_length site ord f hf parent) (fun node priv xs es c atRow good sites valid
      parsed operands => by
        apply canonicalInv_start (site := site) (ord := ord) (dfs := A.dfs) (reg := prv)
          (ready := ready) (xs := xs) (es := es) (p := p)
          (o := ⟨node, priv, c, atRow.trans data.siteAddr.symm, good, sites, valid, parsed,
            data.level.symm ▸ operands⟩))
    (fun xs es node => canonicalInv_stable site ord A.dfs prv ready xs es (A.stage .shrink)
      (A.dfsPC 3) node)
    (fun xs es => cursor ▸ exactRows xs es) (cursor ▸ data.mapRoom)
  have entryEq : A.entry .shrink = A.stage .shrink (shrinkSegment B ord).entry := rfl
  have degreeEq : a i = oldExponent i := rfl
  simpa only [canonicalFamily, data.publicData, data.levels, data.passIndex, data.level, entryEq,
    degreeEq] using physical

set_option maxHeartbeats 2500000 in
-- Specialization of the stored parent reader uses the selected output network.
include resident in
/-- One native parser covers all independently supplied parent halves at this physical site. -/
theorem canonicalParent_exactOn (installed : Contains A M)
    (data : CanonicalSiteData site M f hf T hT X z j id base) (H : Word w) (positive : 0 < w)
    (maps : ∀ parent, CanonicalMapData site H parent)
    (ready : (Y).network.Half v → DFS.Scratch w n → Prop)
    (frame : ∀ parent priv, ready parent (DFS.scratch n priv) →
      ShrinkCallFrameLive.Stored regions n priv)
    (stored : ∀ parent s, ready parent s →
      (Packet.mk nodeAddr (packed (Y) v parent)).Stored (regions).arguments s) :
    (canonicalParent site ord f hf).ExactOn
      (fun node s => node.val = rowAddr ∧ ∃ parent, ready parent s)
      M (A.entry .shrink) (A.dfsPC 3) A.dfs site.mem := by
  apply parentParser_exactOn (Y) v (regions).arguments (canonicalFamily site ord f hf) M
    (A.entry .shrink) (A.dfsPC 3) A.dfs site.mem positive rowAddr ready
    (fun parent s good => data.siteAddr ▸ stored parent s good)
  intro parent
  exact canonicalFamily_exactOn site ord geometry rootFields leaf refresh A M f hf T hT X z
    j id base ds resident installed data H parent (maps parent) (ready parent) (frame parent)
    (stored parent)

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
