import OAI.Computability.VPVNP.PairShrinkRoleBankHistogramSum
import OAI.Computability.VPVNP.PairShrinkRoleMapLabels
import OAI.Computability.VPVNP.PairShrinkSiteSources

/-!
# The scheduled exponent in the physical shrinking histogram

The selected site's row enumerates its resident motif parties. The actual
private gather and grouped map at each occurrence add their emitted names
to the common counters. Summing those stores in row order gives the exponent
of the local kernel witness, including repetitions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

section Histogram

open BurstRAM DFS Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open CompressorRecords CompressorRecords.ShrinkBlockInputs CompressorRecords.ShrinkSlots
open ShrinkMapImage.Registers ResidentMapLoop.Exact MapResidentRows NodeArguments
open scoped Fin.CommRing

variable {K : Type} {C : Type*} [_root_.Field K] [CommRing C] {S : BlockSchedule K}
  {B : S.Templates}
  {i : Fin S.steps} {g n w t packetEnd : ℕ}
  {X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g)}
  {sel : X.ShrinkSelection B.shrink} {v : MapResidentRows.Site X}
open private rowBase from OAI.Computability.VPVNP.PairShrinkRoleBankHistogramStep
attribute [local instance] rowBase
set_option allowUnsafeReducibility true in
attribute [local reducible] rowBase Compression.PackingData.shrinkTermLayout
set_option allowUnsafeReducibility true in
attribute [local irreducible] Compression.ShrinkEnergy.chosenLayout

variable (site : CanonicalSite B i X sel v w n t) (ord : B.Entry ≃ Fin t)
  (f : B.Entry → C) (hf : B.IsSolution f)
  (old : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
    X.packingInputIso.site.symm) X.network.Half v)
  (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)
local notation "W" => B.shrinkPassWitnesses f hf i rfl X sel v old parent
local notation "side" => selectedLayout X B.shrink sel
local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "jobs" => ShrinkSiteBank.jobs (g := g) (w := w) B i X sel site.workspace
  site.positions site.blocks
  site.cur site.bounds n site.rowEnd site.older site.later v old parent
open private jobPublic from OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader
local notation:max "pubAt" q:max => jobPublic site old parent q
local notation "row" => MapWitness.rowEquiv (a := a i) (g := g) X side v
set_option quotPrecheck false in
local notation:max "bin" l:max => (((regions).histBase + (ord l).val : ℕ) : Word w)

set_option maxHeartbeats 1000000 in
-- Expose the selected hidden assignment once without unfolding every resident matrix.
private noncomputable abbrev witnessHidden (x : (W).Choice) :
    Placed (X.packingData.shrinkInternalOwner side)
      (internalLabel (ShrinkPreparedCall.width B.shrink X sel) side) v := x.1

local notation:max "absorbed" x:max => witnessHidden (B := B) (i := i) (X := X) (sel := sel)
  (v := v) f hf old parent x
attribute [local irreducible] ResidentMapLoop.Exact.scan MapWitness.actions canonicalBank
  MapWitness.names MapWitness.input NodeArguments.rawScratch

set_option maxHeartbeats 1800000 in
-- Compare the same packed witness in the scheduled, physical and resident map indices.
/-- Every successful scan of the site's actual gather and matrix rows adds its
scheduled local exponent to the indicated private word. -/
theorem canonicalBank_histogram (x : (W).Choice) (baseline : Word w → Word w)
    (packets : ∀ q, (jobs q).Packets packetEnd baseline)
    {T : IncidenceDirectory w} {origin : ℕ}
    (headers : ∀ j, let q := row j
      (jobs q).OldPublished (ShrinkCallABI.operands (slotDegree S)) (pubAt q)
        (rowOrdinalWord X side v j) site.mem site.level T origin)
    (node : Word w) {initial final : Scratch w n} {es : List (Event w)}
    (scanOk : scan node (canonicalBank site (⇑ord) parent old (absorbed x)) initial =
      some (es, final))
    (l : B.Entry) :
    rawScratch final (bin l) = rawScratch initial (bin l) + ((W).exponents x l : Word w) := by
  have counts := canonicalBank_counts (B := B) (i := i) (X := X) (sel := sel) (v := v)
    site ord old parent (absorbed x) baseline packets headers node scanOk l
  have total := MapWitness.ordinal_sum B f hf i X sel v old parent ord x l
  exact counts.trans (congrArg (fun k : ℕ => rawScratch initial (bin l) + (k : Word w)) total)

end Histogram

section Header

open BurstRAM DFS Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open CompressorRecords CompressorRecords.ShrinkBlockInputs CompressorRecords.ShrinkSlots
open ShrinkMapImage.Registers ResidentMapLoop.Exact MapResidentRows NodeArguments
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K}
  {B : S.Templates}
  {i : Fin S.steps} {g n w t : ℕ}
  {X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g)}
  {sel : X.ShrinkSelection B.shrink} {v : MapResidentRows.Site X}
private noncomputable local instance countSiteBase : DecidableEq X.Base := Classical.decEq _

variable (site : CanonicalSite B i X sel v w n t)
  (old : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
    X.packingInputIso.site.symm) X.network.Half v)
  (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)
local notation "side" => selectedLayout X B.shrink sel
local notation "jobs" => ShrinkSiteBank.jobs B i X sel site.workspace site.positions site.blocks
  site.cur site.bounds n site.rowEnd site.older site.later v old parent
open private jobPublic from OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader
local notation:max "pubAt" q:max => jobPublic site old parent q
local notation "row" => MapWitness.rowEquiv X side v

local notation "layout" => BlockProgram.layout B site.workspace.val site.positions site.blocks
local notation "head" => DescriptorSpace.levelStart layout site.cur

set_option maxHeartbeats 2200000 in
-- Identifying the physical row transports the node pointer and the same dense ordinal.
/-- The selected vertex's row certificate supplies the actual old-header
operand at each ordered job, including its loaded node and stage words. -/
theorem canonicalOldPublished (H : Word w) (here : site.level = (head : Word w))
    (sources : ∀ q, ShrinkSiteBank.RowSources B i X sel site.workspace site.positions site.blocks
      site.cur site.bounds n site.rowEnd site.older site.later v old parent site.mem H q)
    (j : Fin (order X side v).length) :
    let q := row j
    (jobs q).OldPublished (ShrinkCallABI.operands (slotDegree S)) (pubAt q)
      (rowOrdinalWord X side v j) site.mem site.level
      (DescriptorSpace.packedIncidence layout w site.cur (DemandRAM.oldCount X))
      (DescriptorSpace.tableBase layout site.cur (0 : Fin 6)) := by
  dsimp only
  rw [jobPublic, here, ShrinkSiteBank.node_eq]
  exact (sources (row j)).old

end Header

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
