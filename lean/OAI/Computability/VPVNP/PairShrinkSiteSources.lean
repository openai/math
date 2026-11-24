import OAI.Computability.VPVNP.PairShrinkResidentPublication
import OAI.Computability.VPVNP.PairShrinkCanonicalReadAreas

/-!
# The native source rows of a selected shrinking site

All resident jobs draw their descriptor, old and surviving intervals and term
fields from the same producing level. The original and successor DFS row
pointers identify the old children and the popped parent.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSiteBank

open BurstRAM Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open CompressorRecords DescriptorSpace ShrinkBlockInputs ShrinkSlots
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
private noncomputable local instance bankBase : DecidableEq X.Base := Classical.decEq _
variable (workspace : Word w) (positions blocks cur : ℕ)
variable (bounds : ShrinkResidentSources.Bounds B i X workspace positions blocks cur)
variable (n rowEnd older later : ℕ)
variable (v : (X.Base × BitWord (packingTagBits (2 ^ a i))) × BitWord g)
variable (x : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
  X.packingInputIso.site.symm) X.network.Half v)
variable (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)
variable (phy : Memory w) (H : Word w)
local notation "side" => selectedLayout X B.shrink sel
variable (q : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v)
local notation "job" => jobs B i X sel workspace positions blocks cur bounds n rowEnd older later
  v x parent q
local notation "L" => BlockProgram.layout B workspace.val positions blocks
local notation "here" => levelStart L cur
local notation "nextHead" => levelStart L (cur + 1)
local notation "cut" => tableBase L cur (0 : Fin 6)
local notation "T" => packedIncidence L w cur (DemandRAM.oldCount X)
local notation "shape" => levelShape (b := b i) X
local notation "U" => packedIncidence L w (cur + 1) (actualCount shape)
local notation "term" => ShrinkInput.termHead (w := w) X cut
local notation "heads" => ShrinkOutput.heads shape (SelectedArena.roleBase X term 10)
  (tableBase L cur (3 : Fin 6))
local notation "absHead" => ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X cut) w
local notation "regns" => TerminalLayout.privateRegions (slotDegree S) n rowEnd
  (Fintype.card B.Entry)
local notation "Y" => X.shrinkNext B.shrink (S.shrink i) sel
local notation "node" => (later + (B.recordLimit + 2) *
  PortRefresh.ArgumentAddress.siteOrdinal Y v : ℕ)
local notation "P" => pub (here : Word w) (node : Word w) regns n
local notation "O" => ShrinkCallABI.operands (slotDegree S)
local notation "motif" => Prod.fst (Subtype.val q)
local notation "st" => Nat.cast (R := Word w) (Fin.val (ShrinkMotifOrder.stateNumber X motif))

/-- Per-row inputs to both native scans and the map argument writer. -/
structure RowSources : Prop where
  old : (job).OldPublished O P st phy (here : Word w) T cut
  next : (job).SupplyPublished O ShrinkCallABI.node P st phy heads absHead U later
    (B.recordLimit + 2)
  abArea : (job).ABAreas (here : Word w) T cut H.val
  supplyArea : (job).SupplyAreas (here : Word w) absHead heads U nextHead H.val phy
  termEnd : ShrinkInput.termEnd X cut 10 ≤ H.val
  two : 2 < 2 ^ w
  termRoom : ShrinkInput.termEnd X cut 10 < 2 ^ w
  pairs : ShrinkTermInputs.statePairs X (ShrinkInput.demandHead X cut) phy
  fields : TermRecordScan.Fields B.shrink ShrinkSliceArrays.supplyRoles demandMass_pos
    (ShrinkPreparedCall.widthsDemand X motif) (sel motif).val
    (ShrinkTermSelection.rowBase X term 10 motif) phy

set_option maxHeartbeats 2000000 in
-- Reducing the common job fields identifies the exact parent and both physical interval banks.
/-- Extract every resident's source contract and the checked read ranges
from the producing pass's retained data. -/
theorem rowSources
    (words : ShrinkResidentHeaders.Words B i X sel workspace positions blocks cur n phy)
    (data : ShrinkResidentSources.Data B i X (S.shrink i) sel workspace positions blocks cur phy)
    (oldLayer : phy (here + 14) = (older : Word w))
    (newLayer : phy (nextHead + 14) = (later : Word w))
    (newStride : phy (nextHead + 15) = ((B.recordLimit + 2 : ℕ) : Word w))
    (beforeHeader : endAddress L ≤ H.val) :
    RowSources B i X sel workspace positions blocks cur bounds n rowEnd older later v x parent
      phy H q := by
  have evaluated := ShrinkResidentPublication.published_words B i X (S.shrink i) sel motif q.1.2
    workspace positions blocks cur bounds n rowEnd older later (job).old (job).parent phy
    words data oldLayer newLayer newStride
  change (job).OldPublished O (pub (here : Word w) ((job).node : Word w) regns n) st
    phy (here : Word w) T cut ∧ (job).SupplyPublished O ShrinkCallABI.node
      (pub (here : Word w) ((job).node : Word w) regns n) st phy heads absHead U later
      (B.recordLimit + 2) at evaluated
  rw [node_eq] at evaluated
  have safe := ShrinkCanonicalJob.read_areas B i X (S.shrink i) sel motif q.1.2 workspace
    positions blocks cur bounds (job) rfl rfl H phy beforeHeader words.supply.successor
  exact ⟨evaluated.1, evaluated.2, safe.1, safe.2.1, safe.2.2,
    (ShrinkCanonicalJob.geometry B i X (S.shrink i) sel motif workspace
      positions blocks cur bounds).two, safe.2.2.trans_lt H.isLt, data.pairs, data.terms motif⟩

end PairSimulation.ShrinkSiteBank

end VPVNP
end Computability
end OAI
