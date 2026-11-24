import OAI.Computability.VPVNP.PairShrinkSiteSources
import OAI.Computability.VPVNP.PairShrinkGatherTraceReads
import OAI.Computability.VPVNP.PairTerminalFootprint

/-!
# Public trace of each certified resident occurrence

The interval gathers and the map argument reads use the same recorded
operand registers. Their read domains follow directly from the two
published row banks and the selected term's extent.
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
private noncomputable local instance fieldReadsBase : DecidableEq X.Base := Classical.decEq _
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

variable (sources : RowSources B i X sel workspace positions blocks cur bounds n rowEnd
  older later v x parent phy H q)

variable {B i X sel workspace positions blocks cur bounds n rowEnd older later v x parent phy H q}
include sources

/-- Each public interval setup and copy in this resident stays in the worker read domain. -/
theorem RowSources.gather_reads (room : H.val + 31 < 2 ^ w) :
    SourceTransport.Reads (TerminalLink.workerCell H)
      ((job).trace O ShrinkCallABI.node P st phy) :=
  (job).trace_reads O ShrinkCallABI.node P st phy (TerminalLink.workerCell H)
    sources.old sources.next ((job).abi_readSafe (slotDegree S) H room
      sources.old sources.next sources.abArea sources.supplyArea)

/-- The complete successful matrix event sequence reads only the row's recorded operands. -/
theorem RowSources.success_reads {t : ℕ} (ordinal : B.Entry → Fin t)
    (arg : LocalHistory.EntryInput B.shrink) (width : MapConstants.widthThreshold B.shrink ≤ w)
    (room : H.val + 31 < 2 ^ w) :
    SourceTransport.Reads (TerminalLink.workerCell H)
      ((ShrinkCallABI.family B (slotDegree S) (a i) ordinal).successEvents
        demandMass_pos arg width P st phy) :=
  TerminalFootprint.reads_mono ((job).abi_success_reads (slotDegree S) B ordinal
    sources.old sources.abArea sources.termEnd arg width)
    (fun _ lo ↦ TerminalLink.workerCell_of_lt room lo)

end PairSimulation.ShrinkSiteBank

end VPVNP
end Computability
end OAI
