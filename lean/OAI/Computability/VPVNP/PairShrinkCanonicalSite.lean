import OAI.Computability.VPVNP.PairShrinkCanonicalWorkspaceFit
import OAI.Computability.VPVNP.PairShrinkRoleChild
import OAI.Computability.VPVNP.PairShrinkSiteBank
import OAI.Computability.VPVNP.PairSimulationShrinkGatherSource

/-! # Physical directories and workspace bounds at a selected shrinking site -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM DFS Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open CompressorRecords CompressorRecords.ShrinkBlockInputs CompressorRecords.ShrinkSlots
open LocalHistory NodeArguments NodeArguments.ChildScan ShrinkHiddenGuess
open ShrinkMapImage.Registers MapResidentRows
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
  (i : Fin S.steps) {g : ℕ} (X : State (a i) (packingLaneBits (a i) g))
  (sel : X.ShrinkSelection B.shrink) (v : MapResidentRows.Site X)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

local notation "side" => selectedLayout X B.shrink sel
local notation "widths" => ShrinkPreparedCall.width B.shrink X sel
local notation "Hidden" => Placed (X.packingData.shrinkInternalOwner side)
  (internalLabel widths side) v

/-- Addresses, field directories and workspace bounds for one selected site. -/
structure CanonicalSite (w n t : ℕ) where
  /-- Base word address of the compressor's descriptor workspace. -/
  workspace : Word w
  /-- Number of processor positions used when laying out the compressor's workspace. -/
  positions : ℕ
  /-- Number of complete scheduled blocks in the compressor's workspace layout. -/
  blocks : ℕ
  /-- Chronological pass index used to locate the producing level and its tables. -/
  cur : ℕ
  bounds : ShrinkResidentSources.Bounds B i X workspace positions blocks cur
  /-- Exclusive end address of the selected traversal's node rows. -/
  rowEnd : ℕ
  /-- Base address of the input layer's node rows. -/
  older : ℕ
  /-- Base address of the output layer's node rows. -/
  later : ℕ
  /-- Upper address bound on the canonical jobs' private workspaces. -/
  limit : ℕ
  fits : ∀ m, canonicalFits B i X sel (w := w) t n rowEnd older limit m
  /-- Physical memory read by the vertex handler at this site. -/
  mem : Memory w
  /-- Word address of the header for the producing compressor level. -/
  level : Word w
  /-- Word address of the shrinking term records for the producing level. -/
  term : Word w
  /-- Published map directory and term data read at this site from the specified memory. -/
  source : MapRowSource X sel side mem level term
  width : MapConstants.widthThreshold B.shrink ≤ w
  /-- The eleven public operand words of the terminal vertex program. -/
  publicData : Fin 11 → Word w
  /-- Number of passes in the selected chronological execution. -/
  levels : ℕ
  /-- Pass ordinal supplied to the vertex handler for this row. -/
  passIndex : ℕ
  /-- Directory of the packed incidence columns used to recover the old wire endpoints. -/
  incidence : IncidenceDirectory w
  /-- Child-argument descriptor selected by the popped node address. -/
  descriptor : Word w → ChildArguments.Descriptor w X
  /-- Addresses and row parameters for guessing the hidden fields at this site. -/
  hiddenArgs : Args w
  /-- Initial assignment of the hidden fields placed at this site. -/
  seed : Hidden

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
