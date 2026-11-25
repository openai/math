import OAI.Hierarchy.DescentTerminalSourceAddressBound
import OAI.Hierarchy.DescentTerminalBranchLibrary
import OAI.Hierarchy.DescentTerminalPlacedChip

namespace OAI
/-! # The true selected graph fits both adjacent reads of the physical joined bank -/
namespace Hierarchy.DescentTerminalEmitter
open DescentTerminalChipRuntime DescentTerminalChipPins DescentTerminalChipSource DescentTerminalChronologicalChip
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open DescentTerminalSiteShelves DescentTerminalHeaderScatter
open DescentKernelHistory DescentBundleHistory DescentEpochTagKeys DescentTerminalGraphPositions
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow DescentTerminalPorts DescentTerminalCableOrder
open DescentTerminalBinReaddress DescentTerminalRecipeRows DescentTerminalScalarTransposes
open ThreeFlat.Routing Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open Computability.BorderVNP.Crossing
open DescentTerminalVertexFields DescentSixParty DescentCompiler
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false

open DescentTerminalScalarPadded

namespace Branch
variable {F P U : Type} [Field F] [Fintype P] {ew:P→ℕ}
variable {D k age zStage degree wire hist K₀ W q piece bitsW H nodesN addrN verts initial arity groups stride : ℕ}
variable {G:PoweredGadget F} {ε price:ℝ} {σ:AtomSchedule}
variable (cfg:DescentTerminalCompiledPrefix.Shape)
local notation "p" => W*piece
local notation "S" => σ.hostSize age

variable {world:MarkedWorld F D P ew} {live:DescentSixParty.Reached world G price ε σ k age zStage degree wire hist}
variable (l:Leaf cfg world live U W q piece H nodesN addrN verts)
local notation "net" => world.graph
local notation "raw" => RowBit cfg.terminal.plane.rawRows (q*p)→Bool
local notation "T" => DescentBundleTagKeys.capacity initial arity groups p stride
local notation "cable" => edgeCode net l.home l.native


open DescentTerminalCompiledPrefix.AddressPlan
theorem Leaf.placed_seen (I:Input) (base:ℕ) (O:DescentPrivateExponentRAM.Banks)
    (codes front empty:ℕ) (publicVolume:(∑x,ew x)≤ cfg.terminal.plane.publicRows*(q*p))
    (pay:raw) (outer:Ports ew) (i:Fin (K₀*W)) :
    (l.contents cfg pay outer).first i+1<
      (DescentTerminalChipBootWords.chipBanks (K:=K₀) (W:=W) (q:=q) («p»:=piece) codes (layout cfg I base O).emit front empty).raw.size := by
  have covered:=DescentTerminalChipSource.file_range (K₀:=K₀) net l.home l.native l.external l.nodes l.ops
    (fun v=>((l.shape v).recipe l.hp).restricted) l.hp l.birth l.wp l.qp rfl pay outer l.volume publicVolume i
  exact covered.trans (DescentTerminalDataPlane.Arena.room _)
end Branch
end
end Hierarchy.DescentTerminalEmitter

end OAI
