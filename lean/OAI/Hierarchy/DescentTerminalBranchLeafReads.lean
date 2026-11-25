import OAI.Hierarchy.DescentTerminalBranchPrint

namespace OAI
/-! # A common request alphabet for all reached typed terminal networks -/
namespace Hierarchy.DescentTerminalEmitter
open DescentTerminalChipRuntime DescentTerminalChipPins DescentTerminalChipSource DescentTerminalChronologicalChip
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open DescentTerminalSiteShelves DescentTerminalHeaderScatter
open DescentKernelHistory hiding Word
open DescentBundleHistory DescentEpochTagKeys DescentTerminalGraphPositions
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow DescentTerminalPorts DescentTerminalCableOrder
open DescentTerminalBinReaddress DescentTerminalRecipeRows DescentTerminalScalarTransposes
open ThreeFlat.Routing Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open Computability.BorderVNP.Crossing
open DescentTerminalVertexFields DescentSixParty DescentCompiler
open scoped Classical BigOperators Fin.CommRing
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

/-- Instance-independent finite alphabets with the actual site, wire and birth order of
the selected reached network. The word and row capacities are common to all such selections. -/
structure Leaf (world:MarkedWorld F D P ew) (live:DescentSixParty.Reached world G price ε σ k age zStage degree wire hist)
    (U:Type) (W q piece H nodesN addrN verts:ℕ) where
  home : world.graph.Site→Fin S
  native : world.graph.Edge↪Fin (Fintype.card world.graph.Edge)
  external : P↪ℕ
  nodes : world.graph.Site↪ℕ
  ops : ∀v,Boundary world.graph v↪ℕ
  bit : SiteBits (U:=U) world.graph
  shape : ∀v,DescentBundleHistory.Shape (W*piece) (bit v)
  hp : 0<W*piece
  birth : ∀v,(bit v).Node↪ℕ
  hidden : ∀v,((shape v).recipe hp).restricted.Hidden↪ℕ
  wp : 0<W
  qp : 0<q
  space : DescentTerminalBinPack.purchased W (counts (q:=q) (order world.graph home native (W*piece) external nodes ops).site)≤ cfg.terminal.pool
  countsFit : ∀v,DescentTerminalRestrictedRows.operandCount bit shape v≤H
  atoms : ∀v,Fintype.card (bit v).Node≤nodesN
  refs : ∀v u,(∑j,∑g,((shape v).chunk u j g).count)≤addrN
  vertsFit : ∀i,((order world.graph home native (W*piece) external nodes ops).site i).nodes≤verts
  fit : ∀i,((order world.graph home native (W*piece) external nodes ops).site i).rows q≤W
  volume : (∑e,world.graph.width e)≤ cfg.terminal.plane.rawRows*(q*(W*piece))

variable {world:MarkedWorld F D P ew} {live:DescentSixParty.Reached world G price ε σ k age zStage degree wire hist}
variable (l:Leaf cfg world live U W q piece H nodesN addrN verts)
local notation "net" => world.graph
local notation "raw" => RowBit cfg.terminal.plane.rawRows (q*p)→Bool
local notation "T" => DescentBundleTagKeys.capacity initial arity groups p stride
local notation "cable" => edgeCode net l.home l.native

def Leaf.contents (pay:raw) (outer:Ports ew) : DescentTerminalChipRuntime.Content K₀ W q piece :=
  content (K₀:=K₀) (W:=W) (q:=q) (piece:=piece)
    net l.home l.native l.external l.nodes l.ops (fun v=>((l.shape v).recipe l.hp).restricted)
    l.hp l.birth l.wp l.qp rfl pay outer

def Leaf.assignment (pay:raw) := takeBits net (denseBits net cable l.volume) pay

variable (old:Codec U initial) (machine:sliceWidth W q piece≤bitsW)
def Leaf.keys (pay:raw) (outer:Ports ew) :=
  requests (arity:=arity) (groups:=groups) (stride:=stride) net l.home l.native l.external l.nodes l.ops
    l.bit l.shape l.hp l.birth l.hidden old l.wp l.qp rfl machine l.space l.countsFit l.atoms l.refs l.vertsFit
    (l.assignment cfg pay) outer

def Leaf.debt := ∑v,((l.shape v).recipe l.hp).deadBits

theorem Leaf.eval_graph (small:∀i v,((order net l.home l.native p l.external l.nodes l.ops).site i).arity v≤q)
    (scalar:U→List (List Bool)→F) (table:(net).Tables F) (correct:ReadsBits net scalar l.bit table)
    (labels:∀v u,old.fits ((l.bit v).tag u)) (lengths:∀v u,(l.bit v).arity u≤arity)
    (slices:∀v u,(∑j,(l.shape v).groups u j)≤groups) (delta:∀v u j g,((l.shape v).chunk u j g).stride≤ stride)
    (pay:raw) (outer:Ports ew) (fit:l.debt cfg<2^bitsW) :
    (∏v,(net).read table (l.assignment cfg pay) outer v)=
      (∏j:Fin bitsW,if (l.debt cfg).testBit j.val then (2:F)^(2^j.val) else 1)*
      ∏i,DescentTerminalChronologicalBooks.menu (fun j args=>bundleScalar p scalar
        ((DescentBundleTagKeys.codec old arity groups p stride).read j) args)
        ((l.keys cfg (arity:=arity) (groups:=groups) (stride:=stride) old machine pay outer) i) := by
  apply DescentTerminalChronologicalChip.graph_product net l.home l.native l.external l.nodes l.ops l.bit l.shape l.hp
    l.birth l.hidden old l.wp l.qp rfl machine l.space l.countsFit l.atoms l.refs l.vertsFit l.fit small
    scalar table correct labels lengths slices delta (l.assignment cfg pay) outer bitsW fit

theorem Leaf.factors (small:∀i v,((order net l.home l.native p l.external l.nodes l.ops).site i).arity v≤q)
    (scalar:U→List (List Bool)→F) (table:(net).Tables F) (correct:ReadsBits net scalar l.bit table)
    (labels:∀v u,old.fits ((l.bit v).tag u)) (lengths:∀v u,(l.bit v).arity u≤arity)
    (slices:∀v u,(∑j,(l.shape v).groups u j)≤groups) (delta:∀v u j g,((l.shape v).chunk u j g).stride≤ stride)
    (pay:raw) (outer:Ports ew) (fit:l.debt cfg<2^bitsW) :
    (∏_i:Unit,(2:F)^(l.debt cfg))*
      (∏i,DescentTerminalChronologicalBooks.menu (fun j args=>bundleScalar p scalar
        ((DescentBundleTagKeys.codec old arity groups p stride).read j) args)
        ((l.keys cfg (arity:=arity) (groups:=groups) (stride:=stride) old machine pay outer) i))=
       ∏v,(net).read table (l.assignment cfg pay) outer v := by
  rw [l.eval_graph cfg old machine small scalar table correct labels lengths slices delta pay outer fit,
      ←ProtocolStackContraction.power_bits (2:F) _ bitsW fit]
  simp

variable (abi:DescentTerminalCompiledPrefix.Layout) (ms:MaskedShelf (2^k)) (meter:Memory bitsW)
variable (banks:Banks) (cpu:DescentTerminalChipRuntime.Layout)
    (pay : RowBit cfg.terminal.plane.rawRows (q*(W*piece)) → Bool)
    (outer:Ports ew) (z:Inputs K₀ W q piece→Bool)
variable (B:ℕ)
set_option Elab.async false
set_option maxHeartbeats 1000000 in
def Leaf.Printed : Type :=
  BranchPrint (F:=F) (P:=P) (U:=U) (world:=world) (ew:=ew) (W:=W) (q:=q)
    (piece:=piece) (bitsW:=bitsW) (H:=H) (nodesN:=nodesN) (addrN:=addrN) (verts:=verts)
    (initial:=initial) (arity:=arity) (groups:=groups) (stride:=stride) («K₀»:=K₀) (B:=B)
    live cfg abi ms meter l.home l.native l.external l.nodes l.ops l.bit l.shape l.hp l.birth l.hidden old l.wp l.qp
    l.countsFit l.atoms l.refs l.vertsFit l.fit banks cpu pay outer z

set_option maxHeartbeats 1000000 in
theorem Leaf.printed_reads (h:l.Printed cfg (arity:=arity) (groups:=groups) (stride:=stride) old abi ms meter banks cpu pay outer z B) :
    let out:=DescentTerminalCompiledPrefix.Suffix.output cfg abi ms meter
    Chips cpu banks (l.contents cfg pay outer) out z ∧
    ((l.contents cfg pay outer).accepts bitsW z → ∀i:Fin cfg.terminal.pool,
      (DescentTerminalChipRuntime.key banks).eval out (i.val:Word bitsW)=
        (((l.keys cfg (arity:=arity) (groups:=groups) (stride:=stride) old machine pay outer) i).val:Word bitsW)) := by
  exact BranchPrint.proves (arity:=arity) (groups:=groups) (stride:=stride)
    live cfg abi ms meter l.home l.native l.external l.nodes l.ops l.bit l.shape
    l.hp l.birth l.hidden old l.wp l.qp machine l.space l.countsFit l.atoms l.refs l.vertsFit l.fit
    banks cpu pay outer z h

end Branch
end
end Hierarchy.DescentTerminalEmitter

end OAI
