import OAI.Hierarchy.DescentTerminalBranchLibrary

namespace OAI
/-! # Dynamic data of one genuinely reached terminal branch -/
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
section NativeInputs
variable {F P U : Type} [Field F] [Fintype P] {ew : P→ℕ}
    {D W q piece bitsW H nodesN addrN verts initial arity groups stride : ℕ}
    {world : MarkedWorld F D P ew} {G : PoweredGadget F} {ε price : ℝ} {σ : AtomSchedule}
    {k age zStage degree wire hist : ℕ} (live : DescentSixParty.Reached world G price ε σ k age zStage degree wire hist)
    (cfg:DescentTerminalCompiledPrefix.Shape) (abi:DescentTerminalCompiledPrefix.Layout)
    (ms:MaskedShelf (2^k)) (meter:Memory bitsW)
local notation "N" => world.graph
local notation "p" => W*piece
local notation "S" => σ.hostSize age
local notation "g" => σ.groupCount age
local notation "state" => cfg.terminal
local notation "E" => abi.emit
local notation "directory" => abi.directory
local notation "input" => DescentTerminalCompiledPrefix.Suffix.sockets cfg abi meter
variable (home:world.graph.Site→Fin (σ.hostSize age)) (native:world.graph.Edge ↪ Fin (Fintype.card world.graph.Edge))
    (external : P ↪ ℕ) (nodes : world.graph.Site ↪ ℕ) (ops : ∀v,Boundary world.graph v ↪ ℕ)
    (bit : SiteBits (U:=U) world.graph) (s : ∀v,DescentBundleHistory.Shape (W*piece) (bit v)) (hp : 0<W*piece)
    (birth : ∀v,(bit v).Node ↪ ℕ) (privateRank : ∀v,((s v).recipe hp).restricted.Hidden ↪ ℕ) (old : Codec U initial) (wp : 0<W) (qp : 0<q)
local notation "ready" => maskedMem ms directory S input
local notation "m" => issued state E directory ready
local notation "L" => DescentTerminalCableOrder.order (D:=D) (P:=P) (bits:=ew) («S»:=σ.hostSize age)
  world.graph home native (W*piece) external nodes ops
local notation "rsite" => fun v=>Recipe.restricted (DescentBundleHistory.Shape.recipe hp (s v))
local notation "sites" => Order.site L
local notation "T" => DescentBundleTagKeys.capacity initial arity groups p stride
local notation "book" => DescentBundleTagKeys.codec old arity groups p stride
local notation "recipes" => DescentTerminalBundleRows.recipes L rsite hp birth (Codec.store book)
variable (countsFit : ∀v,DescentTerminalRestrictedRows.operandCount bit s v ≤ H) (atoms : ∀v,Fintype.card (bit v).Node ≤ nodesN)
    (refs : ∀v u,(∑j,∑digit,((s v).chunk u j digit).count) ≤ addrN)
    (vertsFit : ∀i : Fin (σ.hostSize age),((order world.graph home native (W*piece) external nodes ops).site i).nodes ≤ verts)
    (fit : ∀i : Fin (σ.hostSize age),((order world.graph home native (W*piece) external nodes ops).site i).rows q ≤ W)
local notation "hH" => fun i v=>Nat.le_trans
  (DescentTerminalRestrictedRows.hidden_bound bit s hp (Order.node L i v)) (countsFit (Order.node L i v))
local notation "hN" => fun i v=>atoms (Order.node L i v)
local notation "hA" => fun i v u=>(Eq.symm (DescentBundleHistory.Shape.recipe_refs hp (s (Order.node L i v)) u)) ▸ refs (Order.node L i v) u
local notation "hw" => fun (i : Fin S) (v : Fin (sites i).nodes) (u : (recipes i v).Hidden) =>
  (show (recipes i v).width u ≤ p from le_refl p)

local notation "ranked" => charts (arity:=arity) (groups:=groups) (stride:=stride) N home native external nodes ops bit s hp birth privateRank old
variable {K₀ B : ℕ} (banks:Banks) (pay:RowBit cfg.terminal.plane.rawRows (q*(W*piece))→Bool) (outer:Ports ew)
set_option maxHeartbeats 1000000 in
/-- The earlier node and route readbacks consumed by the terminal ROM. -/
structure BranchInputs (fitsBins : Bins («S»:=σ.hostSize age) (W:=W) (q:=q) (Order.site
    (DescentTerminalCableOrder.order (D:=D) (P:=P) (bits:=ew) («S»:=σ.hostSize age)
      world.graph home native (W*piece) external nodes ops))≤K₀)
    (oneWord : verts * span q T H nodesN addrN p ≤ B) where
  clustered : DescentTerminalPublicGroup.Clustered N home external
  short : ∀i v,(sites i).arity v≤q
  homeId : (L).home=live.home
  ranking : ∀v,(L).nodeRank v=(live.placement.site live.vertex live.valid.coordinates v).val
  occupied : ∀i c,blankAt (q:=q) (t:=T) (H:=H) («N»:=nodesN) (A:=addrN) (w:=p) (groups:=g) (blocks:=2^k)
      (measured ms input (q:=q) (t:=T) (H:=H) («N»:=nodesN) (A:=addrN) (w:=p) (groups:=g) i) c≠0 ↔
      ∃u,live.chart L homeId i u=c
  previous : ∀i v,PrimitiveReceipts (q:=q) (sites i) (recipes i) (ranked i) (hH i) (hN i) (hA i) v
    (venueField (q:=q) (t:=T) (H:=H) («N»:=nodesN) (A:=addrN) (w:=p)
      (cellAt (q:=q) (t:=T) (H:=H) («N»:=nodesN) (A:=addrN) (w:=p) (groups:=g) (blocks:=2^k)
        (measured ms input (q:=q) (t:=T) (H:=H) («N»:=nodesN) (A:=addrN) (w:=p) (groups:=g) i) (live.rawResident L homeId i v)))
  shared : MountedMask (q:=q) (t:=T) (H:=H) («N»:=nodesN) (A:=addrN) (w:=p) (V:=verts) (groups:=g) ms input oneWord
  controls : Controls (B:=B) (n:=(state).pool) directory input sites fit (fun i=>actual (w:=p) (sites i) (recipes i) (ranked i)
      (hH i) (hN i) (hA i) (hw i) (vertsFit i) (short i))
  ports : ControlColumns state E m N home native external nodes ops rsite hp birth wp qp fitsBins banks
  cables : SourceRows (W:=W) (q:=q) (piece:=piece) state E m external pay outer banks
  VG : ℕ
  VV : ℕ
  VM : ℕ
  VA : ℕ
  nameBits : ℕ
  localFit : ∀i,DescentTerminalLocalPortBook.Room (sites i) VG VV VM VA
  names : ∀i,(sites i).Name ↪ Word nameBits
  args : ∀i,(sites i).Arg→Word nameBits
  matchNames : ∀i v,args i v=names i ((sites i).arg v.1 v.2)
  routeColumns : DescentTerminalRouteIssue.Reads («K»:=K₀) (W:=W) (q:=q) (a:=Nat.clog 2 (W*2^nameBits)) (E).route
    (DescentTerminalLocalPortBook.rows (K₀:=K₀) (q:=q) sites wp localFit names args) (named state E m)

end NativeInputs
section LeafInput

variable {F P U : Type} [Field F] [Fintype P] {ew : P → ℕ}
variable {D k age zStage degree wire hist K₀ W q piece bitsW H nodesN addrN verts initial arity groups stride B : ℕ}
variable {G : PoweredGadget F} {ε price : ℝ} {σ : AtomSchedule}
variable {world : MarkedWorld F D P ew} {live : DescentSixParty.Reached world G price ε σ k age zStage degree wire hist}
variable (cfg : DescentTerminalCompiledPrefix.Shape)
variable (l : Leaf cfg world live U W q piece H nodesN addrN verts)
variable (old : Codec U initial) (abi : DescentTerminalCompiledPrefix.Layout)
variable (ms : MaskedShelf (2^k)) (meter : Memory bitsW) (banks : Banks)
variable (pay : RowBit cfg.terminal.plane.rawRows (q*(W*piece)) → Bool) (outer : Ports ew)
local notation "N" => world.graph
local notation "p" => W*piece
local notation "T" => DescentBundleTagKeys.capacity initial arity groups p stride
local notation "siteOrder" => order N l.home l.native (W*piece) l.external l.nodes l.ops

/-- The total purchased rows of this leaf fit the whole-bin physical pool. -/
theorem Leaf.binsFit (capacity : cfg.terminal.pool = K₀*W) :
    Bins (W:=W) (q:=q) (siteOrder).site ≤ K₀ :=
  Nat.le_of_mul_le_mul_right (l.space.trans_eq capacity) l.wp

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
/-- Earlier variable columns at the actual native leaf, with the bins fixed by
the paid size of the preceding stage. -/
def Leaf.Entering (capacity : cfg.terminal.pool = K₀*W)
    (oneWord : verts*span q T H nodesN addrN p ≤ B) : Type :=
  BranchInputs (F:=F) (P:=P) (U:=U) (world:=world) (ew:=ew) (W:=W) (q:=q)
    (piece:=piece) (bitsW:=bitsW) (H:=H) (nodesN:=nodesN) (addrN:=addrN) (verts:=verts)
    (initial:=initial) (arity:=arity) (groups:=groups) (stride:=stride) («K₀»:=K₀) (B:=B)
    live cfg abi ms meter l.home l.native l.external l.nodes l.ops l.bit l.shape l.hp l.birth l.hidden old l.wp l.qp
    l.countsFit l.atoms l.refs l.vertsFit l.fit banks pay outer (l.binsFit cfg capacity) oneWord


end LeafInput
end Branch
end
end Hierarchy.DescentTerminalEmitter

end OAI
