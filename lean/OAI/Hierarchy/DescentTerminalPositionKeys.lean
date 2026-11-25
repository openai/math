import OAI.Hierarchy.DescentTerminalPositionIssue
import OAI.Hierarchy.DescentTerminalEmittedKey
import OAI.Hierarchy.DescentTerminalPackedLeafRAM
import OAI.Hierarchy.DescentTerminalChronologicalChip

namespace OAI
/-! # Genuine surviving graph-row keys at the universal static chip address -/
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
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {P U : Type} [Fintype P] {ew : P→ℕ}
    {D S p W q piece bitsW H nodesN addrN verts rawRows initial arity groups stride : ℕ}
    (state : Shape) (E : Layout) (directory : Directory) (input : Memory bitsW)
    (N : Network D P ew) (home : N.Site→Fin S) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    (external : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,Boundary N v ↪ ℕ)
    (bit : SiteBits (U:=U) N) (s : ∀v,DescentBundleHistory.Shape p (bit v)) (hp : 0<p)
    (birth : ∀v,(bit v).Node ↪ ℕ) (privateRank : ∀v,((s v).recipe hp).restricted.Hidden ↪ ℕ) (old : Codec U initial) (wp : 0<W) (qp : 0<q)
local notation "m" => issued state E directory input
local notation "L" => order N home native p external nodes ops
local notation "rsite" => fun v=>Recipe.restricted (DescentBundleHistory.Shape.recipe hp (s v))
local notation "sites" => DescentTerminalBundleRows.site L rsite hp birth
local notation "K" => Bins (W:=W) (q:=q) sites
local notation "T" => DescentBundleTagKeys.capacity initial arity groups p stride
local notation "book" => DescentBundleTagKeys.codec old arity groups p stride
local notation "recipes" => DescentTerminalBundleRows.recipes L rsite hp birth (Codec.store book)
variable (same : p=W*piece) (machine : sliceWidth W q piece ≤ bitsW)
    (space : DescentTerminalBinPack.purchased W
      (counts (q:=q) (order N home native p external nodes ops).site) ≤ state.pool)
    (countsFit : ∀v,DescentTerminalRestrictedRows.operandCount bit s v ≤ H) (atoms : ∀v,Fintype.card (bit v).Node ≤ nodesN)
    (refs : ∀v u,(∑j,∑g,((s v).chunk u j g).count) ≤ addrN)
    (vertsFit : ∀i,((order N home native p external nodes ops).site i).nodes ≤ verts)
    (fit : ∀i,((order N home native p external nodes ops).site i).rows q ≤ W)
local notation "hH" => fun i v=>Nat.le_trans
  (DescentTerminalRestrictedRows.hidden_bound bit s hp (Order.node L i v)) (countsFit (Order.node L i v))
local notation "hN" => fun i v=>atoms (Order.node L i v)
set_option quotPrecheck false in
local notation "hA" => fun i v u=>(Eq.symm (DescentBundleHistory.Shape.recipe_refs hp (s (Order.node L i v)) u)) ▸ refs (Order.node L i v) u
set_option quotPrecheck false in
local notation "hw" => fun (i : Fin S) (v : Fin (sites i).nodes) (u : (recipes i v).Hidden) =>
  (show (recipes i v).width u ≤ p from le_refl p)

local notation "ranked" => charts (arity:=arity) (groups:=groups) (stride:=stride) N home native external nodes ops bit s hp birth privateRank old
local notation "leaf" => DescentTerminalChronologicalIssue.leaf sites wp qp space recipes ranked hH hN hA hw vertsFit
local notation "codes" => DescentTerminalScalarHeader.range q T H nodesN addrN p verts
local notation "earlier" => routed state E m

include fit in
theorem position_keys {K₀ B : ℕ} (fitsBins : K ≤ K₀) (banks : Banks) (dst : ℕ) (pos : 0<bitsW)
    (capacity : Room state E bitsW) (wordFit : q*p ≤ bitsW)
    (pay : RowBit rawRows (q*p)→Bool) (outer : Ports ew)
    (volume : (∑e,N.width e) ≤ rawRows*(q*p)) (clustered : DescentTerminalPublicGroup.Clustered N home external)
    (z : Inputs K₀ W q piece→Bool)
    (accept : (content N home native external nodes ops rsite hp birth wp qp same pay outer).accepts bitsW z)
    (emptyKey : banks.empty=(DescentTerminalChronologicalBooks.empty q T H nodesN addrN p verts (W*piece)).val)
    (bounds : ∀b∈[banks.scalar.header,banks.scalar.payload,banks.scalar.pointer],b.Fits bitsW dst)
    (roomOut : dst+state.pool<2^bitsW) (tableFit : codes+1 ≤ 2^bitsW)
    (keyFit : DescentTerminalChronologicalBooks.Keys q T H nodesN addrN p verts (W*piece) ≤ 2^bitsW)
    (headerBase : banks.scalar.header.base=E.scalar) (headerRoom : state.pool≤banks.scalar.header.size)
    (payloadRoom : K₀*W ≤ banks.scalar.payload.size) (ptrRoom : codes+1≤banks.scalar.pointer.size)
    (short : ∀i v,(sites i).arity v≤q) (onePass : state.leaves=state.pool)
    (bp : 0<B) (start : Fin S→ℕ) (stream : ℕ→Bool)
    (small : ∀i,(sites i).nodes*DescentTerminalVertexFields.span q T H nodesN addrN p≤B)
    (texture : ∀i,DescentTerminalVertexFields.Source (actual (w:=p) (sites i) (recipes i) (ranked i) (hH i) (hN i) (hA i)
      (hw i) (vertsFit i) (short i)) (start i) stream)
    (arrived : Reached (pool:=state.pool) directory input sites fit (fun i=>actual (w:=p) (sites i) (recipes i) (ranked i)
      (hH i) (hN i) (hA i) (hw i) (vertsFit i) (short i)) start stream bp)
    (wordSide : W<2^bitsW) (eventFit : E.leaf.event.Fits bitsW E.leaf.cells.base) (eventSize : state.pool≤E.leaf.event.size)
    (frames : ∀i : Fin state.pool,let a:=E.leaf.event.base+i.val
      BeforeKey state E a ∧ AfterFlights state E a ∧ a<E.scalar)
    (compileLow : (DescentTerminalLeafFold.row E.leaf).Fits bitsW E.leaf.cells.base)
    (half : ∀(i : Fin state.pool) (j : Fin 2),E.leaf.half.read earlier ((field i j).val:Computability.VPVNP.BurstRAM.Word bitsW)=(i.val:Computability.VPVNP.BurstRAM.Word bitsW))
    (identity : ∀i : Fin state.pool,E.leaf.home.read earlier (i.val:Computability.VPVNP.BurstRAM.Word bitsW)=(i.val:Computability.VPVNP.BurstRAM.Word bitsW))
    (decoder : ∀j : Fin (alphabet verts W B),E.leaf.weight.read earlier (j.val:Computability.VPVNP.BurstRAM.Word bitsW)=
      ((entryBy (DescentTerminalVertexFields.decode (q:=q) (t:=T) (H:=H) (N:=nodesN) (A:=addrN) (w:=p)) qp j):Computability.VPVNP.BurstRAM.Word bitsW))
    (maskAlias : E.leaf.occupancy=E.leaf.cells) (romLow : E.leaf.table.Fits bitsW E.leaf.cells.base)
    (fieldsFit : (DescentTerminalPrintedFields.capacity q T H nodesN addrN p verts).total≤2^bitsW)
    (headerROM : ∀j : Fin (DescentTerminalPrintedFields.capacity q T H nodesN addrN p verts).total,
      E.leaf.table.read earlier (j.val:Computability.VPVNP.BurstRAM.Word bitsW)=
      ((DescentTerminalPrintedFields.headerTable q T H nodesN addrN p verts)[j.val]'(by simp [DescentTerminalPrintedFields.headerTable]):Computability.VPVNP.BurstRAM.Word bitsW))
    (static : Boot banks (result state E m) z)
    (pointer : ∀j : Fin codes,m (banks.scalar.pointer.base+j.val+1)=((j.val*2^(q*(W*piece)):ℕ):Computability.VPVNP.BurstRAM.Word bitsW))
    (safe : ∀j : Fin codes,BeforeKey state E (banks.scalar.pointer.base+(j.val+1)) ∧
      AfterFlights state E (banks.scalar.pointer.base+(j.val+1))) :
    let a:=takeBits N (denseBits N (edgeCode N home native) volume) pay
    let req:=requests (arity:=arity) (groups:=groups) (stride:=stride) N home native external nodes ops bit s hp birth privateRank old wp qp same
      machine space countsFit atoms refs vertsFit a outer
    ∀i : Fin state.pool,(DescentTerminalChipRuntime.key banks).eval (result state E m) (i.val:Computability.VPVNP.BurstRAM.Word bitsW)=((req i).val:Computability.VPVNP.BurstRAM.Word bitsW) := by
  apply keys_of_cells state E m N home native external nodes ops bit s hp birth privateRank old wp qp same machine
    space countsFit atoms refs vertsFit fit fitsBins banks dst pos capacity wordFit pay outer volume clustered z accept
    emptyKey bounds roomOut tableFit keyFit headerBase headerRoom payloadRoom ptrRoom _ maskAlias romLow fieldsFit headerROM static pointer safe
  exact field_cells state E directory input sites wp qp fit recipes ranked hH hN hA hw vertsFit short space pos
    capacity onePass bp start stream small texture arrived wordSide eventFit eventSize frames compileLow half identity decoder

end
end Hierarchy.DescentTerminalEmitter

end OAI
