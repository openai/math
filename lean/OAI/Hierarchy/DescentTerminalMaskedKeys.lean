import OAI.Hierarchy.DescentTerminalPositionKeys
import OAI.Hierarchy.DescentTerminalActivePages

namespace OAI
/-! # Scalar keys obtained from the actual occupied earlier group/block fields and fixed native output -/
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
variable {F P U : Type} [Field F] [Fintype P] {ew : P→ℕ}
    {D p W q piece bitsW H nodesN addrN verts rawRows initial arity groups stride : ℕ}
    {world : MarkedWorld F D P ew} {G : PoweredGadget F} {ε price : ℝ} {σ : AtomSchedule}
    {k age zStage degree wire hist : ℕ} (live : DescentSixParty.Reached world G price ε σ k age zStage degree wire hist)
variable (state : Shape) (E : Layout) (directory : Directory) (ms : MaskedShelf (2^k)) (input : Memory bitsW)
    (home : world.graph.Site→Fin (σ.hostSize age)) (native : world.graph.Edge ↪ Fin (Fintype.card world.graph.Edge))
    (external : P ↪ ℕ) (nodes : world.graph.Site ↪ ℕ) (ops : ∀v,Boundary world.graph v ↪ ℕ)
    (bit : SiteBits (U:=U) world.graph) (s : ∀v,DescentBundleHistory.Shape p (bit v)) (hp : 0<p)
    (birth : ∀v,(bit v).Node ↪ ℕ) (privateRank : ∀v,((s v).recipe hp).restricted.Hidden ↪ ℕ) (old : Codec U initial) (wp : 0<W) (qp : 0<q)
local notation "ready" => maskedMem ms directory (σ.hostSize age) input
local notation "m" => issued state E directory ready
local notation "L" => order world.graph home native p external nodes ops
local notation "rsite" => fun v=>Recipe.restricted (DescentBundleHistory.Shape.recipe hp (s v))
local notation "sites" => DescentTerminalBundleRows.site L rsite hp birth
local notation "K" => Bins (W:=W) (q:=q) sites
local notation "T" => DescentBundleTagKeys.capacity initial arity groups p stride
local notation "book" => DescentBundleTagKeys.codec old arity groups p stride
local notation "recipes" => DescentTerminalBundleRows.recipes L rsite hp birth (Codec.store book)
variable (same : p=W*piece) (machine : sliceWidth W q piece ≤ bitsW)
    (space : DescentTerminalBinPack.purchased W
      (counts (q:=q) (order world.graph home native p external nodes ops).site) ≤ state.pool)
    (countsFit : ∀v,DescentTerminalRestrictedRows.operandCount bit s v ≤ H) (atoms : ∀v,Fintype.card (bit v).Node ≤ nodesN)
    (refs : ∀v u,(∑j,∑g,((s v).chunk u j g).count) ≤ addrN) (vertsFit : ∀i,((order world.graph home native p external nodes ops).site i).nodes ≤ verts)
    (fit : ∀i,((order world.graph home native p external nodes ops).site i).rows q ≤ W)
local notation "hH" => fun i v=>(DescentTerminalRestrictedRows.hidden_bound bit s hp (Order.node L i v)).trans (countsFit (Order.node L i v))
local notation "hN" => fun i v=>atoms (Order.node L i v)
local notation "hA" => fun i v u=>((s (Order.node L i v)).recipe_refs hp u).symm ▸ refs (Order.node L i v) u
local notation "hw" => fun (i : Fin (σ.hostSize age)) (v : Fin (sites i).nodes) (u : (recipes i v).Hidden) =>
  (show (recipes i v).width u ≤ p from le_refl p)

local notation "ranked" => charts (arity:=arity) (groups:=groups) (stride:=stride) world.graph home native external nodes ops bit s hp birth privateRank old
local notation "leaf" => DescentTerminalChronologicalIssue.leaf sites wp qp space recipes ranked hH hN hA hw vertsFit
local notation "codes" => DescentTerminalScalarHeader.range q T H nodesN addrN p verts
local notation "sourceInputs" => measured ms input
  (q:=q) (t:=T) (H:=H) (N:=nodesN) (A:=addrN) (w:=p) (groups:=σ.groupCount age)
local notation "earlier" => routed state E m

theorem sparse_keys {K₀ B : ℕ} (fitsBins : K ≤ K₀) (banks : Banks) (dst : ℕ) (pos : 0<bitsW)
    (capacity : Room state E bitsW) (wordFit : q*p ≤ bitsW)
    (pay : RowBit rawRows (q*p)→Bool) (outer : Ports ew)
    (volume : (∑e,world.graph.width e) ≤ rawRows*(q*p)) (clustered : DescentTerminalPublicGroup.Clustered world.graph home external)
    (z : Inputs K₀ W q piece→Bool)
    (accept : (content world.graph home native external nodes ops rsite hp birth wp qp same pay outer).accepts bitsW z)
    (emptyKey : banks.empty=(DescentTerminalChronologicalBooks.empty q T H nodesN addrN p verts (W*piece)).val)
    (bounds : ∀b∈[banks.scalar.header,banks.scalar.payload,banks.scalar.pointer],b.Fits bitsW dst)
    (roomOut : dst+state.pool<2^bitsW) (tableFit : codes+1 ≤ 2^bitsW)
    (keyFit : DescentTerminalChronologicalBooks.Keys q T H nodesN addrN p verts (W*piece) ≤ 2^bitsW)
    (headerBase : banks.scalar.header.base=E.scalar) (headerRoom : state.pool≤banks.scalar.header.size)
    (payloadRoom : K₀*W ≤ banks.scalar.payload.size) (ptrRoom : codes+1≤banks.scalar.pointer.size)
    (short : ∀i v,(sites i).arity v≤q) (onePass : state.leaves=state.pool)
    (homeId : (L).home=live.home) (ranking : ∀v,(L).nodeRank v=(live.placement.site live.vertex live.valid.coordinates v).val)
    (bp : 0<B) (oneWord : verts*DescentTerminalVertexFields.span q T H nodesN addrN p≤B)
    (occupied : ∀i c,blankAt (q:=q) (t:=T) (H:=H) (N:=nodesN) (A:=addrN) (w:=p) (groups:=σ.groupCount age)
      (blocks:=2^k) (sourceInputs i) c≠0 ↔
      ∃u,live.chart L homeId i u=c)
    (previous : ∀i v key,let r:=record (sites i) (recipes i) (ranked i) (hH i) (hN i) (hA i) (hw i) (short i) v
      allows (fun j=>(value r j).val) key→
      venueField (q:=q) (t:=T) (H:=H) (N:=nodesN) (A:=addrN) (w:=p)
        (cellAt (q:=q) (t:=T) (H:=H) (N:=nodesN) (A:=addrN) (w:=p)
          (groups:=σ.groupCount age) (blocks:=2^k) (sourceInputs i) (live.rawResident L homeId i v)) key=(value r key).val)
    (shared : MountedMask (q:=q) (t:=T) (H:=H) (N:=nodesN) (A:=addrN) (w:=p) (V:=verts) (groups:=σ.groupCount age) ms input oneWord)
    (controls : Controls (B:=B) (n:=state.pool) directory input sites fit (fun i=>actual (w:=p) (sites i) (recipes i) (ranked i)
      (hH i) (hN i) (hA i) (hw i) (vertsFit i) (short i)))
    (pages : directory.texture.base+((σ.hostSize age)+1)<2^bitsW) (stored : directory.texture.Fits bitsW E.leaf.event.base)
    (pagesFit : (σ.hostSize age)+1≤directory.texture.size) (preserve : ∀b∈[directory.span.active,directory.span.owner,directory.span.localRow,
      directory.ports,directory.count,directory.firstWord,directory.skip,directory.countShift,directory.modeShift,
      directory.skipShift,directory.wordShift],b.Fits bitsW directory.texture.base)
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
    let a:=takeBits world.graph (denseBits world.graph (edgeCode world.graph home native) volume) pay
    let req:=requests (arity:=arity) (groups:=groups) (stride:=stride) world.graph home native external nodes ops bit s hp birth privateRank old wp qp same
      machine space countsFit atoms refs vertsFit a outer
    ∀i : Fin state.pool,(DescentTerminalChipRuntime.key banks).eval (result state E m) (i.val:Computability.VPVNP.BurstRAM.Word bitsW)=((req i).val:Computability.VPVNP.BurstRAM.Word bitsW) := by
  let books:=fun i=>actual (w:=p) (sites i) (recipes i) (ranked i) (hH i) (hN i) (hA i) (hw i) (vertsFit i) (short i)
  have marked:=live.active_pages L homeId ranking ms input books (fun _=>rfl) occupied oneWord bp
    (fun i v=>record_zeros (sites i) (recipes i) (ranked i) (hH i) (hN i) (hA i) (hw i) (short i) v) previous
  have published:=mask_directory ms directory input sites fit books oneWord bp shared controls pages stored pagesFit preserve
  exact position_keys state E directory ready world.graph home native external nodes ops bit s hp birth privateRank old wp qp same machine
    space countsFit atoms refs vertsFit fit fitsBins banks dst pos capacity wordFit pay outer volume clustered z accept emptyKey
    bounds roomOut tableFit keyFit headerBase headerRoom payloadRoom ptrRoom short onePass bp _ _
    (fun i=>(Nat.mul_le_mul_right _ (vertsFit i)).trans oneWord) marked published wordSide eventFit eventSize frames
    compileLow half identity decoder maskAlias romLow fieldsFit headerROM static pointer safe

end
end Hierarchy.DescentTerminalEmitter

end OAI
