import OAI.Hierarchy.DescentTerminalPrimitiveReceipts
import OAI.Hierarchy.DescentTerminalMaskedKeys
import OAI.Hierarchy.DescentTerminalEmittedChip
import OAI.Hierarchy.DescentTerminalSuffixData

namespace OAI
/-! # True reached input columns for the observation and scalar of the fixed terminal suffix -/
namespace Hierarchy.DescentTerminalEmitter
open DescentTerminalChipRuntime DescentTerminalChipPins DescentTerminalChipSource DescentTerminalChronologicalChip
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open DescentTerminalSiteShelves DescentTerminalHeaderScatter
open DescentKernelHistory hiding Word
open DescentBundleHistory DescentEpochTagKeys DescentTerminalGraphPositions
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow DescentTerminalPorts DescentTerminalCableOrder
open DescentTerminalDenseWindowRAM (radix)
open DescentTerminalBinReaddress DescentTerminalRecipeRows DescentTerminalScalarTransposes
open ThreeFlat.Routing Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open Computability.BorderVNP.Crossing
open DescentTerminalVertexFields DescentSixParty DescentCompiler
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

open DescentTerminalScalarPadded
namespace Branch
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
local notation "rawRows" => (state).plane.rawRows
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
local notation "K" => Bins («S»:=σ.hostSize age) (W:=W) (q:=q) sites
local notation "T" => DescentBundleTagKeys.capacity initial arity groups p stride
local notation "book" => DescentBundleTagKeys.codec old arity groups p stride
local notation "recipes" => DescentTerminalBundleRows.recipes L rsite hp birth (Codec.store book)
variable (machine : sliceWidth W q piece ≤ bitsW)
    (space : DescentTerminalBinPack.purchased W (counts (q:=q) (order world.graph home native (W*piece) external nodes ops).site) ≤ cfg.terminal.pool)
    (countsFit : ∀v,DescentTerminalRestrictedRows.operandCount bit s v ≤ H) (atoms : ∀v,Fintype.card (bit v).Node ≤ nodesN)
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
local notation "leaf" => DescentTerminalChronologicalIssue.leaf sites wp qp space recipes ranked hH hN hA hw vertsFit
local notation "codes" => DescentTerminalScalarHeader.range q T H nodesN addrN p verts
local notation "earlier" => routed state E m

variable {K₀ B : ℕ} (banks:Banks) (cpu:DescentTerminalChipRuntime.Layout) (pay:RowBit cfg.terminal.plane.rawRows (q*(W*piece))→Bool)
    (outer:Ports ew) (z:Inputs K₀ W q piece→Bool)
local notation "geometry" => content (K₀:=K₀) (W:=W) (q:=q) (piece:=piece) world.graph home native external nodes ops rsite hp birth wp qp rfl pay outer
local notation "out" => DescentTerminalCompiledPrefix.Suffix.output cfg abi ms meter
local notation "keys" => requests (D:=D) (P:=P) (ew:=ew) («S»:=σ.hostSize age) (arity:=arity) (groups:=groups) (stride:=stride)
  world.graph home native external nodes ops bit s hp
  birth privateRank old wp qp rfl machine space countsFit atoms refs vertsFit
/-- All scalar, cable and routing receipts refer to real inputs of the corresponding
bounded native subpass. The literal proposal planes and static ROMs are supplied before
the emitter. Its resulting five chip observations and keys are derived in `proves`. -/
structure BranchPrint where
  siteCount : cfg.sites=S
  fitsBins : Bins («S»:=σ.hostSize age) (W:=W) (q:=q) (Order.site
    (DescentTerminalCableOrder.order (D:=D) (P:=P) (bits:=ew) («S»:=σ.hostSize age)
      world.graph home native (W*piece) external nodes ops))≤K₀
  pos : 0<bitsW
  capacity : Room state E bitsW
  wordFit : q*p ≤ bitsW
  volume : (∑e,world.graph.width e) ≤ cfg.terminal.plane.rawRows*(q*(W*piece))
  clustered : DescentTerminalPublicGroup.Clustered N home external
  emptyKey : banks.empty=(DescentTerminalChronologicalBooks.empty q T H nodesN addrN p verts (W*piece)).val
  bounds : ∀b∈[banks.scalar.header,banks.scalar.payload,banks.scalar.pointer],b.Fits bitsW cpu.first
  roomOut : cpu.first+(state).pool<2^bitsW
  tableFit : codes+1 ≤ 2^bitsW
  keyFit : DescentTerminalChronologicalBooks.Keys q T H nodesN addrN p verts (W*piece) ≤ 2^bitsW
  headerBase : banks.scalar.header.base=(E).scalar
  headerRoom : (state).pool≤banks.scalar.header.size
  payloadRoom : K₀*W ≤ banks.scalar.payload.size
  ptrRoom : codes+1≤banks.scalar.pointer.size
  short : ∀i v,(sites i).arity v≤q
  onePass : (state).leaves=(state).pool
  homeId : (L).home=live.home
  ranking : ∀v,(L).nodeRank v=(live.placement.site live.vertex live.valid.coordinates v).val
  bp : 0<B
  oneWord : verts*span q T H nodesN addrN p≤B
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
  pages : (directory).texture.base+(S+1)<2^bitsW
  stored : (directory).texture.Fits bitsW (E).leaf.event.base
  pagesFit : S+1≤(directory).texture.size
  preserve : ∀b∈[(directory).span.active,(directory).span.owner,(directory).span.localRow,
      (directory).ports,(directory).count,(directory).firstWord,(directory).skip,(directory).countShift,(directory).modeShift,
      (directory).skipShift,(directory).wordShift],b.Fits bitsW (directory).texture.base
  wordSide : W<2^bitsW
  eventFit : (E).leaf.event.Fits bitsW (E).leaf.cells.base
  eventSize : (state).pool≤(E).leaf.event.size
  frames : ∀i : Fin (state).pool,let a:=(E).leaf.event.base+i.val
      BeforeKey state E a ∧ AfterFlights state E a ∧ a<(E).scalar
  compileLow : (DescentTerminalLeafFold.row (E).leaf).Fits bitsW (E).leaf.cells.base
  half : ∀(i : Fin (state).pool) (j : Fin 2),(E).leaf.half.read earlier ((field i j).val:Word bitsW)=(i.val:Word bitsW)
  identity : ∀i : Fin (state).pool,(E).leaf.home.read earlier (i.val:Word bitsW)=(i.val:Word bitsW)
  decoder : ∀j : Fin (alphabet verts W B),(E).leaf.weight.read earlier (j.val:Word bitsW)=
      ((entryBy (DescentTerminalVertexFields.decode (q:=q) (t:=T) (H:=H) («N»:=nodesN) (A:=addrN) (w:=p)) qp j):Word bitsW)
  maskAlias : (E).leaf.occupancy=(E).leaf.cells
  romLow : (E).leaf.table.Fits bitsW (E).leaf.cells.base
  fieldsFit : (DescentTerminalPrintedFields.capacity q T H nodesN addrN p verts).total≤2^bitsW
  headerROM : ∀j : Fin (DescentTerminalPrintedFields.capacity q T H nodesN addrN p verts).total,
      (E).leaf.table.read earlier (j.val:Word bitsW)=
      ((DescentTerminalPrintedFields.headerTable q T H nodesN addrN p verts)[j.val]'(by simp [DescentTerminalPrintedFields.headerTable]):Word bitsW)
  pointer : ∀j : Fin codes,m (banks.scalar.pointer.base+j.val+1)=((j.val*2^(q*(W*piece)):ℕ):Word bitsW)
  safe : ∀j : Fin codes,BeforeKey state E (banks.scalar.pointer.base+(j.val+1)) ∧
      AfterFlights state E (banks.scalar.pointer.base+(j.val+1))
  ports : ControlColumns state E m N home native external nodes ops rsite hp birth wp qp fitsBins banks
  cables : SourceRows (W:=W) (q:=q) (piece:=piece) state E m external pay outer banks
  gateRows : (state).rows=K₀*W
  gateBank : (E).route.gate.base=banks.gate.base
  gateLife : ∀i : Fin (K₀*W),banks.gate.base+3*i.val<(E).leaf.cells.base ∧ banks.gate.base+3*i.val<(E).scalar
  VG : ℕ
  VV : ℕ
  VM : ℕ
  VA : ℕ
  nameBits : ℕ
  localFit : ∀i,DescentTerminalLocalPortBook.Room (sites i) VG VV VM VA
  names : ∀i,(sites i).Name ↪ Word nameBits
  args : ∀i,(sites i).Arg→Word nameBits
  matchNames : ∀i v,args i v=names i ((sites i).arg v.1 v.2)
  routeSpace : DescentTerminalRouteIssue.Fits (E).route bitsW (K₀*W)
  routeColumns : DescentTerminalRouteIssue.Reads («K»:=K₀) (W:=W) (q:=q) (a:=Nat.clog 2 (W*2^nameBits)) (E).route
    (DescentTerminalLocalPortBook.rows (K₀:=K₀) (q:=q) sites wp localFit names args) (named state E m)
  fits : ∀x∈[banks.index,banks.formats,banks.raw,banks.menuStart,banks.highField,banks.denseROM],x.Fits bitsW cpu.first
  sizes : (K₀*W)≤banks.index.size ∧ (K₀*W)≤banks.formats.size ∧ Menus q p≤banks.menuStart.size ∧ radix q p≤banks.highField.size ∧
      Menus q p*(radix q p*radix q p)≤banks.denseROM.size
  seen : ∀i,(geometry).first i+1<banks.raw.size
  routeFit : banks.gate.Fits bitsW cpu.first ∧ banks.joinedX.Fits bitsW cpu.first ∧ banks.pointer.Fits bitsW cpu.first ∧ banks.routeROM.Fits bitsW cpu.first
  routeSize : 3*(K₀*W)≤banks.gate.size ∧ (K₀*W)≤banks.joinedX.size ∧ 2^(DescentTerminalBinFormat.controlBits W q)≤banks.pointer.size ∧
      2^(DescentTerminalBinFormat.controlBits W q)*2^(sliceWidth W q piece)≤banks.routeROM.size
  bootInit : Boot banks m z
  bootBefore : ∀b∈[banks.ySlices,banks.scalar.payload,banks.joinedX,banks.xWords,banks.highField,banks.menuStart,banks.denseROM,
        banks.pointer,banks.routeROM,banks.scalar.pointer],∀j<b.size,BeforeKey state E (b.base+j) ∧ AfterFlights state E (b.base+j)
  bootCaps : (∀b∈[banks.ySlices,banks.scalar.payload,banks.joinedX,banks.xWords],(K₀*W) ≤ b.size) ∧
      radix q (W*piece)≤banks.highField.size ∧ Menus q (W*piece)≤banks.menuStart.size ∧
      Menus q (W*piece)*(radix q (W*piece)*radix q (W*piece))≤banks.denseROM.size ∧
      2^(DescentTerminalBinFormat.controlBits W q)≤banks.pointer.size ∧ 2^(DescentTerminalBinFormat.controlBits W q)*2^(sliceWidth W q piece)≤banks.routeROM.size


set_option maxHeartbeats 1000000 in
/-- One selected branch has the actual chip inputs and, on its unique accepted
transpose, the actual scalar key of every paid row, in the very same final memory. -/
theorem BranchPrint.proves (h:BranchPrint (arity:=arity) (groups:=groups) (stride:=stride)
    live cfg abi ms meter home native external nodes ops bit s hp birth privateRank old
    wp qp countsFit atoms refs vertsFit fit banks cpu pay outer z (B:=B)) :
    Chips cpu banks geometry out z ∧
    ((geometry).accepts bitsW z → ∀i:Fin (state).pool,(DescentTerminalChipRuntime.key banks).eval out (i.val:Word bitsW)=
      (((keys (takeBits world.graph (denseBits world.graph (edgeCode world.graph home native) h.volume) pay) outer) i).val:Word bitsW)) := by
  have output : out = result state E m :=
    congrArg (fun hostCount => result cfg.terminal abi.emit
      (issued cfg.terminal abi.emit abi.directory
        (maskedMem ms abi.directory hostCount (DescentTerminalCompiledPrefix.Suffix.sockets cfg abi meter)))) h.siteCount
  rw [output]
  have static : Boot banks (result state E m) z :=
    boot_read state E banks m z h.capacity h.bootInit h.bootBefore h.bootCaps
  constructor
  · exact chips state E m h.capacity h.pos N home native external nodes ops rsite hp birth wp qp h.fitsBins pay outer banks z
      cpu h.ports h.cables h.gateRows h.gateBank h.gateLife h.localFit fit h.names h.args h.matchNames h.routeSpace
      h.routeColumns static h.wordFit h.fits h.sizes h.seen h.routeFit h.routeSize
  · intro accept
    exact sparse_keys (F:=F) (P:=P) (U:=U) (D:=D) (ew:=ew) («p»:=W*piece)
      (W:=W) (q:=q) (piece:=piece) (bitsW:=bitsW) (H:=H) (nodesN:=nodesN) (addrN:=addrN)
      (verts:=verts) («rawRows»:=cfg.terminal.plane.rawRows) (initial:=initial)
      (arity:=arity) (groups:=groups) (stride:=stride) (K₀:=K₀) (B:=B)
      live state E directory ms input home native external nodes ops bit s hp birth privateRank old wp qp rfl machine
      space countsFit atoms refs vertsFit fit h.fitsBins banks cpu.first h.pos h.capacity h.wordFit pay outer h.volume h.clustered z
      accept h.emptyKey h.bounds h.roomOut h.tableFit h.keyFit h.headerBase h.headerRoom h.payloadRoom h.ptrRoom h.short
      h.onePass h.homeId h.ranking h.bp h.oneWord h.occupied
      (fun i v key => PrimitiveReceipts.read (q:=q) (t:=T) (H:=H) («N»:=nodesN) (A:=addrN) (w:=W*piece)
        (sites i) (recipes i) (ranked i) (hH i) (hN i) (hA i) (hw i) (h.short i) v
        (venueField (q:=q) (t:=T) (H:=H) («N»:=nodesN) (A:=addrN) (w:=W*piece)
          (cellAt (q:=q) (t:=T) (H:=H) («N»:=nodesN) (A:=addrN) (w:=W*piece)
            (groups:=σ.groupCount age) (blocks:=2^k)
            (measured ms input (q:=q) (t:=T) (H:=H) («N»:=nodesN) (A:=addrN) (w:=W*piece)
              (groups:=σ.groupCount age) i) (live.rawResident L h.homeId i v))) (h.previous i v) key) h.shared h.controls h.pages h.stored h.pagesFit
      h.preserve h.wordSide h.eventFit h.eventSize h.frames h.compileLow h.half h.identity h.decoder h.maskAlias
      h.romLow h.fieldsFit h.headerROM static h.pointer h.safe

end Branch
end
end Hierarchy.DescentTerminalEmitter

end OAI
