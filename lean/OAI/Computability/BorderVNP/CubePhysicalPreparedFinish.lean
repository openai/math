import OAI.Computability.BorderVNP.CubePhysicalFinishReceipt
import OAI.Computability.BorderVNP.CubePhysicalSignedVisitOrder
import OAI.Computability.BorderVNP.DiagonalTallyGadgetOperands
import OAI.Computability.BorderVNP.DiagonalTallySignedHeaderRoom

/-! # The actual selected cube and checked cell arrays construct the signed finish -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger

open VPVNP.BurstRAM Crossing Diagonal Diagonal.CellEntries DiagonalTallyRAM DiagonalTallyAllocation
open DiagonalTallyMaterialize DiagonalTallyCellReports RoutingISA DiagonalResidueRAM
open TeamContraction.ProcessorSlots TeamContraction.JointHeader TeamContraction.JointHeader.PositiveFields
open RoutingISA.SignedTaskArena FiniteEvaluator
open scoped BigOperators Classical

variable {D B w : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
variable {N : Network D P bits} {cell : N.Site → Cell}
variable (sa : SignedTaskArena.Layout) (pub : Arg → Word w) (control fieldWidth bodyCap : ℕ)
local notation "layout" => reportLayout sa.before sa.after (Fin.val (pub 0)) control sa.p.parameters fieldWidth bodyCap sa.cube.stop
local notation "params" => sa.p.parameters
local notation "gadgets" => sa.p.report.gadgets
local notation "teams" => sa.cube.teams
local notation "PacketIndex" => Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks
local notation "Position" => TableEntry sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s

variable (slot : LiveBit N cell ↪ Slot sa.cube.n sa.cube.header.d sa.cube.header.blocks (sa.cube.h*sa.cube.b))
    (tags : N.Tables (Entry (Fin sa.p.parameters) (Fin sa.p.report.gadgets))) (x : Ports bits)
    (id : TableEntry sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s → Fin sa.p.report.gadgets)
    (words : PowerWords (Fin sa.cube.teams) (Fin sa.p.parameters) (Fin sa.p.report.gadgets) B N tags)
    (label : Cell → Label (sa.cube.n+1) sa.cube.header.d) (team : Fin sa.cube.header.d → Fin sa.cube.teams)
    (a : Path N cell sa.cube.n sa.cube.header.d sa.cube.header.blocks sa.cube.b sa.cube.h sa.cube.K sa.cube.s)
    (t : Fin sa.cube.teams) (o : Orders tags words label team a t)
    (uses : PowerSlot (Fin sa.cube.teams) (Fin sa.p.parameters) B → UseRead)
    (cells : ∀ c : Cell,CellRead {v : N.Site // cell v=c} sa.p.report.gadgets)
    (packets : Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks × Vertex (sa.cube.n+1) → PacketRead)
    (reports : Cell → ReportCell (reportLayout sa.before sa.after (pub 0).val control sa.p.parameters fieldWidth bodyCap sa.cube.stop))

local notation "ordering" => Orders.withNativeVertices tags words label team a t o
local notation "tablePosition" => fun (_ : PacketIndex) => id
local notation "rows" => physicalRow slot tags x tablePosition words label team a
local notation "cs" => teamReports tags words label team a t ordering reports
local notation "cursor" => sa.after.reportCursor
local notation "data" => pathBanks a sa.cube.header.packetBase sa.cube.singleBank
local notation "X" => gadgetLookup sa pub (Fin.val ∘ team) t.val D data

variable {reserve axes groups cap width : ℕ} (A : StartupArena)
    (p : PositiveFields reserve axes groups cap sa.cube.teams sa.dim width)
local notation "raw" => rawAddress A reserve axes groups cap

include packets

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1600000 in
/-- The owned cube scan and cell scanner produce the exact chronological operands
for this physical term. Reading the authentic parsed header then gives the
positive finish receipt on every proposed common subtotal word. -/
theorem preparedFinish {banks : CellBanks.Layout} (mac : TeamOpcode.Macros w 8) (state : Bank w) (mem : Memory w)
    (alloc : ReportAllocation sa.before sa.after banks layout cs cursor)
    (bankStart : banks.bankStart=sa.cube.cellBank) (bankCount : banks.cells=sa.cube.cells)
    (bankStride : banks.stride=sa.cube.cellStride) (frame : (pub 0).val=A.frame)
    (parsed : HeaderSeed sa p pub raw t.val mem)
    (selected : CubePacket.WordPrepared X sa.id pub mem)
    (report : supplied mem (cellEnd cs cursor) (cursor).descriptors (cellOperands cs cursor))
    (count : (mem ((pub 0).val+35)).val=(cellOperands cs cursor).length)
    (codes : ∀ e,sa.id e=(id e).val)
    (vertexCap : (X).frame.count ≤ sa.p.report.vertices)
    (digitsFit : Tally.argumentWidth sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s ≤ sa.p.report.cubeWidth)
    (headerSize : A.header=PositiveFields.width reserve axes groups cap teams sa.dim width)
    (placed : A.next ≤ sa.cube.header.header) {u v k : ℕ} (endFit : sa.endAddress w u v k<2^w)
    (teamFit : teams<2^w) (widthFit : width ≤ w) (wpos : 0<w)
    (useBit : ∀ i,(uses i).bit=words.localUse (pathEdges slot a) (fun _ port => x port.val) i.1 i.2.1 i.2.2)
    (siteID : ∀ c (v : {v : N.Site // cell v=c}) g,(((cells c).observed v).filterMap Prod.snd).count g.val=
      (counters (tags v.val (pathEdges slot a v.val) (fun port => x port.val))).2 g)
    (source : UseOccurrence cs ≃ {i // routedPowerOwner tags words label team a i=t})
    (align : ∀ a', let i := (source a').val
      occurrencePair cs a'=(i.2.1.val,if (uses i).bit then 2^i.2.2.val else 0))
    (fields : ∀ c,(cells c).directory.reportedCounts=countFields ((reports c).privateWires+(reports c).supplied)
      gadgets (layout).countWidth)
    (digits : ∀ c g j,(reports c).counts g j=(cells c).bank
      ((reports c).privateWires+(reports c).supplied+g.val*(layout).countWidth+j.val))
    (bounded : ∀ c,rows t c<2^w) :
    ∃ receipt : FinishInput t rows width pub mac state mem p.tallyWords,
      receipt.post=sa.after ∧ receipt.raw=raw ∧
      receipt.operands=receiptOperands tags tablePosition words label team a t ordering reports sa.after cursor
        (pub 0).val (sa.cube.stop+1) ∧
      (∀ k < sa.after.start, k ≠ (pub 0).val+35 → receipt.selected k = mem k) ∧
      traceCost receipt.earlier ≤ selectedOperandsTicks (X).frame.count (X).frame.width := by
  obtain ⟨frameFit,rawLow,rawHigh,room,dimFit,localFit,_⟩ := finishSeedRoom sa A headerSize placed endFit
  rw [←frame] at frameFit rawLow
  have fresh : sa.after.fresh<2^w := (Nat.le_add_right sa.after.fresh (2*sa.after.bound.operands)).trans_lt localFit
  have actual (j : Fin (ordering).nVertex) :
      sa.id (((X).visits j).entry D)=(pathPacketID tablePosition a ((ordering).vertices j).val).val := by
    rw [codes]
    exact congrArg Fin.val (nativeVisit_id (d':=sa.cube.scanner (pub 0).val t.val (data).axis.val sa.cube.rowSelectorBits)
      sa.cube.header.packetBase sa.cube.singleBank team a label t rfl id j)
  have equalIDs : (fun j => sa.id (((X).visits j).entry D))=
      (fun j : Fin (ordering).nVertex => (pathPacketID tablePosition a ((ordering).vertices j).val).val) := funext actual
  obtain ⟨es,s,mt,prepare,clock,_,suppliedRows,total,cap,sep,kept⟩ :=
    gadgetOperands sa pub (Fin.val ∘ team) t.val D data alloc bankStart bankCount bankStride rfl rfl
      mac state mem selected report count parsed.seed.words.1 parsed.parameters vertexCap digitsFit frameFit fresh
      (fun i => (codes _).symm ▸ (id (((X).visits i).entry D)).isLt) dimFit.le
  erw [equalIDs] at suppliedRows total cap sep
  let receipt := finishReceipt slot tags x tablePosition words label team a t ordering uses cells packets reports p
    sa.after pub mac state s mem mt es cursor raw (sa.cube.stop+1) prepare parsed.seed kept frameFit rawLow rawHigh room
    teamFit widthFit wpos useBit siteID source align fields digits parsed.subtotal bounded suppliedRows total cap sep
  exact ⟨receipt,rfl,rfl,rfl,kept,clock⟩

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI
