import OAI.Hierarchy.ProtocolRAMCatalystPurchasedBirth
import OAI.Hierarchy.ProtocolRAMCatalystStripDateEntry
import OAI.Hierarchy.ProtocolRAMCatalystStripLedgerReads
import OAI.Hierarchy.ProtocolRAMCatalystStripOwners
import OAI.Hierarchy.ProtocolRAMCatalystDateLive

namespace OAI
/-! # Dated signed cash and owner words on an actual purchased strip -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard BoughtSockets PurchaseFrozen
open CatalystArchive ColumnWires StripDirectory PurchaseStage StockCommit RepairHistogram
open scoped Classical Fin.CommRing
variable {z W k q depth payload K : ℕ}
local notation "N" => Stages z (2^W)
local notation "P" => Fintype.card (PayloadRole N k)
local notation "R" => Fintype.card (PurchasedRole depth k)
local notation "D" => max P R
local notation "bits" => Native.wordBits z (2^W) Native.copies
local notation "dim" => Fintype.card (CoreBoard.Columns z (2^W))*k
variable (F : Type) [Field F] [Nonempty (Fin k)] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
local instance : Nonempty (PurchasedRole depth k) :=
  ⟨.catalyst (ChainStrip.inlet depth 0) (Classical.choice inferInstance)⟩
variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : CatalogueRows.Board)
  (G : PortBanks ((c.inject+c.cool)*c.outerFuel)) (arena : Arena)
  (p : Fin (c.inject+c.cool)) (a : Fin c.outerFuel) (j t prior : ℕ)
  (phi : PhasePrice)
local notation "ev" => Attempt.inner p.val a.val j t
local notation "shelf₀" => (s.outer p.val a.val).market.shelf
local notation "birthShelf[" base "]" => ({shelf₀ with stockBase := base} : Shelf)
local notation "key₀" => s.stratumHeader p.val a.val
local notation "native" => build F (withPorts s c b G) ev prior
local notation "v" => ({(native).market with phase := phi} : Market z (2^W) k)
local notation "g" => (native).pricedArea
local notation "src" => (native).stockSource
local notation "kb" => stratumHeader z (2^W) k s.sampler.degree depth key₀
local notation "strata" => PurchaseFrozen.count z (2^W) k
local notation "span₀" => paths z s.sampler.degree depth
local notation "menu₀" => purchasedMenu F depth k s.positive s.radius s.radius_nonneg s.tolerance
  s.tolerance_pos (s.tree ev) (s.tree_nonneg ev) s.minimum
local notation "board₀" => ({s.inner p.val a.val j t with market := {(s.inner p.val a.val j t).market with
  sampler := s.sampler, depth := depth}} : StripDirectory.Boards z (2^W) k q
    (Fintype.card (ChainStrip.Axes depth k)) (Fintype.card (PurchasedRole depth k)))
local notation "raw₀" => (board₀).build (purchasedFormat F z (2^W) k q depth key₀ shelf₀ s.sampler
  s.positive s.radius s.radius_nonneg s.tolerance s.tolerance_pos (s.tree ev) (s.tree_nonneg ev) s.minimum) prior
local notation "slots₀" => (purchasedChannels (z:=z) (d:=2^W) (k:=k) shelf₀ s.sampler depth key₀).slot
variable (chart : Chart (Native.wordBits z (2^W) Native.copies) q
    (max (Fintype.card (PayloadRole (Stages z (2^W)) k)) (Fintype.card (PurchasedRole depth k)))) (before : Memory (Native.wordBits z (2^W) Native.copies)) (labels : LabelSource)
local notation "rep" => Calendar.repair chart ev
local notation "gate" => (guard chart ev).apply before
local notation "snap" => commitMemory chart ev before g src labels
local notation "flags₀" => flagBank shelf₀ s.sampler z (2^W) k depth

/-- Addresses and fitted native tests at the purchased attempt. The original
failure bank, its checked threshold and the reserve outcome are computed. -/
structure PurchasedFrame : Prop where
  raw : chart.raw ev=testedBoard (v).failures (native).board
  layout : chart.layout ev=(v).layout
  «prefix» : chart.frozen ev=(v).prefix
  ready : Calendar.ready chart (.attempt ev) before
  rows : (v).rows≤(v).failures.rows
  cap : (v).rows≤(v).failures.bank.size
  bitsFit : (v).rows≤(rep).repairBits.size
  cut : (v).failures.cut<2^bits
  failureOrder : (v).failures.base+(v).rows≤(rep).tests.excess.out ∧ (v).failures.base+(v).rows≤(rep).tests.payload.out ∧
    (v).failures.base+(v).rows≤(rep).tests.discrepancy.out
  mask : MaskSpace (v).layout rep
  maskLow : (rep).repairBits.base+(v).rows≤labels.out
  order : labels.out≤(g).start
  flagLow : (flags₀).base+(flags₀).size≤chart.stopAt ev

omit [Nonempty (Fin k)] in
private theorem original_bought_flag (frame : PurchasedFrame F s c b G p a j t prior phi chart before labels)
    (rowsFit : strata*span₀≤2^bits)
    (row : Fin (v).rows) (yes : row∈liveRows (enabledBatch (v).layout (native).board) snap (v).rows) :
    (flags₀).read before (row.val:Word bits)≠0 := by
  have ready := frame.ready
  have installed : (rep).failedMIS=(v).failures.bank := by simp only [Calendar.repair,frame.raw]; rfl
  have literal : (rep).batch.owner=.row := by simp only [Calendar.repair,frame.raw]; rfl
  have eq : enabledBatch (v).layout rep=enabledBatch (v).layout (native).board := by
    change {(chart.raw ev).batch with enabled:=(chart.raw ev).repairBits,owner:=.row}=
      {(native).board.batch with enabled:=(native).board.repairBits,owner:=.row}
    rw [frame.raw]; rfl
  have started : prepared chart ev before=(v).prefix.after gate := by rw [prepared,frame.prefix]
  have live : row∈liveRows (enabledBatch (v).layout rep)
      (stageInput g src labels (postOutput (v).layout rep ((v).prefix.after gate))) (v).rows := by
    have charged := (Finset.mem_filter.mp yes).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change committed (enabledBatch (v).layout (native).board) (commitMemory chart ev before g src labels) (row.val:Word bits) at charged
    simpa only [commitMemory,frame.layout,started,eq] using charged
  have stageReady : (v).ready gate := by
    have ok := ready.2.1
    rw [frame.prefix] at ok
    exact ok
  have auditsReady : AuditReady (audits (v).layout rep) (postSnapshot (v).layout rep ((v).prefix.after gate)) := by
    simpa only [frame.layout,started] using ready.2.2.2.2.2.2.1
  have four : 4≤2^bits := Nat.le_trans (by decide : 4≤2^2) (Nat.pow_le_pow_right (by decide) (by unfold Native.wordBits; omega))
  have entered := (v).committed_live_at_price rep gate row g src labels stageReady literal installed rowsFit
    frame.rows frame.cap frame.bitsFit four frame.cut frame.failureOrder frame.mask auditsReady frame.maskLow frame.order live
  change (flags₀).read gate (row.val:Word bits)≠0 at entered
  have low : (flags₀).base+((row.val:Word bits).val%(flags₀).size)<chart.stopAt ev :=
    (Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le frame.flagLow
  change image (chart.stopAt ev) 1 _ before _ ≠ 0 at entered
  rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl low)] at entered
  exact entered

omit [Nonempty (Fin k)] in
/-- Recover the genuine retained birth of every committed physical stock row
from the checked failure bit, the original tile records and the birth flag
archive. The same numerical row indexes the final reporter operands. -/
theorem PurchasedFrame.live_paths (frame : PurchasedFrame F s c b G p a j t prior phi chart before labels)
    (π : Equiv.Perm (Fin (2^z))) (birthStock : ℕ) (phase : PhasePrice) (price : ℝ)
    (kind : ℕ) (origin : Shelf.Mem z (2^W))
    (saved : ArchiveReads (birthShelf[birthStock]) s.sampler π depth key₀ phase price kind origin before k)
    (rooms : strata≤2^bits ∧ (depth+1)*span₀≤2^bits)
    (whole : strata*span₀≤2^bits) (stock : PurchaseInventory.footprint z N k≤2^bits)
    (row : Fin (v).rows) (yes : row∈liveRows (enabledBatch (v).layout (native).board) snap (v).rows) :
    ∃ path : LiveChains s.sampler π depth (actualMarks (birthShelf[birthStock]) phase price kind origin (k:=k)),
      BoughtLocation.relative path=row := by
  have flag:=original_bought_flag F s c b G p a j t prior phi chart before labels frame whole row yes
  obtain ⟨board,number,_⟩:=liveBoardEquiv_relative (birthShelf[birthStock]) s.sampler π depth key₀ s.positive
    phase price kind origin before saved.tiles saved.flags saved.header rooms.1 rooms.2 whole
    (by unfold Native.wordBits;omega) stock
  exact ⟨board ⟨row,flag⟩,number _⟩

local notation "sizes" => StripSizes raw₀ slots₀ (board₀).start D (Fintype.card (menu₀).index) (PacketWidths.ofMenu menu₀).maximum snap
private abbrev purchasedSizeAt := sizes

variable (size : purchasedSizeAt F s c b G p a j t prior chart before labels)
local notation "purchasedInput[" bound "]" => StripInput.of_purchased (F:=F) depth key₀ shelf₀ s.sampler s.positive s.radius s.radius_nonneg
  s.tolerance s.tolerance_pos (s.tree ev) (s.tree_nonneg ev) s.minimum board₀ prior (board₀).start snap bound
local notation "x" => purchasedInput[size]

omit [Nonempty (Fin k)] in
private theorem purchasedAffirmative (frame : PurchasedFrame F s c b G p a j t prior phi chart before labels)
    (whole : strata*span₀ ≤ 2^bits) (sameMemory : (x).mem = snap)
    (batch : (x).ballot = enabledBatch (v).layout (native).board)
    (row : Fin (x).raw.market.rows) (active : row ∈ liveRows (x).ballot (x).mem (x).raw.market.rows) :
    (flags₀).read before (row.val : Word bits) ≠ 0 := by
  let key : Word bits := row.val
  have paid : committed (x).ballot (x).mem key := (Finset.mem_filter.mp active).2
  have atSnapshot : committed (x).ballot snap key :=
    (congrArg (fun memory : Memory bits => committed (x).ballot memory key) sameMemory).mp paid
  have atBoard : committed (enabledBatch (v).layout (native).board) snap key :=
    (congrArg (fun source => committed source snap key) batch).mp atSnapshot
  have entered : row ∈ liveRows (enabledBatch (v).layout (native).board) snap (v).rows :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, atBoard⟩
  exact original_bought_flag F s c b G p a j t prior phi chart before labels frame whole row entered

set_option cleanup.letToHave false in
set_option maxHeartbeats 1300000 in
/-- Install the entry at its genuine calendar input, posting cash in the
original padded order. The selected birth determines all purchased owners. -/
def purchasedDate (frame : PurchasedFrame F s c b G p a j t prior phi chart before labels)
    (π : Equiv.Perm (Fin (2^z))) (groups : Fin G.oldGroups ≃ AllGroups z (2^W))
    (packed : TaggedShorterSupergroups.Directory
      (TaggedShorterSupergroups.reserved z W (ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel))) G.height)
    (bins : G.bins=packed.groups)
    (hdr : key₀=G.directory.keysBase) (birthStock : ℕ) (phase : PhasePrice) (price : ℝ) (kind : ℕ) (origin : Shelf.Mem z (2^W))
    (saved : ArchiveReads (birthShelf[birthStock]) s.sampler π depth key₀ phase price kind origin before k)
    (reports : ColumnROM.Tables z W k ((c.inject+c.cool)*c.outerFuel) G.column G.directory.remapBase
      G.directory.sitesBase G.directory.superBase groups packed π before)
    (rooms : strata ≤ 2^bits ∧ (depth+1)*span₀ ≤ 2^bits)
    (whole : strata*span₀≤2^bits) (stock : PurchaseInventory.footprint z N k≤2^bits)
    (header : (header F (withPorts s c b G) ev).Loaded before)
    (low : ℕ) (protect : ∀y,y<low → Calendar.protected chart y (.attempt ev))
    (below : low≤labels.out) (keysEnd : (kb).stop≤low)
    (tileEnd : ∀i : Key z (2^W) k,((shelf₀).L s.sampler depth i).source.base+(depth+1)*span₀≤low)
    (commit : chart.commit ev=pricedSegment g src labels bits (x).ballot)
    (out : EventBoard (fresh g src) bits)
    {J : Type} [Fintype J] (catalogue : PacketWidths J) (includeMenu : (menu₀).index→J)
    (widths : ∀i,catalogue.width (includeMenu i)=((menu₀).packet i).width)
    (mass : (board₀).copies=catalogue.copiesAt K payload) (scale : 0<K) (idle : Fin dim) :
    Date chart ev before ((ownerLedger s c b G F arena).term (.attempt ev))
      ((g).direct+(native).occurrences) ((ownerLedger s c b G F arena).rows (.attempt ev)) dim payload := by
  let flag := fun i : Fin (strata*span₀) => (flags₀).read before (i.val:Word bits)≠0
  let marks := actualMarks (birthShelf[birthStock]) phase price kind origin (k:=k)
  let unique := actualMarks_unique (birthShelf[birthStock]) phase price kind origin (k:=k)
  have dirKeys : (stratumHeader z (2^W) k s.sampler.degree depth G.directory.keysBase).Loaded before := hdr ▸ saved.header
  have existsBoard := ledger_purchased_rom s c b G F arena π groups packed bins p a j t birthStock phase price
    kind origin before saved.flags saved.tiles reports dirKeys rooms whole stock header size.portFit
  let board := existsBoard.choose
  have read := existsBoard.choose_spec.2
  have nowKeys := retained_header chart ev before g src labels frame.ready kb saved.header (keysEnd.trans below)
    frame.order (fun y _ hi=>protect y (hi.trans_le keysEnd))
  have tiles (i : Key z (2^W) k) : ProtocolRAMPurchaseGateColumns.TileRows ((shelf₀).L s.sampler depth i).source
      (Shelf.pathRows s.sampler π depth i) snap := by
    have endAt : ((shelf₀).L s.sampler depth i).source.base+
          (depth+1)*(PurchaseDFS.layout (2^z) s.sampler.degree depth).length≤low := by
      simpa only [PurchaseFrozen.paths,PurchaseDFS.length_layout] using tileEnd i
    exact retained_tiles chart ev before g src labels frame.ready _ _ (saved.tiles i) (endAt.trans below) frame.order
      (fun y _ hi => protect y (hi.trans_le endAt))
  have ordinary := purchased_addresses (F:=F) depth key₀ shelf₀ s.sampler s.positive s.radius s.radius_nonneg
    s.tolerance s.tolerance_pos (s.tree ev) (s.tree_nonneg ev) s.minimum board₀ prior (board₀).start
    snap size π nowKeys tiles rooms.1 rooms.2 marks (fun row live => by
      obtain ⟨path,equal⟩ := PurchasedFrame.live_paths F s c b G p a j t prior phi chart before labels frame
        π birthStock phase price kind origin saved rooms whole stock row live
      exact ⟨path,congrArg Fin.val equal⟩)
  have sameForm : (x).form = native := by
    change (x).form = PortPadding.format D (board₀).start slots₀ raw₀
    exact purchased_native (F:=F) depth key₀ shelf₀ s.sampler s.positive s.radius s.radius_nonneg
      s.tolerance s.tolerance_pos (s.tree ev) (s.tree_nonneg ev) s.minimum board₀ prior (board₀).start snap size
  have sameMemory : (x).mem = snap := by
    dsimp only [StripInput.of_purchased,StripInput.ofBoard]
  have snapshot : (x).mem = stageInput (x).form.pricedArea (x).form.stockSource labels
      (postOutput (chart.layout ev) (Calendar.repair chart ev) (prepared chart ev before)) := by
    exact sameMemory.trans (congrArg
      (fun form : Format z (2^W) k q D => stageInput form.pricedArea form.stockSource labels
        (postOutput (chart.layout ev) (Calendar.repair chart ev) (prepared chart ev before))) sameForm.symm)
  have readyCommit : chart.commit ev = pricedSegment (x).form.pricedArea (x).form.stockSource labels bits (x).ballot := by
    rw [sameForm]
    exact commit
  have fitted : EventBoard (fresh (x).form.pricedArea (x).form.stockSource) bits := by
    rw [sameForm]
    exact out
  have batch : (x).ballot = enabledBatch (v).layout (native).board :=
    congrArg (fun form : Format z (2^W) k q D => enabledBatch (v).layout form.board) sameForm
  have covered (row : Fin (x).raw.market.rows)
      (active : row ∈ liveRows (x).ballot (x).mem (x).raw.market.rows) :
      ∃r, boughtBalls flag board r = row := by
    exact bought_covered flag board row (purchasedAffirmative F s c b G p a j t prior phi chart before labels size
      frame whole sameMemory batch row active)
  exact Date.ofStrip («menu» := menu₀) (K:=K) (payload:=payload) x (boughtBalls flag board)
    (paidColumns s.sampler π depth marks unique) (pairKeys (CoreBoard.Columns z (2^W)) k).toEmbedding
    idle scale ordinary catalogue includeMenu widths mass chart ev before ((ownerLedger s c b G F arena).term (.attempt ev))
    labels readyCommit frame.ready fitted snapshot covered read

/-- All finite tables and physical range information at one purchased date.
The frozen price for the inner test can be the actual deadline price. Its
birth shelf may originate at a distinct price and phase. -/
structure PurchasedLocal (permutation : Equiv.Perm (Fin (2^z))) (groups : Fin G.oldGroups ≃ AllGroups z (2^W))
    (packed : TaggedShorterSupergroups.Directory
      (TaggedShorterSupergroups.reserved z W (ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel))) G.height)
    (K payload : ℕ) where
  priceAtTime : PhasePrice
  bounds : StripSizes.Room raw₀ slots₀ (board₀).start D (Fintype.card (menu₀).index) (PacketWidths.ofMenu menu₀).maximum bits
  frame : PurchasedFrame F s c b G p a j t prior priceAtTime chart before labels
  bins : G.bins=packed.groups
  keyHeader : key₀=G.directory.keysBase
  receipt : PurchasedBirth shelf₀ s.sampler permutation depth key₀ before k
  rooms : strata ≤ 2^bits ∧ (depth+1)*span₀ ≤ 2^bits
  whole : strata*span₀≤2^bits
  stock : PurchaseInventory.footprint z N k≤2^bits
  low : ℕ
  protect : ∀y,y<low → Calendar.protected chart y (.attempt ev)
  below : low≤labels.out
  portEnd : (header F (withPorts s c b G) ev).stop≤low
  keysEnd : (kb).stop≤low
  tileEnd : ∀i : Key z (2^W) k,((shelf₀).L s.sampler depth i).source.base+(depth+1)*span₀≤low
  commit : chart.commit ev=pricedSegment g src labels bits (enabledBatch (native).market.layout (native).board)
  output : EventBoard (fresh g src) bits
  alphabet : Type
  [finite : Fintype alphabet]
  catalogue : PacketWidths alphabet
  includeMenu : (menu₀).index→alphabet
  widths : ∀i,catalogue.width (includeMenu i)=((menu₀).packet i).width
  mass : (board₀).copies=catalogue.copiesAt K payload
  scale : 0<K
  idle : Fin dim

omit [Nonempty (Fin k)] in
theorem PurchasedLocal.owner_paths {π : Equiv.Perm (Fin (2^z))} {groups : Fin G.oldGroups ≃ AllGroups z (2^W)}
    {packed : TaggedShorterSupergroups.Directory
      (TaggedShorterSupergroups.reserved z W (ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel))) G.height}
    (localData : PurchasedLocal F s c b G p a j t prior chart before labels π groups packed K payload)
    (row : Fin (native).market.rows) (yes : row∈liveRows (enabledBatch (native).market.layout (native).board) snap (native).market.rows) :
    ∃ path : LiveChains s.sampler π depth (actualMarks (birthShelf[localData.receipt.stock])
      localData.receipt.phase localData.receipt.price localData.receipt.kind localData.receipt.frozen (k:=k)),
      BoughtLocation.relative path=row :=
  localData.frame.live_paths F s c b G p a j t prior localData.priceAtTime chart before labels π
    localData.receipt.stock localData.receipt.phase localData.receipt.price localData.receipt.kind
    localData.receipt.frozen localData.receipt.saved localData.rooms localData.whole localData.stock row yes

/-- Join the two original globally installed ROM banks to the local dated source. -/
structure PurchasedData (K payload : ℕ) where
  permutation : Equiv.Perm (Fin (2^z))
  groups : Fin G.oldGroups ≃ AllGroups z (2^W)
  packed : TaggedShorterSupergroups.Directory
    (TaggedShorterSupergroups.reserved z W (ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel))) G.height
  birth : PurchasedLocal F s c b G p a j t prior chart before labels permutation groups packed K payload
  reports : ColumnROM.Tables z W k ((c.inject+c.cool)*c.outerFuel) G.column G.directory.remapBase
    G.directory.sitesBase G.directory.superBase groups packed permutation before
  portHeader : (header F (withPorts s c b G) ev).Loaded before

variable {F s c b G p a j t prior chart before labels}
def PurchasedLocal.observe {π groups packed}
    (data : PurchasedLocal F s c b G p a j t prior chart before labels π groups packed K payload)
    (reports : ColumnROM.Tables z W k ((c.inject+c.cool)*c.outerFuel) G.column G.directory.remapBase
      G.directory.sitesBase G.directory.superBase groups packed π before)
    (port : (header F (withPorts s c b G) ev).Loaded before) :
    PurchasedData F s c b G p a j t prior chart before labels K payload :=
  ⟨π,groups,packed,data,reports,port⟩

/-- Combine the actual guarded market, selected birth and priced signed
columns into the single dated record consumed by reconciliation. -/
def PurchasedData.date (data : PurchasedData F s c b G p a j t prior chart before labels K payload)
    (reserveArena : Arena) :
    Date chart ev before ((ownerLedger s c b G F reserveArena).term (.attempt ev))
      ((g).direct+(native).occurrences) ((ownerLedger s c b G F reserveArena).rows (.attempt ev)) dim payload := by
  letI := data.birth.finite
  have loaded := retained_header chart ev before g src labels data.birth.frame.ready
    (header F (withPorts s c b G) ev) data.portHeader (data.birth.portEnd.trans data.birth.below)
    data.birth.frame.order (fun y _ hi=>data.birth.protect y (hi.trans_le data.birth.portEnd))
  have actual : sizes := StripSizes.of_header data.birth.bounds loaded
  exact purchasedDate F s c b G reserveArena p a j t prior data.birth.priceAtTime chart before labels actual data.birth.frame
    data.permutation data.groups data.packed data.birth.bins data.birth.keyHeader data.birth.receipt.stock data.birth.receipt.phase
    data.birth.receipt.price data.birth.receipt.kind data.birth.receipt.frozen data.birth.receipt.saved data.reports
    data.birth.rooms data.birth.whole data.birth.stock data.portHeader
    data.birth.low data.birth.protect data.birth.below data.birth.keysEnd data.birth.tileEnd data.birth.commit data.birth.output data.birth.catalogue data.birth.includeMenu
    data.birth.widths data.birth.mass data.birth.scale data.birth.idle

omit [Nonempty (Fin k)] in
/-- The signed record retains the native ball number and the true catalyst
role in the purchased term alphabet, including when the board is padded. -/
theorem PurchasedData.positive_ports (data : PurchasedData F s c b G p a j t prior chart before labels K payload)
    (reserveArena : Arena) :
    PositivePorts (fun c y=>(.catalyst c y : PurchasedRole depth k))
      (header F (withPorts s c b G) ev).rows D (data.date reserveArena).entry := by
  dsimp only [PurchasedData.date,purchasedDate,Date.ofStrip,Date.of_priced,readEntry]
  apply repair_positive_ports

end Calendar.StripChart
end Hierarchy.ProtocolRAM
end

end OAI
