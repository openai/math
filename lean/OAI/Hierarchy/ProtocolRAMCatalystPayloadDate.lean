import OAI.Hierarchy.ProtocolRAMCatalystStripDateEntry
import OAI.Hierarchy.ProtocolRAMCatalystStripLedgerReads
import OAI.Hierarchy.ProtocolRAMCatalystStripOwners
import OAI.Hierarchy.ProtocolRAMCatalystDateLive

namespace OAI
/-! # Signed catalyst rows issued by the actual payload attempt -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe CatalystArchive ProbeStage ProbeStage.Native CoreBoard ColumnWires
open PurchaseStage RepairHistogram StockCommit PurchaseFrozen StripDirectory BoughtSockets CatalogueRows
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Fin.CommRing Classical
variable {z W k q depth K payload : ℕ}
local notation "bits" => Native.wordBits z (2^W) Native.copies
local notation "N" => Stages z (2^W)
local notation "P" => Fintype.card (PayloadRole N k)
local notation "R" => Fintype.card (PurchasedRole depth k)
local notation "D" => max P R
local notation "num" => Fintype.card (CoreBoard.Columns z (2^W))*k

section
variable (F : Type*) [Field F] [Nonempty (Fin k)] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] (s : Boards z (2^W) k q depth)
  (c : Mesh) (b : CatalogueRows.Board) (G : PortBanks ((c.inject+c.cool)*c.outerFuel)) (ar : Arena)
  (p a incoming : ℕ)
local notation "evt" => (Attempt.outer p a)
local notation "menu" => payloadMenu F N k s.positive s.radius s.radius_nonneg s.tolerance s.tolerance_pos
  (s.tree evt) (s.tree_nonneg evt) s.minimum
local notation "surface" => (show StripDirectory.Boards z (2^W) k q (Fintype.card (PayloadStrip.Quotes N k)) P from
  {s.outer p a with market:={(s.outer p a).market with sampler:=s.sampler,depth:=depth}})
local notation "src" => (surface).build (payloadFormat F z (2^W) k q s.positive s.radius s.radius_nonneg
  s.tolerance s.tolerance_pos (s.tree evt) (s.tree_nonneg evt) s.minimum) incoming
local notation "fmt" => build F (withPorts s c b G) evt incoming
local notation "L" => ownerLedger s c b G F ar
variable (C : Chart (Native.wordBits z (2^W) Native.copies) q
    (max (Fintype.card (PayloadRole (Stages z (2^W)) k)) (Fintype.card (PurchasedRole depth k)))) (before : Memory (Native.wordBits z (2^W) Native.copies)) (labels : LabelSource) (finish : ℝ) (fees : PhasePrice)
local notation "m" => commitMemory C evt before (fmt).pricedArea (fmt).stockSource labels
local notation "v" => (fmt).atTime c finish fees evt
local notation "prior" => (guard C evt).apply before
local notation "B" => Calendar.repair C evt

local notation "inputP[" bounds "]" => StripInput.of_payload (F:=F) s.positive s.radius s.radius_nonneg s.tolerance s.tolerance_pos
    (s.tree evt) (s.tree_nonneg evt) s.minimum surface incoming (s.outer p a).start m bounds

omit [Nonempty (Fin k)] in
private theorem payloadCovered
    (size : StripSizes src (payloadChannels z N k).slot (s.outer p a).start D
      (Fintype.card (menu).index) (PacketWidths.ofMenu menu).maximum m)
    (all : 2^z≤(v).rows) (prefixFit : 2^z<2^bits)
    (layout : C.layout evt=(v).layout) (frozen : prepared C evt before=(v).prefix.after prior)
    (ballot : enabledBatch (fmt).market.layout (fmt).board=enabledBatch (v).layout B)
    (source : (v).DateMaskRoom B prior (fmt).pricedArea labels) :
    let x := inputP[size]
    let rows := payloadBalls z x.raw.market.rows all
    ∀ (j : Fin x.raw.market.rows), j∈liveRows x.ballot m x.raw.market.rows → ∃r,rows r=j := by
  intro x rows j active
  have sel : j∈liveRows (enabledBatch (v).layout B)
      (stageInput (fmt).pricedArea (fmt).stockSource labels (postOutput (v).layout B ((v).prefix.after prior))) (v).rows := by
    have charged := (Finset.mem_filter.mp active).2
    change committed (enabledBatch (fmt).market.layout (fmt).board)
      (commitMemory C evt before (fmt).pricedArea (fmt).stockSource labels) (j.val : Word bits) at charged
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [commitMemory,layout,frozen,ballot] using charged
  have real := source.live (fmt).stockSource j sel
  have hi := payload_entered s c b G F p a incoming prior j (j.isLt.trans_le source.fits) prefixFit real
  exact ⟨⟨j.val,hi⟩,Fin.ext rfl⟩

omit [Nonempty (Fin k)] in
private theorem payloadSnapshot
    (size : StripSizes src (payloadChannels z N k).slot (s.outer p a).start D
      (Fintype.card (menu).index) (PacketWidths.ofMenu menu).maximum m) :
    let x := inputP[size]
    x.mem = stageInput x.form.pricedArea x.form.stockSource labels
      (postOutput (C.layout evt) (Calendar.repair C evt) (prepared C evt before)) := by
  intro x
  have sameForm : x.form = fmt := by
    change x.form = PortPadding.format D (s.outer p a).start (payloadChannels z N k).slot src
    exact payload_native (F:=F) s.positive s.radius s.radius_nonneg s.tolerance s.tolerance_pos
      (s.tree evt) (s.tree_nonneg evt) s.minimum surface incoming (s.outer p a).start m size
  have sameMemory : x.mem = m := by
    dsimp only [x, StripInput.of_payload, StripInput.ofBoard]
  exact sameMemory.trans (congrArg
    (fun form : Format z (2^W) k q D => stageInput form.pricedArea form.stockSource labels
      (postOutput (C.layout evt) (Calendar.repair C evt) (prepared C evt before))) sameForm.symm)

set_option cleanup.letToHave false in
set_option maxHeartbeats 400000 in
/-- The retained output permutation is read on entry, the checked mask on the actual
price input. Every other argument is a native address, capacity, or public layout. -/
def payloadDate {J : Type*} [Fintype J] (other : PacketWidths J)
    (size : StripSizes src (payloadChannels z N k).slot (s.outer p a).start D
      (Fintype.card (menu).index) (PacketWidths.ofMenu menu).maximum m)
    (π : Equiv.Perm (Fin (2^z))) (groups : Fin G.oldGroups≃AllGroups z (2^W))
    (packed : TaggedShorterSupergroups.Directory
      (TaggedShorterSupergroups.reserved z W (ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel))) G.height)
    (bins : G.bins=packed.groups)
    (reports : ColumnROM.Tables z W k ((c.inject+c.cool)*c.outerFuel) G.column G.directory.remapBase
      G.directory.sitesBase G.directory.superBase groups packed π before)
    (outputs : Native.Resident (Native.initialOutput z) before (fun x : Fin (2^z)=>(π x).val))
    (all : 2^z≤(v).rows) (prefixFit : 2^z<2^bits) (loaded : (header F (withPorts s c b G) evt).Loaded before)
    (words : D≤2^bits) (idle : Fin num) (scale : 0<K)
    (mass : (s.outer p a).copies=((PacketWidths.ofMenu menu).either other).copiesAt K payload)
    (ready : Calendar.ready C (.attempt evt) before) (cash : EventBoard (fresh (fmt).pricedArea (fmt).stockSource) bits)
    (commit : C.commit evt=pricedSegment (fmt).pricedArea (fmt).stockSource labels bits (enabledBatch (fmt).market.layout (fmt).board))
    (layout : C.layout evt=(v).layout) (frozen : prepared C evt before=(v).prefix.after prior)
    (ballot : enabledBatch (fmt).market.layout (fmt).board=enabledBatch (v).layout B)
    (source : (v).DateMaskRoom B prior (fmt).pricedArea labels) :
    Date C evt before ((L).term (.attempt evt)) ((fmt).pricedArea.direct+(fmt).occurrences) ((L).rows (.attempt evt)) num payload := by
  let x := inputP[size]
  let rows := payloadBalls z x.raw.market.rows all
  have cover := payloadCovered F s c b G p a incoming C before labels finish fees size all prefixFit layout frozen ballot source
  have stock := payload_addresses_of_coverage (F:=F) s.positive s.radius s.radius_nonneg s.tolerance
    s.tolerance_pos (s.tree evt) (s.tree_nonneg evt) s.minimum surface incoming (s.outer p a).start m size all cover
  have onBank := ledger_payload_rom s c b G F ar p a π groups packed bins before reports outputs all loaded words
  have sameMemory : x.mem = m := by
    dsimp only [x, StripInput.of_payload, StripInput.ofBoard]
  have chargedRows (j : Fin x.raw.market.rows) (live : j ∈ liveRows x.ballot x.mem x.raw.market.rows) :
      ∃ r, rows r = j :=
    cover j ((congrArg (fun memory => j ∈ liveRows x.ballot memory x.raw.market.rows) sameMemory).mp live)
  let cols := payloadPlaceAll (d:=2^W) π
  let account := (pairKeys (CoreBoard.Columns z (2^W)) k).toEmbedding
  have reads (u : Fin (2^z) × (PayloadStrip.Columns N × Fin k)) :
      ((L).term (.attempt evt)).eval before
        ((finProdFinEquiv (portCell (H:=Fin (PayloadStrip.edgeCount N))
          (E:=PayloadStrip.Quotes N k ⊕ Empty) rows x.ports u)).val : Word bits) =
      ((account (physical cols u)).val : Word bits) := by
    exact onBank u
  have snapshot := payloadSnapshot F s c b G p a incoming C before labels size
  have recv : C.commit evt = pricedSegment x.form.pricedArea x.form.stockSource labels bits x.ballot := commit
  have fitted : EventBoard (fresh x.form.pricedArea x.form.stockSource) bits := cash
  change Date C evt before ((L).term (.attempt evt)) (x.form.pricedArea.direct+x.form.occurrences)
    (x.raw.market.rows*D) num payload
  exact Date.ofStrip («menu» := menu) (K:=K) (payload:=payload) x rows cols account idle
      scale stock ((PacketWidths.ofMenu menu).either other) Sum.inl (fun _=>rfl) mass C evt before ((L).term (.attempt evt))
      labels recv ready fitted snapshot chargedRows reads

/-- The bounded data used by the payload constructor at a date. It contains original
ROM words, sizes, and layout identifications against the chronological RAM machine. -/
structure PayloadData {J : Type*} [Fintype J] (other : PacketWidths J) where
  size : StripSizes src (payloadChannels z N k).slot (s.outer p a).start D
      (Fintype.card (menu).index) (PacketWidths.ofMenu menu).maximum m
  π : Equiv.Perm (Fin (2^z))
  groups : Fin G.oldGroups≃AllGroups z (2^W)
  packed : TaggedShorterSupergroups.Directory
      (TaggedShorterSupergroups.reserved z W (ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel))) G.height
  bins : G.bins=packed.groups
  reports : ColumnROM.Tables z W k ((c.inject+c.cool)*c.outerFuel) G.column G.directory.remapBase
      G.directory.sitesBase G.directory.superBase groups packed π before
  outputs : Native.Resident (Native.initialOutput z) before (fun x : Fin (2^z)=>(π x).val)
  all : 2^z≤(v).rows
  prefixFit : 2^z<2^bits
  loaded : (header F (withPorts s c b G) evt).Loaded before
  words : D≤2^bits
  idle : Fin num
  scale : 0<K
  mass : (s.outer p a).copies=((PacketWidths.ofMenu menu).either other).copiesAt K payload
  ready : Calendar.ready C (.attempt evt) before
  cash : EventBoard (fresh (fmt).pricedArea (fmt).stockSource) bits
  commit : C.commit evt=pricedSegment (fmt).pricedArea (fmt).stockSource labels bits (enabledBatch (fmt).market.layout (fmt).board)
  layout : C.layout evt=(v).layout
  frozen : prepared C evt before=(v).prefix.after prior
  ballot : enabledBatch (fmt).market.layout (fmt).board=enabledBatch (v).layout B
  source : (v).DateMaskRoom B prior (fmt).pricedArea labels

/-- Local inputs and scalar layout checks; global permutation, column directories
and port headers are supplied once by the original boot image. -/
structure PayloadLocal {J : Type*} [Fintype J] (other : PacketWidths J) where
  size : StripSizes.Room src (payloadChannels z N k).slot (s.outer p a).start D
      (Fintype.card (menu).index) (PacketWidths.ofMenu menu).maximum bits
  headerRoom : (header F (withPorts s c b G) evt).stop≤labels.out
  headerGuard : ∀x,(header F (withPorts s c b G) evt).start≤x → x<(header F (withPorts s c b G) evt).stop →
    Calendar.protected C x (.attempt evt)
  all : 2^z≤(v).rows
  prefixFit : 2^z<2^bits
  words : D≤2^bits
  idle : Fin num
  scale : 0<K
  mass : (s.outer p a).copies=((PacketWidths.ofMenu menu).either other).copiesAt K payload
  ready : Calendar.ready C (.attempt evt) before
  cash : EventBoard (fresh (fmt).pricedArea (fmt).stockSource) bits
  commit : C.commit evt=pricedSegment (fmt).pricedArea (fmt).stockSource labels bits (enabledBatch (fmt).market.layout (fmt).board)
  layout : C.layout evt=(v).layout
  frozen : prepared C evt before=(v).prefix.after prior
  ballot : enabledBatch (fmt).market.layout (fmt).board=enabledBatch (v).layout B
  source : (v).DateMaskRoom B prior (fmt).pricedArea labels


variable {F s c b G p a incoming C before labels finish fees}

def PayloadLocal.observe {J : Type*} [Fintype J] {other : PacketWidths J}
    (r : PayloadLocal (K:=K) (payload:=payload) F s c b G p a incoming C before labels finish fees other)
    (π : Equiv.Perm (Fin (2^z))) (groups : Fin G.oldGroups≃AllGroups z (2^W))
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W
      (ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel))) G.height)
    (bins : G.bins=packed.groups)
    (cols : ColumnROM.Tables z W k ((c.inject+c.cool)*c.outerFuel) G.column G.directory.remapBase
      G.directory.sitesBase G.directory.superBase groups packed π before)
    (input : Native.Resident (Native.initialOutput z) before (fun i : Fin (2^z)=>(π i).val))
    (head : (header F (withPorts s c b G) evt).Loaded before) :
    PayloadData (K:=K) (payload:=payload) F s c b G p a incoming C before labels finish fees other := by
  have installed := retained_header C evt before (fmt).pricedArea (fmt).stockSource labels r.ready
    (header F (withPorts s c b G) evt) head r.headerRoom r.source.ordered r.headerGuard
  exact ⟨StripSizes.of_header r.size installed,π,groups,packed,bins,cols,input,r.all,r.prefixFit,head,r.words,r.idle,r.scale,r.mass,r.ready,
    r.cash,r.commit,r.layout,r.frozen,r.ballot,r.source⟩


def PayloadData.date {J : Type*} [Fintype J] {other : PacketWidths J}
    («rec» : PayloadData (K:=K) (payload:=payload) F s c b G p a incoming C before labels finish fees other) (reserveArena : Arena) :
    Date C evt before ((ownerLedger s c b G F reserveArena).term (.attempt evt))
      ((fmt).pricedArea.direct+(fmt).occurrences) ((ownerLedger s c b G F reserveArena).rows (.attempt evt)) num payload :=
  payloadDate F s c b G reserveArena p a incoming C before labels finish fees other
    «rec».size «rec».π «rec».groups «rec».packed «rec».bins «rec».reports
    «rec».outputs «rec».all «rec».prefixFit «rec».loaded «rec».words «rec».idle
    «rec».scale «rec».mass «rec».ready «rec».cash «rec».commit «rec».layout
    «rec».frozen «rec».ballot «rec».source

omit [Nonempty (Fin k)] in
/-- A positive payload cash occurrence is an original ball and catalyst
column, in the very same padded row-major order as the owner scan. -/
theorem PayloadData.positive_ports {J : Type*} [Fintype J] {other : PacketWidths J}
    («rec» : PayloadData (K:=K) (payload:=payload) F s c b G p a incoming C before labels finish fees other)
    (reserveArena : Arena) :
    PositivePorts (fun c j=>(.catalyst c j : PayloadRole N k))
      (header F (withPorts s c b G) evt).rows D («rec».date reserveArena).entry := by
  dsimp only [PayloadData.date,payloadDate,Date.ofStrip,Date.of_priced,readEntry]
  -- The final argument of the stored entry is its bound on every positive debit.
  -- Supply that proof explicitly since unification may discard it by proof irrelevance.
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let target ← goal.getType
      let some entry ← Lean.Meta.whnfUntil target.getAppArgs.back! ``repairEntry
        | throwError "could not expose the constructed repair entry"
      let args := entry.getAppArgs
      let proof ← Lean.Meta.mkAppM ``repair_positive_ports (args.extract (args.size - 7) args.size)
      goal.assign proof

end
end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
