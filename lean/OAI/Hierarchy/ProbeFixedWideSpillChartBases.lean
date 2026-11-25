import OAI.Hierarchy.ProtocolRAMDateSpillSectorRead
import OAI.Hierarchy.ProbeFixedWideSpillTurnActive
import OAI.Hierarchy.ProbeFixedWideSpillRolePages
import OAI.Hierarchy.TaggedWideCalendarSpill

namespace OAI
/-! # Dated chord prefixes read by the signed native turn publisher -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h



open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
local notation "order" => v.wideOrder h width
local notation "sheet" => v.wideSignedPage h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "original" => TerminalLayout.reserve start cnt page
local notation "L" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "C" => v.wideSignedChart h width stock
local notation "last" => (events v.mesh).length
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (bits : ℕ)
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "hi" => v.wideRoleStart h width stock ss
local notation "full" => v.wideFundedSize h width bits

local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "pub" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K (directory).groups H R
local notation "coreTop" => CoreCatalogue.top h v.W K (directory).groups H R
local notation "coreHead" => CoreCatalogue.headBase h v.W K (directory).groups H

local notation "place" => siteNumber h D k
local notation "mount" => (P).catalogue.coreMount π place order chk
local notation "ord" => CoreRoute.enum mount o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i
local notation "lw" => v.wideWidthLayout h width ss
variable (horizon : v.wideFundedSize h width bits ≤ size) (age : v.wideFundedHeight≤h)
  (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (operandAge : v.wideOperandHeight≤h)
  (issues : Attempt→CatalystArchive.Entry (Fintype.card (Columns h (2^v.W))*k) width)
  (card : recordCount v.mesh issues = rowOnlyCount v.mesh (declaredRows v.mesh
    (ownerLedger (v.nativeBoards (v.widePlacement h width) h width) v.mesh
      (v.widePlacement h width).catalogue (v.widePlacement h width).routes F
      (v.privateArena (v.widePlacement h width) h width))))
  (who : Fin (recordCount v.mesh issues)→Fin (Fintype.card (Columns h (2^v.W))*k))
  (cj : Columns h (2^v.W)×Fin k→Fin (Fintype.card (Columns h (2^v.W))*k))
local notation "dur" => CatalystArchive.debit v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))
local notation "closed" => ReserveUse.output original old supply who dur archive
local notation "settled" => (sink).output closed ord ci (fun j=>(cj j).val)
local notation "rawRow" => (sink).terminalRows closed ord ci (fun j=>(cj j).val)
local notation "counts" => fun e : Fin rows=>(rawRow e).width
variable (marks : Marks h v.W k v.wideJobs) (unique : Exclusive marks)
    (A₀ : WideFundedTurnAlignment v h width size M π raw bits issues who cj marks)

local notation "paid" => PaidWidths.total ss chk
local notation "goods" => fun i : Commodity (Fin (2^h)) N k=>RouteSettlement.actual (old).stock closed (ci i)
local notation "held" => fun j : Columns h D×Fin k=>RouteSettlement.actual (old).reserved closed (cj j).val
local notation "taken" => fun j : Columns h D×Fin k=>RouteSettlement.actual (old).used closed (cj j).val
local notation "term" => (mount).actual.chordWidths paid+(commodityGraph π place).chordWidths goods+
  (catalystGraph place).chordWidths (fun j=>held j-taken j)

local notation "shape" => RoleRoom.shape («R»:=WideMemory.R v.sampler h v.W k) v.sampler directory rows
local notation "z" => shape
local notation "ports" => livePort v.sampler (P).catalogue π marks unique order (v.wideBoughtOrdinal h width π marks) A₀
local notation "oldRows" => Fintype.card (Old h v.W k rows)
local notation "value" => v.wideDatedValue h width bits mid chk issues
local notation "tb" => v.wideTerminalBoard h width bits 0

local notation "bsize" => v.wide_dated_bought_rows h width
local notation "axis" => pairKeys (Columns h D) k
local notation "names" => timeRows v.sampler π v.depth marks (P).catalogue order bsize axis
local notation "ordinal" => (P).catalogue.ordinal v.sampler π v.depth marks order bsize
local notation "embedded" => DatedRows.embed v.sampler π v.depth marks (P).catalogue order bsize
local notation "sparse" => sparseKey v.sampler π v.depth marks (P).catalogue order bsize
  (PurchaseInventory.slotEquiv h N k) axis
local notation "partialRow" => DatedRows.lookup v.sampler π v.depth marks (P).catalogue order bsize names
local notation "direction" => DatedRows.inputSide v.sampler π v.depth marks names
local notation "siteCount" => siteLast h D k+1

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option cleanup.letToHave false
open DatedSpillOffsets LinearAlgebra.SpectralBooks ChordGraph SiteTensor Tagged.PassiveWindow
open CoreBoard.WordSeats
variable (datedROM terminalROM work rankFirst turnFirst : ℕ)
variable (oldStart newStart leftOnly rightOnly : Fin (events v.mesh).length→ℕ) (j : Fin (events v.mesh).length)
local notation "panel" => v.wideSpillTurnPage h width bits datedROM terminalROM work rankFirst turnFirst
  oldStart newStart leftOnly rightOnly j
local notation "b₀" => v.wideTerminalBoard h width bits work
local notation "inventory" => v.wideTerminalStock h width bits
local notation "roles" => HistoryRoles.stride k v.sampler.degree v.wideJobs
local notation "segs" => Fintype.card (HistoryRoles.Source v.sampler π v.depth marks)
local notation "goodsIx" => Goods h v.W k
local notation "cashIx" => Catalogue v.sampler π v.depth marks
local notation "catIx" => Catalysts h v.W k
local notation "skeys" => fun i=>(sparse (names i)).val
local notation "phys" => physical v.sampler π v.depth marks unique
local notation "namedRows" => sorted v.sampler π v.depth marks ∘ names
local notation "fields" => SectorRead v.sampler π v.depth marks unique (P).catalogue order bsize axis oldRows
variable (spill : Goods h v.W k→ℕ) (cap : ℕ) (word : HistoryRoles.stride k v.sampler.degree v.wideJobs*cap<2^Native.wordBits h (2^v.W) Native.copies)
local notation "deposits" => routeLoad (mount).ordinary spill
local notation "spent" => ((Sum.elim (fun _:cashIx=>0) (Sum.elim spill (fun _:catIx=>0))) ∘ names)
local notation "received" => ((Sum.elim (fun e:cashIx=>deposits (ordinal e)) (fun _:goodsIx⊕catIx=>0)) ∘ names)
include horizon age budget small operandAge card A₀ unique word

/-- An actual positive commodity source reads the occupation of the preceding
chronological rows of its chord. The native amount may already be zero at checkout. -/
theorem wide_spill_chart_oldBase (initial out : Memory w)
    (initialLow : ∀x,x<full→initial x=settled x) (outLow : ∀x,x<full → out x=settled x)
    (frozen : ∀x,x<(b₀).endAt+3*oldRows → out x=(b₀).extendedState inventory initial x)
    (replayed : v.wideReplayedTurnBase h width ss≤work) (room : (b₀).endAt+3*oldRows<2^w)
    (sites : siteCount≤2^w) (whole : Fin segs→ℕ)
    (seen : fields (oldStart j) (leftOnly j) datedROM whole spent out)
    (bounded : ∀x,spill x≤cap) (pad : Chord siteCount)
    (source : Fin oldRows) (good : goodsIx) (key : SettledMatrix.Layout.numbered (I:=Goods h v.W k) («A»:=Catalysts h v.W k) («r»:=rows) source=.inr (.inl good))
    (on : 0<whole ((names).symm (.inr (.inl good)))) :
    let dateLayout:=(mount).datedLayout (place).injective pad
    ((panel).left.prefix.eval out (source.val:Word w)).val=
      datedBase dateLayout.family (dateLayout.bits spill) (dateLayout.num.symm (.inr (.inl good))) := by
  intro dateLayout
  let idx:=(names).symm (.inr (.inl good))
  have numerical : work+7*oldRows+4*rows<2^w:=by
    change work+4*oldRows+4*rows+3*oldRows<2^w at room
    omega
  have low:=v.wide_replayed_start h width ss
  have ent:=v.wide_signed_turn_ready_at h width stock ((lw).bank last) ss work (v.fixedTerminalStock_end P h width)
    (low.1.trans replayed) (low.2.trans replayed) numerical
  have highFit : (z).ceiling hi<2^w:=(low.1.trans replayed).trans_lt (by omega)
  have oldFit : oldRows≤2^w:=by omega
  have rawSite:=v.wide_spill_original_goods h width size M π raw bits horizon age budget small operandAge
    issues card who cj marks unique A₀ work initial out initialLow highFit oldFit source (.inl good)
    key ent.1 ent.2 room frozen sites false
  have auth:=v.wide_funded_turn_inputs h width size M π raw bits horizon age budget small card who dur ord ci
    (fun i=>(cj i).val) out outLow
  have actualID:=v.wide_role_id_val h width bits out auth.2.2.1 oldFit source
  have ip : names idx=.inr (.inl good):=(names).apply_symm_apply _
  have address : ((v.wideRoleID h width bits).eval out (source.val:Word w)).val=skeys idx:=by
    change _ = (sparse (names idx)).val
    rw [actualID,key,ip,key_goods]
    rfl
  have origin (side : Bool) : phys (names idx,side)=
      publicRoleFor v.sampler π (activePaid v.sampler counts ports) (.inr (.inl good)) side:=by rw [ip];rfl
  have rr:=SectorRead.seen v.sampler π v.depth marks unique (P).catalogue order bsize axis
    oldRows (oldStart j) (leftOnly j) datedROM whole spent out seen oldRows ((b₀).oldSite false)
    ((b₀).oldRole false) (v.wideRoleID h width bits) (source.val:Word w) idx on false
    (by simpa only [origin] using rawSite.2.1) (by simpa only [origin] using rawSite.2.2) address
  have mx : ∀i,spent i≤cap:=by
    intro i
    simp only [Function.comp_apply]
    rcases names i with e|x|c <;> first | exact bounded _ | exact Nat.zero_le _
  have fit : prefixAt namedRows spent idx<2^w:=
    (DatedSpillOffsets.sector_prefix_le v.sampler π v.depth marks unique (P).catalogue order bsize axis spent idx cap mx).trans_lt word
  have rule:=old_prefix_on_goods v.sampler π v.depth marks (P).catalogue order bsize axis mount pad spill good
  exact ((congrArg Fin.val rr).trans (Fin.val_cast_of_lt fit)).trans rule

omit horizon age budget small operandAge card in
/-- Each visited paid native edge reads the entire spill-only mass of earlier
paid rows on its chord through its physically saved site and printed role. -/
theorem wide_spill_chart_newBase (out : Memory w) (whole : Fin segs→ℕ)
    (seen : fields (newStart j) (rightOnly j) datedROM whole received out)
    (bounded : ∀e,deposits e≤cap) (oldAmount : Fin oldRows→ℕ)
    (oldPort : ∀i,0<oldAmount i→Bool→Public v.sampler h v.W k v.wideJobs)
    (data : (b₀).LiveReads v.sampler oldAmount counts oldPort (fun i on t=>.inl (ports i on t)) out)
    (pad : Chord siteCount) (e : Fin rows) (positive : 0<deposits e) (paidNow : 0<counts e)
    (on : 0<whole ((names).symm (.inl (A₀.ident ⟨e,paidNow⟩)))) :
    ((panel).right.prefix.eval out (e.val:Word w)).val=datedBase (filledChord (mount).actual pad) deposits e := by
  let sold:=A₀.ident ⟨e,paidNow⟩
  let idx:=(names).symm (.inl sold)
  have found : ordinal sold=e:=(v.wide_dated_original_ordinal h width π marks sold).symm.trans (A₀.original ⟨e,paidNow⟩)
  have ip : names idx=.inl sold:=(names).apply_symm_apply _
  have origin (side : Bool) : phys (names idx,side)=.inl (ports e paidNow side):=by rw [ip];rfl
  have rawSite := (data.newSite e paidNow false).trans (ProtocolRAMTurnOperands.actual_word v.sampler true
    (fun t=>.inl (ports e paidNow t)) false true)
  have rawRole := (data.newRole e paidNow false).trans (ProtocolRAMTurnOperands.actual_word v.sampler true
    (fun t=>.inl (ports e paidNow t)) false false)
  have kd : skeys idx=e.val:=by
    change (sparse (names idx)).val=e.val
    rw [ip,key_paid,found]
  have address : (Expr.row.eval out (e.val:Word w)).val=skeys idx:=by
    have room:=seen.idSmall idx
    rw [kd] at room ⊢
    exact Fin.val_cast_of_lt room
  have rr:=SectorRead.seen v.sampler π v.depth marks unique (P).catalogue order bsize axis
    oldRows (newStart j) (rightOnly j) datedROM whole received out seen rows ((b₀).newSite false)
    ((b₀).newRole false) .row (e.val:Word w) idx on true
    (by simpa only [origin] using rawSite) (by simpa only [origin] using rawRole) address
  have mx : ∀i,received i≤cap:=by
    intro i
    simp only [Function.comp_apply]
    rcases names i with a|x|c <;> first | exact bounded _ | exact Nat.zero_le _
  have fit : prefixAt namedRows received idx<2^w:=
    (DatedSpillOffsets.sector_prefix_le v.sampler π v.depth marks unique (P).catalogue order bsize axis received idx cap mx).trans_lt word
  have rule:=new_prefix_on_paid v.sampler π v.depth marks (P).catalogue order bsize axis chk pad spill sold
    (by rwa [found])
  rw [found] at rule
  exact ((congrArg Fin.val rr).trans (Fin.val_cast_of_lt fit)).trans rule

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
