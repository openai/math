import OAI.Hierarchy.ProbeFixedWideSpillOriginalWords
import OAI.Hierarchy.ProbeFixedWideSpillTurns
import OAI.Hierarchy.ProtocolRAMDateSpillRankRun
import OAI.Hierarchy.ProtocolRAMTurnAuthenticatedChart
import OAI.Hierarchy.ProtocolRAMPaidOriginalEndpoints
import OAI.Hierarchy.ProbeFixedWideSignedFits

namespace OAI
/-! # Every live native dated turn reads the original commodity, including those exhausted later -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option cleanup.letToHave false
set_option maxHeartbeats 2400000
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
local notation "last" => (events v.mesh).length

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

include horizon age budget small operandAge card


open DateSpill ProtocolRAMDateSpillRank ProtocolRAMTurnChart ProtocolRAMTurnSnapshot
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open CoreBoard.WordSeats
include marks unique A₀
variable (datedROM terminalROM work rankFirst turnFirst : ℕ)
variable (oldStart newStart leftOnly rightOnly : Fin (events v.mesh).length→ℕ) (j : Fin (events v.mesh).length)
local notation "panel" => v.wideSpillTurnPage h width bits datedROM terminalROM work rankFirst turnFirst
  oldStart newStart leftOnly rightOnly j
local notation "ranker" => v.wideSpillRanks h width bits rankFirst
local notation "rpage" => v.wideSpillPage h width bits rankFirst j.val
local notation "tr" => v.wideTerminalBoard h width bits work
local notation "stk" => v.wideTerminalStock h width bits
local notation "extent₀" => (tr).endAt+3*oldRows
local notation "slotRoom" => WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "RawOld" => ProtocolRAMTurnGeometry.Source rows h D k
local notation "decode" => (ProtocolRAMTurnGeometry.sourceOrder rows h D k).symm
local notation "encode" => ProtocolRAMTurnGeometry.sourceOrder rows h D k
local notation "chart" => captured (panel).data

/-- Re-read the dated native source mass and both directed role words on the
same memory. The active original terminal inventory can have width zero. -/
theorem wide_spill_turn_active (initial rankedInput output : Memory w)
    (initialLow : ∀x,x<full→initial x=settled x)
    (rankLow : ∀x,x<full→ rankedInput x=settled x)
    (frozen : ∀x,x<extent₀→ rankedInput x=(tr).extendedState stk initial x)
    (observed : RankTape.Observation ranker mount o j.val rankedInput output)
    (replayed : v.wideReplayedTurnBase h width ss≤work) (within : extent₀≤rankFirst)
    (native : rankFirst<2^w) (sites : siteLast h D k+1≤2^w)
    (pad : Chord (siteLast h D k+1)) (a : Fin oldRows)
    (live : 0<(chart output).width ((encode) ((decode) a)).val) :
    ∃item : Goods h v.W k,(decode) a=.inr (.inl item) ∧
      (panel).data.rawSource.read output (((encode) ((decode) a)).val:Word w)=
        (ProtocolRAMTurnEdges.visit mount (siteNumber h D k).injective pad ((decode) a) 0:Word w) ∧
      (chart output).sourceRole ((encode) ((decode) a)).val<2*slotRoom ∧
      (chart output).targetRole ((encode) ((decode) a)).val<2*slotRoom ∧
      (chart output).width ((encode) ((decode) a)).val=
        RouteSettlement.actual (rpage).overflow rankedInput (PurchaseInventory.slot item) := by
  have room:=within.trans_lt native
  have numeric : work+7*oldRows+4*rows<2^w:=by
    change work+4*oldRows+4*rows+3*oldRows<2^w at room
    clear * - room
    omega
  have sourceRoom : oldRows≤2^w:=by clear * - numeric; omega
  have wide : 2<2^w:=by
    apply lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) ?_)
    clear * - h v
    unfold Native.wordBits
    omega
  have oldPages:=v.wide_replayed_start h width ss
  have ready:=v.wide_signed_turn_ready_at h width stock ((lw).bank last) ss work (v.fixedTerminalStock_end P h width)
    (oldPages.1.trans replayed) (oldPages.2.trans replayed) numeric
  have highFit : (z).ceiling hi<2^w:=(oldPages.1.trans replayed).trans_lt (by clear * - numeric; omega)
  have boot:=v.wide_funded_turn_inputs h width size M π raw bits horizon age budget small
    (entries:=recordCount v.mesh issues) card who dur
    (I:=Commodity (Fin (2^h)) N k) (J:=Columns h D × Fin k)
    (core:=(mount).ordinary) (center:=(mount).centers) ord ci (fun i=>(cj i).val) rankedInput rankLow
  obtain ⟨intermediate,rank,low,amount⟩:=RankTape.Observation.read ranker mount o observed rfl
  have rb : rankFirst≤(rpage).rankStart:=by
    exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have saved (x) (before : x<extent₀) : output x=(tr).extendedState stk initial x :=
    (rank.frame x (before.trans_le (within.trans rb))).trans ((low x (before.trans_le within)).trans (frozen x before))
  have tag:=DatedRoleInput.decoded ((z).stop hi) rankedInput ((lw).bank last) stock (old).reserved (old).used
    boot.2.2.1 sourceRoom a
  have current : (rpage).amount.read output (a.val:Word w)=
      ((rpage).term (stk).kind (stk).index).eval rankedInput (a.val:Word w) := by
    have cap : oldRows≤(rpage).amount.size:=(rpage).amount_room
    change output ((rpage).amount.base+(a.val:Word w).val%(rpage).amount.size)=_
    rw [Fin.val_cast_of_lt (a.isLt.trans_le sourceRoom),Nat.mod_eq_of_lt (a.isLt.trans_le cap)]
    exact (rank.frame _ (Nat.add_lt_add_left (a.isLt.trans_le cap) _)).trans
      (amount a)
  change (stk).kind.eval rankedInput (a.val:Word w)=(DatedRoleInput.tag ((decode) a):Word w) ∧
      (stk).index.eval rankedInput (a.val:Word w)=(DatedRoleInput.localIndex ((decode) a):Word w) at tag
  let mass:=(rpage).amount.read output (a.val:Word w)
  have on : 0 < mass.val := by
    simpa only [mass, Equiv.apply_symm_apply, captured, TurnPage.data, wideSpillTurnPage] using live
  let src:=(decode) a
  obtain ⟨good,key⟩ : ∃item : Goods h v.W k,src=.inr (.inl item):=by
    rcases eqn:src with e|item|c
    · have kt : (stk).kind.eval rankedInput (a.val:Word w)=0:=
        tag.1.trans (congrArg (fun y=>((DatedRoleInput.tag y:ℕ):Word w)) eqn)
      have bad : mass=0:=by
        simpa [mass,Page.term,Expr.eval,kt,DescriptorExpr.Comparison.test,(DatedRoleInput.codes wide).1.symm] using current
      exact False.elim (on.ne' (congrArg Fin.val bad))
    · exact ⟨item,rfl⟩
    · have kt : (stk).kind.eval rankedInput (a.val:Word w)=(2:Word w):=by
        exact tag.1.trans (congrArg (fun y=>((DatedRoleInput.tag y:ℕ):Word w)) eqn)
      have bad : mass=0:=by
        simpa [mass,Page.term,Expr.eval,kt,DescriptorExpr.Comparison.test,(DatedRoleInput.codes wide).2.2] using current
      exact False.elim (on.ne' (congrArg Fin.val bad))
  have source:=v.wide_spill_original_goods h width size M π raw bits horizon age budget small operandAge
    issues card who cj marks unique A₀ work initial output initialLow highFit sourceRoom a (.inl good) key
    ready.1 ready.2 room saved sites
  let role:=publicRoleFor v.sampler π (activePaid v.sampler counts ports) (.inr (.inl good))
  have origin : (name (HistoryRoles.site v.sampler (role false))).val=
      ProtocolRAMTurnEdges.visit mount (siteNumber h D k).injective pad src 0 := by
    rw [key]
    change (name (HistoryRoles.goodsSite (HistoryRoles.goods π (good,false)))).val=
      (name (WordSeats.site π (commodityTurn good 0))).val
    rw [HistoryRoles.goods_site,commodity_start]
    rfl
  have bounded (side : Bool) : (((tr).oldRole side).read output (a.val:Word w)).val < 2*slotRoom := by
    rw [(source side).2.2]
    exact (Nat.mod_le _ _).trans_lt (ProtocolRAMTurnSnapshot.original_bound v.sampler role side)
  have amountEq : mass=(rpage).overflow.read rankedInput (PurchaseInventory.slot good:Word w):=by
    have k0 : (stk).kind.eval rankedInput (a.val:Word w)=(1:Word w):=tag.1.trans (congrArg
      (fun y=>((DatedRoleInput.tag y:ℕ):Word w)) key)
    have i0 : (stk).index.eval rankedInput (a.val:Word w)=(PurchaseInventory.slot good:Word w):=tag.2.trans
      (congrArg (fun y=>((DatedRoleInput.localIndex y:ℕ):Word w)) key)
    simpa [mass,Page.term,Expr.eval,k0,i0,DescriptorExpr.Comparison.test] using current
  simp only [Equiv.apply_symm_apply]
  exact ⟨good,key,(source false).1.trans (congrArg (fun n:ℕ=>(n:Word w)) origin),
    bounded false,bounded true,congrArg Fin.val amountEq⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
