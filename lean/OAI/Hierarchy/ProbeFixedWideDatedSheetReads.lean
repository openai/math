import OAI.Hierarchy.ProbeFixedWideDatedAmounts
import OAI.Hierarchy.TaggedWideSourceAlignmentUnique
import OAI.Hierarchy.TaggedWireDatedResolved
import OAI.Hierarchy.TaggedWideDatedReads
import OAI.Hierarchy.ProbeFixedWideDated

namespace OAI
/-! # Native role sheet reads on the actual counted prefix tape -/

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

/-- Least input height beyond which the signed row populations of all checked
widths are supported by the archived purchase flags. -/
noncomputable def wideDatedSupportHeight : ℕ :=
  Nat.find (Filter.eventually_atTop.1 v.wide_history_supported)

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

include horizon age budget small operandAge card A₀
/-- Once a native field is positive only on the original paid catalogue, its
two sockets, raw ordinal and dense-to-sparse position use the actual archive.
Quantities on goods and catalysts can vary freely at this intermediate stage. -/
theorem wide_sheet_reads_of_counts (m : Memory w)
    (pages : v.WideDatedPages h width bits mid chk m issues)
    (keep : ∀x,x<full→m x=settled x) (highFit : (z).ceiling hi<2^w)
    (amount : Expr) (qty : Old h v.W k rows→ℕ)
    (read : ∀i:Fin oldRows,(amount.eval m (i.val:Word w)).val=qty (SettledMatrix.Layout.numbered i))
    (counted : ∀e,qty (.inl e)≤counts e) (ell unitCost rom : ℕ)
    (strides : ∀x : Fin siteCount,((v.wideDated h width ell unitCost).siteStride rom).read m (x.val:Word w)=
      ((x.val*HistoryRoles.stride k v.sampler.degree v.wideJobs:ℕ):Word w)) :
    DatedRoleSheets.Reads oldRows ((z).chart hi) ((tb).before) ((v.wideDated h width ell unitCost).siteStride rom)
      amount (v.wideRoleID h width bits) v.sampler π v.depth marks unique names m
      (qty ∘ embedded ∘ names) (fun i=>(sparse (names i)).val) partialRow direction := by
  have rootName (e : Fin rows) (pos : 0<counts e) : ordinal (A₀.ident ⟨e,pos⟩)=e :=
    (v.wide_dated_original_ordinal h width π marks _).symm.trans (A₀.original ⟨e,pos⟩)
  have vac (e : Fin rows) (missing : e∉Set.range ordinal) : qty (.inl e)=0 :=
    Nat.eq_zero_of_not_pos (fun pos=>missing ⟨_,rootName e (pos.trans_le (counted e))⟩)
  have opened (a : Catalogue v.sampler π v.depth marks) (on : 0<qty (.inl (ordinal a))) (t : Bool) :
      activePaid v.sampler counts ports (ordinal a) t=.inl (HistoryRoles.paid v.sampler π v.depth marks unique (a,t)) := by
    have pos:=on.trans_le (counted (ordinal a))
    have same : A₀.ident ⟨ordinal a,pos⟩=a:=(ordinal).injective (rootName (ordinal a) pos)
    rw [activePaid_pos v.sampler counts ports (ordinal a) pos]
    change Sum.inl (HistoryRoles.paid v.sampler π v.depth marks unique (A₀.ident ⟨ordinal a,pos⟩,t))=_
    rw [same]
  have chartRoom : (z).signedSites≤(z).ceiling hi:=by
    simp only [RoleRoom.Sizes.ceiling,RoleRoom.Sizes.stop,RoleRoom.Sizes.offset,RoleRoom.Sizes.positive,
      RoleRoom.Sizes.axis,RoleRoom.Sizes.ext,RoleRoom.Sizes.free,RoleRoom.Sizes.pub]
    omega
  have space : siteCount*(2*k)≤2^w:=chartRoom.trans highFit.le
  have positive : 1≤2*k:=by have hk:=v.positive;omega
  have sites : siteCount≤2^w:=
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left siteCount positive : _≤_).trans space
  have ids : (DatedRoleInput.number ∘ embedded ∘ names)=(fun i=>(sparse (names i)).val) := by
    funext i
    simpa only [Function.comp_apply,DatedRows.numbered_raw] using
      (DatedRoleInput.number_at v.sampler π v.depth marks (P).catalogue order bsize names i)
  rw [←ids]
  apply DatedRows.sheet_reads v.sampler π v.depth marks unique (P).catalogue order bsize names
      ((z).chart hi) ((tb).before) ((v.wideDated h width ell unitCost).siteStride rom)
      amount (v.wideRoleID h width bits) m (qty) DatedRoleInput.number
      (activePaid v.sampler counts ports)
  · exact read
  · exact v.wide_role_id_val h width bits m pages.metadata pages.physical
  · exact vac
  · exact opened
  · intro i on t
    apply v.wide_original_resolved h width size M π raw bits horizon age budget small operandAge issues card who cj
      marks unique A₀ m keep highFit pages.physical i _ t
    cases copy : SettledMatrix.Layout.numbered (I:=Goods h v.W k) («A»:=Catalysts h v.W k) («r»:=rows) i with
    | inl e=>exact (by simpa only [copy] using on : 0<qty (.inl e)).trans_le (counted e)
    | inr _=>trivial
  · exact sites
  · exact strides

omit operandAge card A₀ in
theorem wide_dated_paid_le (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w) (j : ℕ) :
    ∀e : Fin rows,value j (.inl e)≤counts e := by
  have capacity:=v.wide_signed_room h width stock (v.fixedTerminalStock_end P h width)
    ((le_max_left ..).trans age) budget
  intro e
  have prior:=PrefixWidths.prefix_total_le (events v.mesh) (v.wideEventSlices h width bits) chk j e
  rw [v.wideEventSlices_flat] at prior
  exact prior.trans ((v.wide_terminal_width_at h width size M π seed who dur cj ss
      (v.wide_funded_stock_at_size h width M π raw bits size horizon age budget small)
      (v.wide_funded_paid_at_size h width M π raw bits size horizon age budget small)
      capacity.1 cost baseline e).2)

/-- Every dated sheet reads its own numerical amount, unchanged original sparse
ordinal and both oriented public sockets from the same counted execution. -/
theorem wide_dated_sheet_reads (m : Memory w)
    (pages : v.WideDatedPages h width bits mid chk m issues)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (keep : ∀x,x<full→m x=settled x)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (highFit : (z).ceiling hi<2^w) (activeAge : v.wideDatedSupportHeight≤h) (nativeRadius : M=v.radius)
    (j : ℕ) (hj : j≤last) (ell unitCost rom : ℕ)
    (strides : ∀x : Fin siteCount,((v.wideDated h width ell unitCost).siteStride rom).read m (x.val:Word w)=
      ((x.val*HistoryRoles.stride k v.sampler.degree v.wideJobs:ℕ):Word w)) :
    DatedRoleSheets.Reads oldRows ((z).chart hi) ((tb).before) ((v.wideDated h width ell unitCost).siteStride rom)
      (v.wideRoleWidth h width bits j) (v.wideRoleID h width bits) v.sampler π v.depth marks unique names m
      (value j ∘ embedded ∘ names) (fun i=>(sparse (names i)).val) partialRow direction := by
  have extent:=(v.wide_funded_extent h width bits).trans horizon
  have support : v.WideHistorySupport h width chk bits := by
    subst M
    exact ((Nat.find_spec (Filter.eventually_atTop.1 v.wide_history_supported)) h activeAge width small budget
      size extent π seed bits).2
  exact v.wide_sheet_reads_of_counts h width size M π raw bits horizon age budget small operandAge issues card who cj
    marks unique A₀ m pages keep highFit (v.wideRoleWidth h width bits j) (value j)
    (v.wide_role_width_at h width bits mid chk m issues pages support j hj)
    (v.wide_dated_paid_le h width size M π raw bits horizon age budget small issues who cj baseline cost j)
    ell unitCost rom strides

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
