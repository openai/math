import OAI.Hierarchy.ProbeFixedWideSpillRankDates
import OAI.Hierarchy.ProbeFixedWideSpillChartBases
import OAI.Hierarchy.TaggedWideOriginalDateFields

namespace OAI
/-! # The original and corrected role receipts on the turn publisher's actual sector pages -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open WideCPU StripDirectory
open scoped Classical BigOperators Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
set_option quotPrecheck false
local notation "P" => v.widePlacement h width
local notation "boards₀" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger boards₀ v.mesh (P).catalogue (P).routes F A)
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
local notation "L" => ownerLedger boards₀ v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "C" => v.wideSignedChart h width stock
local notation "last" => (events v.mesh).length
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts boards₀ v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F boards₀ v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "bits" => v.maxBits
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "hi" => v.wideRoleStart h width stock ss
local notation "full" => v.wideFundedSize h width bits

local notation "K" => WideMemory.K h v.W
local notation "headerWidth" => WideMemory.H h v.W k v.wideJobs
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "pub" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K (directory).groups headerWidth R
local notation "coreTop" => CoreCatalogue.top h v.W K (directory).groups headerWidth R
local notation "coreHead" => CoreCatalogue.headBase h v.W K (directory).groups headerWidth

local notation "place" => siteNumber h D k
local notation "mount" => (P).catalogue.coreMount π place order chk
local notation "ord" => CoreRoute.enum mount o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i
local notation "lw" => v.wideWidthLayout h width ss
variable (horizon : v.wideFundedSize h width v.maxBits ≤ size) (age : v.wideFundedHeight≤h)
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
    (A₀ : WideFundedTurnAlignment v h width size M π raw v.maxBits issues who cj marks)

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
variable (ell unitCost first rom oldWork : ℕ)
section Names
variable (input : Fin (events v.mesh).length→Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "startAt" => v.wideSpillRankEnd h width bits first
local notation "correct" => v.wideSpillDates h width ell unitCost bits first
local notation "baseModel" => v.wideDated h width ell unitCost
local notation "target" => v.wideCorrectedWidths h width size M π raw bits issues first input
local notation "region" => v.wideSpillPage h width bits first
open DatedSpillOffsets
local notation "degs" => HistoryRoles.stride k v.sampler.degree v.wideJobs
local notation "Gds" => Goods h v.W k
local notation "Cts" => Catalysts h v.W k
local notation "Cat" => Catalogue v.sampler π v.depth marks
local notation "clip" => fun j : Fin last=>fun x : Gds=>
  RouteSettlement.actual (region j.val).overflow (input j) (PurchaseInventory.slot x)
local notation "orig" => fun j : Fin (last+1)=>(value j.val ∘ embedded ∘ names)
local notation "post" => fun j : Fin last=>orig j.succ
local notation "pre" => fun j : Fin last=>
  if (correct).attempt j then target 0 j.succ ∘ embedded ∘ names else orig j.castSucc
local notation "sparseBefore" => fun j : Fin last=>((Sum.elim (fun _:Cat=>0) (Sum.elim (clip j) (fun _:Cts=>0))) ∘ names)
local notation "sparseAfter" => fun j : Fin last=>
  ((Sum.elim (fun e:Cat=>routeLoad (mount).ordinary (clip j) (ordinal e)) (fun _:Gds⊕Cts=>0)) ∘ names)
local notation "ids" => fun i=>(sparse (names i)).val
local notation "cert" => SectorRead v.sampler π v.depth marks unique (P).catalogue order bsize axis oldRows

/-- Two genuine mounted sector views on every date, including the distinction
between an attempted repair and a direct feed on its old side. -/
theorem wide_spill_chart_sectors_at_roles (out : Memory w)
    (printed : ∀i,(v.wideCorrectedRoleFact h width size M π raw issues marks unique ell unitCost first rom input i).holds out)
    (fullRole : ∀j f,DatedRoleSheets.roleFact oldRows v.sampler π v.depth marks unique names
      ((baseModel).roleStart oldWork j) (orig j) ids out f)
    (strides : RoleROM.Mounted rom (fun i : Fin siteCount=>i.val*degs) out)
    (oldRoom : oldRows≤2^w) (namesFit : siteCount≤2^w) (roleFit : 2*degs≤2^w)
    (spanFit : siteCount*degs≤2^w) (cap : ℕ) (budget : 2*cap<2^w)
    (regularSize : ∀t i,(orig t) i≤cap) (oldSize : ∀j g₀,clip j g₀≤cap)
    (newSize : ∀j e,routeLoad (mount).ordinary (clip j) e≤cap) (j : Fin last) :
    cert ((correct).preClip oldWork startAt j) ((correct).dateRole startAt j 1) rom (pre j) (sparseBefore j) out ∧
    cert ((baseModel).roleStart oldWork j.succ) ((correct).dateRole startAt j 2) rom (post j) (sparseAfter j) out := by
  have atRole (f : Fin 3) (t : Fin (last+1)) (field : Fin 3) :
      DatedRoleSheets.roleFact oldRows v.sampler π v.depth marks unique names
        ((baseModel).roleStart ((correct).roleRoot startAt f) t) (target f t ∘ embedded ∘ names) ids out field := by
    have physical : ((correct).roles f).physical = oldRows := rfl
    have position : ∀addr,((correct).roles f).roleStart addr t = (baseModel).roleStart addr t := fun _ => rfl
    simpa only [wideCorrectedRoleFact,Equiv.symm_apply_apply,WideCPU.Dated.roleResult,physical,position] using
      printed (finProdFinEquiv (f,finProdFinEquiv (t,field)))
  have hcap : cap<2^w:=by omega
  have idRoom (i) : ids i<2^w:=by
    have smallID:=(sparse (names i)).isLt
    have eq:=v.wide_old_rows h width
    change _ < rows+(PurchaseInventory.footprint h N k+num) at smallID
    change (sparse (names i)).val < 2^w
    exact smallID.trans_le (eq ▸ oldRoom)
  have two : 1<2^w:=by
    apply lt_of_lt_of_le (by decide : 1<2^2) (Nat.pow_le_pow_right (by decide) ?_)
    unfold Native.wordBits
    omega
  have loEq : target 1 j.succ ∘ embedded ∘ names=sparseBefore j := by
    funext i
    cases e:names i with
    | inl c=>simp [Function.comp_def,wideCorrectedWidths,e,DatedRows.embed]
    | inr a=>cases a <;> simp [Function.comp_def,wideCorrectedWidths,e,DatedRows.embed]
  have hiEq : target 2 j.succ ∘ embedded ∘ names=sparseAfter j := by
    funext i
    cases e:names i with
    | inl c=>simp [Function.comp_def,wideCorrectedWidths,e,DatedRows.embed]
    | inr a=>cases a <;> simp [Function.comp_def,wideCorrectedWidths,e,DatedRows.embed]
  have leftPublished (f : Fin 3) := atRole 1 j.succ f
  have rightPublished (f : Fin 3) := atRole 2 j.succ f
  have leftSparse : ∀i,sparseBefore j i<2^w:=by
    intro i
    rcases e:names i with c|x|a <;>
      simp only [Function.comp_apply,e,Sum.elim_inl,Sum.elim_inr] <;> first | exact (oldSize j _).trans_lt hcap | omega
  have rightSparse : ∀i,sparseAfter j i<2^w:=by
    intro i
    rcases e:names i with c|x|a <;>
      simp only [Function.comp_apply,e,Sum.elim_inl,Sum.elim_inr] <;> first | exact (newSize j _).trans_lt hcap | omega
  have fullPre (f) : DatedRoleSheets.roleFact oldRows v.sampler π v.depth marks unique names
      ((correct).preClip oldWork startAt j) (pre j) ids out f := by
    by_cases yes:(correct).attempt j
    · simp only [WideCPU.SpillDates.preClip,ite_eq_left yes]
      exact atRole 0 j.succ f
    · simp only [WideCPU.SpillDates.preClip,ite_eq_right yes]
      exact fullRole j.castSucc f
  have preSmall (i) : pre j i<2^w:=by
    by_cases yes:(correct).attempt j
    · simp only [ite_eq_left yes,wideCorrectedWidths,Fin.cases_succ,Function.comp_apply]
      have past:=regularSize j.succ i
      rcases eqn:names i with c|x|a <;>
        simp only [Function.comp_apply,eqn,DatedRows.embed,Function.Embedding.coe_sumMap,
          Function.Embedding.coe_refl,id_eq,Sum.map_inl,Sum.map_inr,FeedTransfer.middleAmounts,
          Sum.elim_inl,Sum.elim_inr,ite_true,Fin.val_succ] at past ⊢
      · omega
      · have spillBound : RouteSettlement.actual (region j.val).overflow (input j)
            (PurchaseInventory.slot x) ≤ cap := oldSize j x
        omega
      · omega
    · simpa only [ite_eq_right yes] using (regularSize j.castSucc i).trans_lt hcap
  refine ⟨⟨fullPre,?_,strides,preSmall,leftSparse,idRoom,namesFit,roleFit,spanFit,two⟩,
    ⟨fullRole j.succ,?_,strides,fun i=>(regularSize j.succ i).trans_lt hcap,rightSparse,idRoom,namesFit,roleFit,spanFit,two⟩⟩
  · intro f
    rw [←loEq]
    exact leftPublished f
  · intro f
    rw [←hiEq]
    exact rightPublished f

theorem wide_spill_chart_sectors (before out : Memory w)
    (printed : v.correctedContents h width size M π raw issues marks unique ell unitCost first rom oldWork input before out)
    (fullRole : ∀j f,DatedRoleSheets.roleFact oldRows v.sampler π v.depth marks unique names
      ((baseModel).roleStart oldWork j) (orig j) ids out f)
    (strides : RoleROM.Mounted rom (fun i : Fin siteCount=>i.val*degs) out)
    (oldRoom : oldRows≤2^w) (namesFit : siteCount≤2^w) (roleFit : 2*degs≤2^w)
    (spanFit : siteCount*degs≤2^w) (cap : ℕ) (budget : 2*cap<2^w)
    (regularSize : ∀t i,(orig t) i≤cap) (oldSize : ∀j g₀,clip j g₀≤cap)
    (newSize : ∀j e,routeLoad (mount).ordinary (clip j) e≤cap) (j : Fin last) :
    cert ((correct).preClip oldWork startAt j) ((correct).dateRole startAt j 1) rom (pre j) (sparseBefore j) out ∧
    cert ((baseModel).roleStart oldWork j.succ) ((correct).dateRole startAt j 2) rom (post j) (sparseAfter j) out :=
  v.wide_spill_chart_sectors_at_roles h width size M π raw issues marks unique ell unitCost first rom oldWork
    input out printed.1 fullRole strides oldRoom namesFit roleFit spanFit cap budget regularSize oldSize newSize j

end Names
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
