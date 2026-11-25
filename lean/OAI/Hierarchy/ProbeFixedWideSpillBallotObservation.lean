import OAI.Hierarchy.ProbeFixedWideSpillRankDates

namespace OAI
/-! # The selected ballot table before reading the corresponding corrected control -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open WideCPU CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
open scoped Classical BigOperators Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option cleanup.letToHave false
local notation "P" => v.widePlacement h width
local notation "boards" => v.nativeBoards P h width
local notation "arena" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger boards v.mesh (P).catalogue (P).routes F arena)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "rows" => (P).catalogue.rows
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "C" => v.wideSignedChart h width stock
local notation "last" => (events v.mesh).length
local notation "siteCount" => siteLast h D k+1

variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
    (issues : Attempt→CatalystArchive.Entry (Fintype.card (Columns h (2^v.W))*k) width)
    (marks : Marks h v.W k v.wideJobs) (unique : Exclusive marks)
local notation "bits" => v.maxBits
local notation "mid" => v.wideSignedMidAt h width size stock M π (wideRouteOrder h D k)
  (v.wideFundedRaw h width bits raw)

variable (ell unitCost first rom oldWork : ℕ)
section Names
variable (input : Fin (events v.mesh).length→Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "startAt" => v.wideSpillRankEnd h width bits first
local notation "correct" => v.wideSpillDates h width ell unitCost bits first
local notation "baseModel" => v.wideDated h width ell unitCost
local notation "oldRows" => Fintype.card (Old h v.W k rows)
local notation "N" => Stages h D
local notation "order" => v.wideOrder h width
local notation "bsize" => v.wide_dated_bought_rows h width
local notation "axis" => pairKeys (Columns h D) k
local notation "names" => timeRows v.sampler π v.depth marks (P).catalogue order bsize axis
local notation "embedded" => DatedRows.embed v.sampler π v.depth marks (P).catalogue order bsize
local notation "sparse" => sparseKey v.sampler π v.depth marks (P).catalogue order bsize
  (PurchaseInventory.slotEquiv h N k) axis
local notation "target" => v.wideCorrectedWidths h width size M π raw bits issues first input
local notation "saved" => fun a=>v.wideBallotRows h width r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows) a (entryMemory C mid a)

local notation "rr" => v.wideCorrectedRoleFact h width size M π raw issues marks unique ell unitCost first rom input
variable (m : Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "rb" => fun processing : Memory w=>(∀a,a<startAt→processing a=m a) ∧ ∀i,(rr i).holds processing
local notation "br" => fun j=>v.wideSpillBallotFact h width ell unitCost bits first rom oldWork j saved rb
local notation "siteAt" j:arg => (baseModel).ballotStart ((correct).roleRoot startAt 2) j
local notation "packet" j:arg a:arg => v.widePacketFields h width (ProtocolRAMPurchaseSampler.bits (v.widePacketShelf h))
  (.attempt a) ((baseModel).siteROM rom) ((baseModel).siteStride rom) ((baseModel).roleStart oldWork (j).castSucc)
  ((correct).dateRole startAt j 0)
local notation "printed" j:arg a:arg srcMem:arg dstMem:arg => WideCPU.printedSiteRows (v.widePacketShape h width (.attempt a))
  (baseModel).sites (siteAt j) (packet j a) (saved a) srcMem dstMem

private theorem ballot_from_snapshot (j : Fin last) (a : Attempt)
    (onDate : (events v.mesh).get j = .attempt a) {before : Memory w} (atBallot : (br j).holds before) :
    ∃ source, (∀x,x < startAt → source x=m x) ∧ (∀i,(rr i).holds source) ∧ printed j a source before := by
  let fields := fun e => v.widePacketFields h width (ProtocolRAMPurchaseSampler.bits (v.widePacketShelf h))
    e ((baseModel).siteROM rom) ((baseModel).siteStride rom) ((baseModel).roleStart oldWork (j).castSucc)
    ((correct).dateRole startAt j 0)
  change (eventBallotFact (v.widePacketShape h width) (baseModel).sites ((baseModel).ballotROM rom j)
    (siteAt j) fields saved rb ((events v.mesh).get j)).holds before at atBallot
  rw [onDate] at atBallot
  obtain ⟨source,prior,native⟩ := atBallot
  exact ⟨source,prior.1,prior.2,native⟩

/-- Read the actual winning-row scatter on a true attempt in this execution. -/
theorem correctedContents.ballot {out : Memory w}
    (content : v.correctedContents h width size M π raw issues marks unique ell unitCost first rom oldWork input m out)
    (j : Fin last) (a : Attempt) (onDate : (events v.mesh).get j = .attempt a) :
    ∃ source, (∀x,x < startAt → source x=m x) ∧ (∀i,(rr i).holds source) ∧ printed j a source out :=
  ballot_from_snapshot (v:=v) (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw)
    (issues:=issues) (marks:=marks) (unique:=unique) (ell:=ell) (unitCost:=unitCost)
    (first:=first) (rom:=rom) (oldWork:=oldWork) (input:=input) (m:=m) j a onDate (content.2.1 j)

/-- The control values and its underlying ballot have one actual intermediate
memory. Both earlier snapshots agree with the ranked input below the replay start. -/
theorem correctedContents.control_ballot {out : Memory w}
    (content : v.correctedContents h width size M π raw issues marks unique ell unitCost first rom oldWork input m out)
    (side : Bool) (j : Fin last) (a : Attempt) (onDate : (events v.mesh).get j = .attempt a) :
    let fields:=v.wideCorrectedControlFields h width ell unitCost bits first rom oldWork startAt j side
    let base:=v.wideCorrectedControlStart h width ell unitCost bits first startAt j side
    ∃ before source, (∀x,x < startAt → before x=m x) ∧ (∀i,(rr i).holds before) ∧
      (∀x,x < startAt → source x=m x) ∧ (∀i,(rr i).holds source) ∧ printed j a source before ∧
      ∀partySite : Fin siteCount,∀c : Fin (SiteControls.fieldCount (HistoryRoles.stride k v.sampler.degree v.wideJobs)),
        out (base+1+(SiteScatter.pos partySite c).val)=(fields.value (0 : Fin 1) c).eval before (partySite.val:Word w) := by
  intro fields base
  obtain ⟨before,low,roles,ballots,control⟩ := correctedContents.control v h width size M π raw issues marks unique ell unitCost first rom oldWork input m content side j
  obtain ⟨source,frame,earlier,printedRows⟩ := ballot_from_snapshot
    (v:=v) (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw)
    (issues:=issues) (marks:=marks) (unique:=unique) (ell:=ell) (unitCost:=unitCost)
    (first:=first) (rom:=rom) (oldWork:=oldWork) (input:=input) (m:=m) j a onDate (ballots j)
  exact ⟨before,source,low,roles,frame,earlier,printedRows,control⟩

/-- The very ballot consumed by the dense control is still printed in the returned tape. -/
theorem correctedContents.returned_ballot {out : Memory w}
    (content : v.correctedContents h width size M π raw issues marks unique ell unitCost first rom oldWork input m out)
    (side : Bool) (j : Fin last) (a : Attempt) (onDate : (events v.mesh).get j = .attempt a) :
    let fields:=v.wideCorrectedControlFields h width ell unitCost bits first rom oldWork startAt j side
    let base:=v.wideCorrectedControlStart h width ell unitCost bits first startAt j side
    ∃ before source, (∀x,x < startAt → before x=m x) ∧ (∀i,(rr i).holds before) ∧
      (∀x,x < startAt → source x=m x) ∧ (∀i,(rr i).holds source) ∧ printed j a source before ∧
      (∀s : Fin siteCount,∀c : Fin (SiteControls.fieldCount (HistoryRoles.stride k v.sampler.degree v.wideJobs)),
        out (base+1+(SiteScatter.pos s c).val)=(fields.value (0 : Fin 1) c).eval before (s.val:Word w)) ∧
      printed j a source out := by
  intro fields base
  obtain ⟨before,low,roles,ballots,frame,words⟩:=correctedContents.control_prefix v h width size M π raw issues marks unique ell unitCost first rom oldWork input m content side j
  obtain ⟨src,lower,earlier,posted⟩:=ballot_from_snapshot
    (v:=v) (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw)
    (issues:=issues) (marks:=marks) (unique:=unique) (ell:=ell) (unitCost:=unitCost)
    (first:=first) (rom:=rom) (oldWork:=oldWork) (input:=input) (m:=m) j a onDate (ballots j)
  refine ⟨before,src,low,roles,lower,earlier,posted,words,?_⟩
  obtain ⟨ids,atSite,values⟩:=posted
  refine ⟨ids,atSite,fun site col=>(frame _ ?_).trans (values site col)⟩
  let root:= (correct).roleRoot startAt 2
  have lastBallot:=WideCPU.extent ((baseModel).rolesEnd root)
    (fun i=>((baseModel).ballot i).span (baseModel).sites) j
  change (baseModel).ballotStart root j+((baseModel).ballot j).span (baseModel).sites ≤
    (baseModel).controlStart root at lastBallot
  have columns : ((baseModel).ballot j).columns=(v.widePacketShape h width (.attempt a)).columns := by
    change (v.widePacketShape h width ((events v.mesh).get j)).columns=_
    rw [onDate]
  have orig:=WideCPU.extent ((baseModel).controlStart root) (fun i=>((baseModel).control i).span (baseModel).sites) j
  change (baseModel).controlBase root j+((baseModel).control j).span (baseModel).sites ≤
    (baseModel).maskStart root at orig
  have beginCtr : (baseModel).controlStart root ≤ (baseModel).controlBase root j := Nat.le_add_right ..
  have spill : (baseModel).maskStart root ≤ (correct).spillStart startAt j := Nat.le_add_right ..
  have cell : (SiteScatter.pos site col).val < (baseModel).sites*((baseModel).ballot j).columns := by
    rw [columns]
    exact (SiteScatter.pos site col).isLt
  simp only [WideCPU.Shape.span] at lastBallot
  have beforeControl : (baseModel).ballotStart root j+1+(SiteScatter.pos site col).val <
      (baseModel).controlStart root := by
    clear * - lastBallot cell
    omega
  cases side with
  | false => exact beforeControl.trans_le beginCtr
  | true => exact beforeControl.trans_le (beginCtr.trans ((Nat.le_add_right ..).trans (orig.trans spill)))

section
variable {v h width size M π raw issues marks unique ell unitCost first rom input}

/-- Split the physical correction sheet ordinal into sector, boundary and field. -/
theorem corrected_role_pages (processing : Memory w) (pages : ∀i,(rr i).holds processing)
    (sector : Fin 3) (boundary : Fin (last+1)) (field : Fin 3) :
    DatedRoleSheets.roleFact oldRows v.sampler π v.depth marks unique names
      ((baseModel).roleStart ((correct).roleRoot startAt sector) boundary)
      (target sector boundary ∘ embedded ∘ names) (fun i=>(sparse (names i)).val) processing field := by
  have phys : ((correct).roles sector).physical = oldRows := rfl
  have pos : ∀a,((correct).roles sector).roleStart a boundary = (baseModel).roleStart a boundary := fun _ => rfl
  simpa only [wideCorrectedRoleFact,Equiv.symm_apply_apply,WideCPU.Dated.roleResult, phys, pos] using
    pages (finProdFinEquiv (sector,finProdFinEquiv (boundary,field)))

end

end Names
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
