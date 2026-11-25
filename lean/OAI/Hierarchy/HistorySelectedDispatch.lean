import OAI.Hierarchy.HistorySelectedChildren
import OAI.Hierarchy.HistorySelectedLeafPacket
import OAI.ThreeFlat.Diagonal.HistorySelectedStageArm

namespace OAI
/-! # Dispatch each elected S44 ordinal to its actual original producer -/

namespace Hierarchy.HistorySelectedDispatch
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.TickWorkspace
open Diagonal.NavigationPass NativeNavigation Diagonal.HistoryContraction Diagonal.NavigationDirectory
open RAM RAM.NavigationNodeRows RAM.PhysicalProcedure RAM.HistoryNodeDirectory RAM.HistoryNodeDirectory.Selected
open RAM.HistoryStageBody.Physical HistoryStageSetup HistoryWordStepRun HistoryPartyBatchExec
open Hierarchy.HistorySelectedReceiverLoop
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {F Pins : Type} [Field F] [Fintype F] {u K heads heap fee levels degree : ℕ}
set_option quotPrecheck false
local notation "W" => 16*u^10
local notation "V" => volume u
local notation "peak" => (2^((3*u^10+4)/5):ℕ)
local notation "tag₀" => HistoryRefreshEmitter.tag (K:=F)
local notation "keep₀" => TickTerminalRoot.slotKeep u

/-- The stage inputs recovered before individual nodes are visited. These
facts mention only the two layers and their published navigation records. -/
def stageRows (B : Block F) (K heads heap fee levels : ℕ) (cur ctr : Word W)
    (b : Banks) (mid issued warm : Memory W) : Run.WordVisit F Pins :=
  fun {_ _ _ _} {X} R i L step O pay row=>
    RecordedWordStep K cur ctr heads heap mid Pins B.publicTemplate R i L step O pay row ∧
    warmDirectoryVisit b warm R i L step O pay row ∧ X.OrderedHalves L ∧
    State.HalfRows O (halfArchiveCell u) (numeric mid) ∧
    State.HalfRows row.sites (halfArchiveCell u) (numeric mid) ∧
    (∀v,2*archiveColumn b (numeric issued) (row.sites.id v) 1=step.words.ext v) ∧
    Nonempty (R.ResourceReceipt fee levels peak b (numeric issued) L step O pay row)

private def afterSeed (k : ℕ) : Run.WordVisit F Pins := fun _ _ _ _ _ _ row=>k≤row.sites.layer.first

omit [Fintype F] in
private theorem afterSeed_rows {d l : ℕ} {A : State d l} (r : Run F A) (k : ℕ) (h : r.plan.History)
    (J : Run.WordSteps Pins r) (L : A.Words Pins) (C : r.Charges) (O : A.ArchiveSites)
    (p : r.ArchivePath h C O) (beginning : k≤O.layer.first+O.layer.count) :
    r.WordVisits (afterSeed k) h J L C O p := by
  induction r with
  | done=>trivial
  | step R next ih=>
    have lo : k≤p.1.sites.layer.first:=by rw [p.1.row.contiguous];exact beginning
    exact ⟨lo,ih h.1 (Run.tailHistory R next h) (J.2 h.1) (J.1 L h.1).words (C.2 h.1)
      p.1.sites p.2 (lo.trans (Nat.le_add_right ..))⟩

variable {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (seed : A.Words Pins) (trees : Forest F seed.ports.form) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O) (zero : O.layer.first=0)
    (pointer : (Σ v:A.Site,Fin (seed.ext v))→ℕ)
local notation "lastRow" => (r.finalArchive h C O p).1
local notation "total" => (lastRow).first+(lastRow).count
local notation "node" => r.archiveNode h J seed trees C O p zero
local notation "values" => (fun j : Fin total=>NodeValue.ofSite (node j) pointer
  (streamAt u O.layer.count j.val) (endsAt u O.layer.count j.val))
variable (B : Block F) (cur ctr : Word (16*u^10)) (b : Banks)
    (mid issued warm : Memory (16*u^10)) (xs : List NodeRow)
    (D : HistoryNodeDirectory.Selected.Directory (16*u^10)
      ((r.finalArchive h C O p).1.first+(r.finalArchive h C O p).1.count))
    (shape : TraceBucketAtom.Layout) (rom : TraceRawLookup.Layout) (rest : Fin 1→Word (16*u^10))
local notation "shelf" => archive B (base u 38) W K
local notation "fs" => families B (base u 38) W
local notation "decoder" => TraceRawLookup.virtual W rom (TraceBucketAtom.publicProgram W)
local notation "leaf" => HistorySelectedSeed.procedure (HistoryStageBody.Physical.initial u shape) decoder
  (TraceBucketAtom.publicData shape rest)
local notation "arm" => (fun j : Fin total=>B.nativeArmTime levels fee b (numeric issued) j.val)
local notation "test" => stageRows (Pins:=Pins) B K heads heap fee levels cur ctr b mid issued warm

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3200000 in
/-- The directory, forest, and all earlier child IDs come from one selected
history. The leaf side consumes original control and operand words; the
stage side constructs the real Source, including its child's elected cache. -/
theorem visits (stored : r.ArchiveRowsStored b (numeric issued) h C O p)
    (rootCode : ℕ→Word W) (roots : ∀j,D.root j=rootCode
      ((r.archiveDirectory h C O p b (numeric issued) stored zero (lastRow).first (lastRow).count rfl rfl).root j))
    (recorded : r.WordVisits test h J seed C O p) (mount : WarmSources u b xs mid issued warm)
    (priced : ∀j : Fin total,Run.PricedAt b (numeric issued) fee levels peak j.val (node j))
    (original : ∀ (x : A.Site) (j : Fin total) (prev : Memory W),j.val=O.id x →
      node j=Run.nodeOfSite seed trees (fun v k=>(⟨v,k⟩ : Σ z : A.Site, Fin (seed.ext z))) x →
      Ledger u D tag₀ values keep₀ warm j.val prev→picked D j.val=true→
      Nonempty (HistorySelectedSeed.Operands shape rom rest tag₀ (bump (ownerData W u) prev)
        values j b (numeric issued) u O.layer.count))
    (allowance : B.archiveUnit u B.localCoefficient degree≤b.unitWork)
    (coefficient : (W+1)^3≤fee) (margin : 10*(levels+2)^2*fee≤b.unitWork)
    (unit : 0<b.unitWork) (age : 40≤u) (fixed : B.archiveConstant B.localCoefficient≤u)
    (square : total≤V^2) (nodes : b.nodes=base u 44) (cash : b.charges=base u 43)
    (headsAbove : base u 20≤heads) (heapBelow : heap≤base u 40)
    (table : Mounted B W W (base u 38) warm) (tableSize : base u 38+libraryWords B W<2^W)
    (stridePos : 0<K) (strideFit : K<2^W) (counters : cur.val<ctr.val)
    (fits : total≤2^W) (controlRoom : base u 18<2^W) (headerRoom : base u 13+8*total≤base u 14)
    (streamRoom : ∀j,(values j).stream+4*(values j).net.cells≤base u 14)
    (extRoom : ∀j,(values j).ext+(values j).external≤base u 14) :
    ∀ (j : Fin total) prev,Ledger u D tag₀ values keep₀ warm j.val prev→picked D j.val=true→
      Emitted (u:=u) shelf leaf fs D values tag₀ (B.nativeVisitCost levels fee b (numeric issued))
        arm (fun j _=>arm j) j (bump (ownerData W u) prev) := by
  let chron:=r.archiveDirectory h C O p b (numeric issued) stored zero (lastRow).first (lastRow).count rfl rfl
  have parentAt:=HistorySelectedChildren.archive_parentAt r h C O p b issued stored zero
    (lastRow).first (lastRow).count rfl rfl
  have parents:=HistorySelectedChildren.parentVisits r h J seed C O p b (numeric issued) stored
  have origin:=afterSeed_rows r O.layer.count h J seed C O p (Nat.le_add_left ..)
  have both:=r.wordVisits_pair _ _ h J seed C O p parents origin
  have allRows:=r.wordVisits_pair test _ h J seed C O p recorded both
  intro j prev reached chosen
  have source := Run.archived_source _ seed trees O r h J C p zero allRows j
  generalize rank : j.val=idx at source
  generalize tree : node j=actual at source
  cases source with
  | «leaf» x=>
    obtain ⟨s⟩:=original x j prev rank tree reached chosen
    exact s.emitted B shelf D (base u 38) W levels fee
      ((by positivity : 0<(W+1)^3).trans_le coefficient)
  | @stage a l' c k X R i L step old charge row observed forest orig v prior=>
    obtain ⟨⟨visit,dir,order,preHalf,postHalf,pairs,⟨bill⟩⟩,parent,after⟩:=observed
    let idx₀:=row.sites.id v
    have numbered : values j=NodeValue.ofSite
        (Run.nodeOfSite step.words (step.nextForest forest) (Run.pushedOrigin step orig) v)
        pointer (streamAt u O.layer.count idx₀) (endsAt u O.layer.count idx₀) := by
      change NodeValue.ofSite (node j) pointer _ _=_
      rw [tree,rank]
    have children:=HistorySelectedChildren.exact_children chron D rootCode roots tag₀ values
      R i L step old charge row v b issued parentAt parent j rank reached chosen fits controlRoom
      headerRoom streamRoom extRoom forest orig pointer O.layer.count (by
        intro k
        obtain ⟨ok,e⟩:=prior k
        exact ⟨ok,congrArg (fun a=>NodeValue.ofSite a pointer _ _) e⟩)
    have price:=priced j
    rw [tree,rank] at price
    let s : Run.StageOccurrence.Source (K:=K) (heads:=heads) (heap:=heap) (levels:=levels) (fee:=fee)
        (degree:=degree) (cur:=cur) (ctr:=ctr) (xs:=xs) (D₀:=D) (j:=j) (vals:=values)
        (b:=b) (mid:=mid) (out:=issued) (warm:=warm) (prev:=prev) (step:=step) (row:=row)
        B O.layer.count forest orig pointer v shape (fun i=>warm (base u 38+i.val)) := {
      visit:=visit, warmData:=mount,current:=reached,dir:=dir,priorOrder:=order,
      predecessor:=preHalf,successor:=postHalf,pairs:=pairs v,prior:=children,charges:=bill,
      priced:=price,allowance:=allowance,coefficient:=coefficient,margin:=margin,unit:=unit,
      age:=age,fixed:=fixed,index:=rank,numbered:=numbered,later:=after.trans (Nat.le_add_right ..),
      fits:=rank ▸ j.isLt.trans_le square,nodes:=nodes,cash:=cash,headsAbove:=headsAbove,heapBelow:=heapBelow,
      table:=table,tableSize:=tableSize,stridePos:=stridePos,strideFit:=strideFit,counters:=counters }
    exact Run.StageOccurrence.emitReceiver B O.layer.count forest orig pointer v s leaf

end
end Hierarchy.HistorySelectedDispatch

end OAI
