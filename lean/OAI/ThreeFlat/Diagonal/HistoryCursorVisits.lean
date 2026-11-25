import OAI.ThreeFlat.Diagonal.HistoryMotifTariffRefreshExecution
import OAI.ThreeFlat.Diagonal.PhysicalVisitRates
import OAI.ThreeFlat.Diagonal.PhysicalEndLevel
import OAI.ThreeFlat.Diagonal.TraceSeedEntryFrame
import OAI.ThreeFlat.Diagonal.PhysicalTypedAdmission
import OAI.ThreeFlat.Diagonal.NavigationDescendantWork
import OAI.ThreeFlat.Diagonal.PhysicalSelectedWork
import OAI.ThreeFlat.RAM.HistoryWordStepRun
import OAI.ThreeFlat.Diagonal.NativeNavigationAdmission
import OAI.ThreeFlat.RAM.NativeVisitFrame
import OAI.ThreeFlat.RAM.HistorySelectedFrame
import OAI.ThreeFlat.RAM.HistoryStageResources
import OAI.ThreeFlat.RAM.HistorySelectedFamily
import OAI.ThreeFlat.RAM.TickLedgerTerminal

namespace OAI
set_option quotPrecheck false

/-! # Selected S44 nodes of the accepted chronological navigation branch -/
namespace ThreeFlat.Diagonal.PhysicalStage.Run

open Computability.VPVNP.BurstRAM RAM HistoryContraction NavigationPass
open scoped Classical BigOperators
noncomputable section

variable {F Pins : Type} [Field F] {W d l : ℕ} {A : State d l}
variable (native : WordVisit F Pins) (seed : A.Words Pins) (trees : Forest F seed.ports.form) (first : A.ArchiveSites)
local notation "E" => (Σ a:A.Site,Fin (seed.ext a))

/-- Each assembled source row retains its producing visit on the very same
word assembler, with the earlier S44 IDs of all the input sites. -/
inductive SourceAt (lookup : ℕ→SelectedNode F Pins E→Prop) : ℕ→SelectedNode F Pins E→Prop
  | leaf (v : A.Site) :
    SourceAt lookup (first.id v) (nodeOfSite seed trees (fun a j=>⟨a,j⟩) v)
  | stage {a b c e : ℕ} {X : State a b} (R : Move F X c e) (i : Fin R.rules.count)
      (L : X.Words Pins) (step : R.WordStep Pins L i) (O : X.ArchiveSites)
      (charge : (R.next i).Site→ℕ) (row : R.ArchiveStep i O charge)
      (receipt : native R i L step O charge row)
      (N : Forest F L.ports.form) (orig : ∀u,Fin (L.ext u)→E) (v : (R.next i).Site)
      (prior : ∀ j,lookup (row.data.child (row.sites.ord v) j)
        (nodeOfSite L N orig (row.row.children v j).val)) :
    SourceAt lookup (row.sites.id v) (nodeOfSite step.words (step.nextForest N) (pushedOrigin step orig) v)

local notation "rel" => SourceAt native seed trees first

private theorem sourceAt_from {a b : ℕ} {X : State a b} (r : Run F X)
    (h : r.plan.History) (J : WordSteps Pins r) (L : X.Words Pins) (N : Forest F L.ports.form)
    (C : r.Charges) (O : X.ArchiveSites) (path : r.ArchivePath h C O)
    (orig : ∀u,Fin (L.ext u)→E) (lookup : ℕ→SelectedNode F Pins E→Prop)
    (entry : ∀v,rel lookup (O.id v) (nodeOfSite L N orig v))
    (table : ∀ j lo hi,lookup j (r.selectedAt h J L N C O path orig j lo hi))
    (receipts : r.WordVisits native h J L C O path)
    (j : ℕ) (lo hi) : rel lookup j (r.selectedAt h J L N C O path orig j lo hi) := by
  induction r generalizing j with
  | done X=>
    let v:=O.ord.symm ⟨j-O.layer.first,by change j<O.layer.first+O.layer.count at hi;omega⟩
    have num : O.id v=j:=by simp only [State.ArchiveSites.id,v,Equiv.apply_symm_apply];omega
    have atV:=entry v
    rw [num] at atV
    exact atV
  | step R next ih=>
    by_cases old : j<O.layer.first+O.layer.count
    · let v:=O.ord.symm ⟨j-O.layer.first,by omega⟩
      have num : O.id v=j:=by simp only [State.ArchiveSites.id,v,Equiv.apply_symm_apply];omega
      rw [selectedAt,dite_eq_left old]
      have atV := entry v
      rw [num] at atV
      exact atV
    · have after : path.1.sites.layer.first≤j:=by rw [path.1.row.contiguous];omega
      rw [selectedLater R next h J L N C O path orig j lo hi after]
      apply ih h.1 (tailHistory R next h) (J.2 h.1) (J.1 L h.1).words
        ((J.1 L h.1).nextForest N) (C.2 h.1) path.1.sites path.2
        (pushedOrigin (J.1 L h.1) orig) ?_ ?_ receipts.2
      · intro v
        apply SourceAt.stage R h.1 L (J.1 L h.1) O (C.1 h.1) path.1 receipts.1 N orig v
        intro k
        have id:=path.1.row.childId v k
        have lower : O.layer.first≤path.1.data.child (path.1.sites.ord v) k:=by
          rw [id];exact Nat.le_add_right ..
        have upper : path.1.data.child (path.1.sites.ord v) k<
            ((Run.step R next).finalArchive h C O path).1.first+
            ((Run.step R next).finalArchive h C O path).1.count:=by
          apply Nat.lt_of_lt_of_le _ ((Run.step R next).archive_bounds h C O path).2
          rw [id];exact Nat.add_lt_add_left (O.ord _).isLt _
        have stored:=table _ lower upper
        rwa [selectedChild L N O R next h J C path orig v k] at stored
      · intro k lk hk
        have low : O.layer.first≤k:=by rw [path.1.row.contiguous] at lk;omega
        have stored:=table k low hk
        rwa [selectedLater R next h J L N C O path orig k low hk lk] at stored

/-- Inspecting an actual global S44 row produces its concrete seed or receipt.
Every predecessor of a returned stage is identified in the original global lookup,
including when the inspected row is several stages after the seed. -/
theorem archived_source (r : Run F A) (h : r.plan.History) (J : WordSteps Pins r)
    (C : r.Charges) (path : r.ArchivePath h C first) (zero : first.layer.first=0)
    (receipts : r.WordVisits native h J seed C first path)
    (i : Fin ((r.finalArchive h C first path).1.first+(r.finalArchive h C first path).1.count)) :
    rel (fun j z => ∃ bound, r.archiveNode h J seed trees C first path zero ⟨j,bound⟩=z)
      i.val (r.archiveNode h J seed trees C first path zero i) := by
  apply sourceAt_from
  · exact fun v=>SourceAt.leaf v
  · intro j lo hi;exact ⟨hi,rfl⟩
  · exact receipts

end
end ThreeFlat.Diagonal.PhysicalStage.Run

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PrivateRAM HistoryNodeDirectory HistoryNodeDirectory.Selected PhysicalProcedure
open Diagonal.TickWorkspace
open scoped BigOperators Fin.CommRing
noncomputable section
set_option Elab.async false
variable {F : Type} {u n : ℕ}
variable (A : Archive) (B : TraceBucketAtom.Layout)
  (pub : Fin TraceEndpointROM.params→Word (16*u^10)) (fs : List Family)
  (D : Directory (16*u^10) n) (v : Fin n→NodeValue F) (tag : ((Fin 3→Bool)→F)→ℕ)
  (input : Memory (16*u^10)) (cost : ℕ→ℕ) (seedCost : Fin n→ℕ) (stageCost : Fin n→Family→ℕ)

/-- The branch chosen by the physical S44 selector executes its genuine
leaf or assembled stage program from the post-increment state. -/
inductive ChosenRun {u n : ℕ} (A : Archive) (B : TraceBucketAtom.Layout)
    (pub : Fin TraceEndpointROM.params → Word (16*u^10)) (fs : List Family)
    (seedCost : Fin n → ℕ) (stageCost : Fin n → Family → ℕ)
    (j : Fin n) (entry out : Memory (16*u^10)) : Prop where
  | seed (which : fs.find? (matchesFamily u entry)=none)
      (run : (HistoryInitialSeed.procedure (16*u^10) (initial u B) pub).Exec entry out (seedCost j)) :
      ChosenRun A B pub fs seedCost stageCost j entry out
  | stage (f : Family) (which : fs.find? (matchesFamily u entry)=some f)
      (run : (HistoryStageBody.procedure (layout u A f) f.childBound (16*u^10)).Exec entry out (stageCost j f)) :
      ChosenRun A B pub fs seedCost stageCost j entry out


/-- Conditions remaining per selected row after the real physical stage/seed
and its branch guard have been identified. All mutable stage outputs are tied
to one final memory image. -/
structure CacheWrite (j : Fin n) (entry : Memory (16*u^10)) : Prop where
  headerFits : nodeAddress u entry+5<2^(16*u^10)
  stageFits : ∀ f∈fs,(entry (nodeAddress u entry)).val=kind f.mode →
    stageAddress u entry+48<2^(16*u^10) ∧ f.oldPorts<2^(16*u^10)
  priced : bodyCost u entry (seedCost j) (stageCost j) fs≤cost j.val
  result : ∃ out,ChosenRun A B pub fs seedCost stageCost j entry out ∧ (v j).Cached tag u j.val out ∧
    ∀ addr,OutsideNode u j.val addr→ out addr=entry addr

/-- An accepted S44 family publishes the selected node in the very memory
returned by its native stage procedure. -/
theorem CacheWrite.of_stage (j : Fin n) (entry out : Memory (16*u^10)) (f : Family)
    (header : nodeAddress u entry+5<2^(16*u^10))
    (stages : ∀ g∈fs,(entry (nodeAddress u entry)).val=kind g.mode →
      stageAddress u entry+48<2^(16*u^10) ∧ g.oldPorts<2^(16*u^10))
    (priced : bodyCost u entry (seedCost j) (stageCost j) fs≤cost j.val)
    (guard : fs.find? (matchesFamily u entry)=some f)
    (writes : (HistoryStageBody.procedure (layout u A f) f.childBound (16*u^10)).Exec entry out (stageCost j f) ∧
      (v j).Cached tag u j.val out ∧ ∀ addr,OutsideNode u j.val addr→ out addr=entry addr) :
    CacheWrite A B pub fs v tag cost seedCost stageCost j entry :=
  ⟨header,stages,priced,out,.stage f guard writes.1,writes.2⟩

/-- Charge the native guards and the selected join to the fixed block on the
actual issued tree. The kernel time stays visible for the local motif tariff. -/
theorem CacheWrite.stage_price [Field F] [Fintype F] (grid : Diagonal.PhysicalStage.Block F)
    (start height : ℕ) (entry : Memory (16*u^10)) (f : Family) (seed : ℕ) (arm : Family→ℕ)
    (member : f∈families grid start height)
    (guard : (families grid start height).find? (matchesFamily u entry)=some f)
    {pins : ℕ} (tree : Diagonal.HistoryContraction.Tree F pins) (kernel : ℕ)
    (paid : arm f≤kernel+(6*StageRun.rootRate (layout u A f) f.childBound)*tree.resources) :
    bodyCost u entry seed arm (families grid start height)≤kernel+grid.stageClockRate*tree.resources := by
  have node := tree.nodes_pos
  have alive : 1≤tree.resources := by
    dsimp only [Diagonal.HistoryContraction.Tree.resources,Diagonal.HistoryContraction.Stage.treeWork]
    omega
  have fixed:=block_root_rate grid start height u A f member
  have roots:=Nat.mul_le_mul_right tree.resources (Nat.mul_le_mul_left 6 fixed)
  have guards:=Nat.mul_le_mul_left (blockGuardFee grid) alive
  have choice:=selection_cost grid start height u entry seed arm
  rw [guard] at choice
  change bodyCost u entry seed arm (families grid start height)≤blockGuardFee grid+arm f at choice
  unfold Diagonal.PhysicalStage.Block.stageClockRate
  simp only [Nat.add_mul,Nat.mul_one] at guards ⊢
  omega

/-- Assemble the actual visited node effects and arithmetic ownership frame
into the postorder visitor. Previous cache data are obtained from the single
address interval of each earlier node. -/
theorem visits_of_cursor {cap : ℕ}
    (ctrl : VisitFrame u input D v (TickTerminalRoot.slotKeep u) cost cap)
    (age : 16≤u) (wordSpace : base u 46<2^(16*u^10)) (len : n ≤ stride u)
    (owners : ∀ j,2*(D.root j).val+2 ≤ stride u/4)
    (nodeSpace : ∀ j : Fin n,base u 12+(j.val+1)*(volume u)^2≤base u 13 ∧
      base u 13+8*j.val+8≤base u 14)
    (prior : ∀ j : Fin n,picked D j.val=true→
      (v j).stream+4*(v j).net.cells≤base u 12+(j.val+1)*(volume u)^2 ∧
      (v j).ext+(v j).external≤base u 12+(j.val+1)*(volume u)^2)
    (visits : ∀ (j : Fin n) (m : Memory (16*u^10)),Ledger u D tag v (TickTerminalRoot.slotKeep u) input j.val m → picked D j.val=true →
      CacheWrite A B pub fs v tag cost seedCost stageCost j (bump (ownerData (16*u^10) u) m)) :
    NativeVisits u A B pub fs input D v tag (TickTerminalRoot.slotKeep u) cost cap seedCost stageCost := by
  refine ⟨ctrl,?_,?_⟩
  · intro j m ledger pick
    have verified:=visits j m ledger pick
    exact ⟨verified.headerFits,verified.stageFits,verified.priced⟩
  intro j m ledger pick
  obtain ⟨out,cachedRun,cached,frame⟩:=(visits j m ledger pick).result
  have budget:=nodeSpace j
  have strideBig : 4 ≤ stride u := by
    have e : 2≤u^10:=(by omega : 2≤u).trans (Nat.le_self_pow (by decide) _)
    have vbig : 4≤volume u:=Nat.pow_le_pow_right (by decide:0<(2:ℕ)) e
    exact vbig.trans (Nat.le_self_pow (by decide : 4≠0) _)
  have limit : base u 19<2^(16*u^10):=by
    have x:=apart (u:=u) (by decide : 19<46);omega
  have ownerFrame:=Ledger.owner_words (u:=u) (i:=j.val) D wordSpace strideBig len owners budget.1 budget.2
  have keepFrame (x : ℕ) (hx : (TickTerminalRoot.slotKeep u) x) : OutsideNode u j.val x ∧ x≠base u 18:=by
    refine ⟨TickTerminalRoot.slotKeep.outside budget.1 budget.2 hx,?_⟩
    rcases hx with low|high
    · have:=apart (u:=u) (by decide : 12<18);omega
    · have:=apart (u:=u) (by decide : 18<19);omega
  have next:=Ledger.emitted u j.val tag ledger j.isLt ctrl.room limit budget.1 budget.2 ownerFrame keepFrame
    (fun k _ pickedK=>prior k pickedK) frame cached
  have rawFrame {a : ℕ} (ok : OutsideNode u j.val a) (neq : a≠base u 18) : out a=m a:=by
    have hr : ((ownerData (16*u^10) u) 0).val=base u 18:=Fin.val_cast_of_lt ctrl.ctrlRoom
    rw [frame a ok]
    simp [bump,writeMemory,hr,neq]
  refine ⟨out,?_,?_,next.cursor,next.stop,next.directory,?_,?_,cached⟩
  · intro f found
    cases cachedRun with
    | seed miss run=>rw [miss] at found;contradiction
    | stage g hit run=>rw [hit] at found;cases found;exact run
  · intro miss
    cases cachedRun with
    | seed _ run=>exact run
    | stage _ hit _=>rw [hit] at miss;contradiction
  · intro a keep;exact rawFrame (keepFrame a keep).1 (keepFrame a keep).2
  · intro k old selected a used
    have h:=(v k).earlier_outside u j.val old budget.1 budget.2 (prior k selected).1 (prior k selected).2 used
    apply rawFrame h.1
    have:=h.2
    have:=apart (u:=u) (by decide : 14<18)
    omega

end
end ThreeFlat.RAM.HistoryStageBody.Physical

namespace ThreeFlat.RAM.HistoryWordStepRun
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.HistoryContraction Diagonal.PhysicalStage Diagonal.TickWorkspace
open HistoryStageRoot HistoryStageBody HistoryStageSetup HistoryStageSnapshots
open HistoryPartyBatchExec HistoryStageBody.Physical HistoryStageBankArena HistoryBoundedBody
open HistoryStageShapeWires NavigationNodeRows
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F Pins E : Type} [Field F] {d l D lanes W : ℕ} {S : State d l} {R : Move F S D lanes}
  {branch : Fin R.rules.count} (L : S.Words Pins) (step : R.WordStep Pins L branch)
  {old : S.ArchiveSites} {charge : (R.next branch).Site→ℕ} (record : R.ArchiveStep branch old charge)
  (v : (R.next branch).Site) (u seedCount : ℕ) (bank : Archive) (family : Family) (m : Memory W)
  (trees : Forest F L.ports.form) (orig : ∀ x,Fin (L.ext x)→E) (pointer : E→ℕ) (tag : ((Fin 3→Bool)→F)→ℕ)
local notation "A" => Physical.layout u bank family
local notation "C" => family.childBound
local notation "V" => volume u
local notation "T" => numInput A C (numeric m)
local notation "X" => HistoryStageSetup.run A C m
local notation "B" => (X).compiled
local notation "z" => Move.WordStep.targetSite (R:=R) (i:=branch) v
local notation "D₀" => step.stage
local notation "N" => fun k=>((D₀).tapeFactor trees z k).compile
local notation "ar" => (D₀).tapeArity trees z
local notation "wire" => (D₀).tapePin trees z
local notation "q" => Typed.copy T (numeric m) N wire
local notation "ops" => Tape.tape (W:=W) N wire tag q
local notation "produced" => adjust A C T .result ((B).output ops)
local notation "Y" => childCount T (numeric m)
local notation "idx" => record.sites.id v
local notation "target" => NodeValue.ofSite (Run.nodeOfSite step.words (step.nextForest trees)
  (Run.pushedOrigin step orig) v) pointer (T).stream (T).ext

/-- The native kernel and the join publish the exact current chronological
node at its postorder arena addresses. Each address outside the new node is
read unchanged by the next iteration, including the loop cursor. -/
theorem visit_cache_priced {K hEnd eEnd : ℕ} {cur ctr : Word W} {issuedMemory : Memory W} {allow : StaticMotif F→Prop}
    (visit : Diagonal.NavigationPass.RecordedWordStep K cur ctr hEnd eEnd issuedMemory Pins allow
      R branch L step old charge record) (order : step.ChildOrder record)
    (g : Ranges u idx bank family m N q) (head : (X).Header)
    (cells : SourceCells A C T (numeric m) W) (inputs : ∀ j,(T).words j<2^W)
    (b : Banks) (directory : DirectoryRow b record.sites.layer (record.sites.ord v) m)
    (source : record.data.Reads (numeric m)) (nodes : b.nodes=base u 44)
    (countRoom : record.sites.layer.childCount<2^W)
    (listRoom : record.sites.layer.children+(record.sites.ord v).val*record.sites.layer.childCount<2^W)
    (ports : HistoryStageRoot.Ports L.ports ((R.target_eq branch).symm ▸ step.words.ports)
      (D₀).count (D₀).child z T (numeric m))
    (childSize : ∀ k : Fin record.sites.layer.childCount,L.ext (record.row.children v k).val≤V)
    (child : ∀ k : Fin record.sites.layer.childCount,let id:=record.data.child (record.sites.ord v) k
      (NodeValue.ofSite (Run.nodeOfSite L trees orig (record.row.children v k).val) pointer
        (streamAt u seedCount id) (endsAt u seedCount id)).Cached tag u id m)
    (rootPins : (atResult (numeric m) (T).kernel).pins=(D₀).rootWidth z)
    (rootRows : (atResult (numeric m) (T).kernel).rows=((D₀).root z).compile.cells)
    (rootBits : (atResult (numeric m) (T).kernel).bits=((D₀).root z).compile.internal)
    (kernel : HistoryCompiledRows.Records tag ((D₀).root z).compile (atResult (numeric m) (T).kernel).stream m)
    (earlier : ∀ k,k<Y→numeric m (numeric m (HistoryStageRoot.node T+3)+k)<(T).id)
    (listCells : ∀ k,k<Y→NavigationCell u (numeric m (HistoryStageRoot.node T+3)+k))
    (incident : ∀ j : Fin 2,NavigationCell u (numeric m (HistoryStageRoot.node T+6)+j.val))
    (last : 0<numeric m (numeric m (HistoryStageRoot.node T+6))→∀ j,2≤j→j≤3→
      NavigationCell u (HistoryStageBounds.lastIncident T (numeric m)+j))
    (widths : ∀ k,2+ar k+(N k).internal<2^W) (bits : ((D₀).assemble trees z).compile.internal<2^W)
    (pins : step.words.ports.form.width v<2^W) (ids : ∀ tt,tag tt<2^W)
    (rowVolume : 4*(∑ k,(N k).cells)≤V) (large : 162≤V) (exts : step.words.ext v≤V)
    (later : seedCount≤ idx) (entry : Memory W) (kernelTime : ℕ)
    (kernelExec : (HistoryMotifJoin.kernelProcedure A W C).Exec entry m kernelTime)
    (kernelKeep : ∀ a,OutsideNode u idx a→m a=entry a) :
    ((HistoryStageBody.procedure A C W).Exec entry produced
        (kernelTime+((X).prepareCost+(B).ticks ops+writeCost A C T .result ((B).output ops))) ∧
    (NodeValue.ofSite (Run.nodeOfSite step.words (step.nextForest trees)
        (Run.pushedOrigin step orig) v) pointer (streamAt u seedCount idx) (endsAt u seedCount idx)).Cached
      tag u idx produced ∧
    ∀ a,OutsideNode u idx a→produced a=entry a) ∧
    kernelTime+((X).prepareCost+(B).ticks ops+writeCost A C T .result ((B).output ops)) ≤
      kernelTime+(6*StageRun.rootRate A C)*(step.nextForest trees v).resources := by
  obtain ⟨joined,cached,paid⟩:=run_priced L step record v u seedCount bank family m trees orig pointer tag
    visit order g head cells inputs b directory source nodes countRoom listRoom ports childSize child
    rootPins rootRows rootBits kernel earlier listCells incident last widths bits pins ids rowVolume large exts
  obtain ⟨stream,ends⟩:=stage_addresses u seedCount C bank family (numeric m) idx g.join.index later
  refine ⟨⟨kernelExec.then joined,?_,fun a ha=>?_⟩,Nat.add_le_add_left paid _⟩
  · rw [←stream,←ends]
    exact cached
  · exact (join_output_frame u idx bank family m N wire tag q g.join cells a ha).trans (kernelKeep a ha)

theorem visit_cache {K hEnd eEnd : ℕ} {cur ctr : Word W} {issuedMemory : Memory W} {allow : StaticMotif F→Prop}
    (visit : Diagonal.NavigationPass.RecordedWordStep K cur ctr hEnd eEnd issuedMemory Pins allow
      R branch L step old charge record) (order : step.ChildOrder record)
    (g : Ranges u idx bank family m N q) (head : (X).Header)
    (cells : SourceCells A C T (numeric m) W) (inputs : ∀ j,(T).words j<2^W)
    (b : Banks) (directory : DirectoryRow b record.sites.layer (record.sites.ord v) m)
    (source : record.data.Reads (numeric m)) (nodes : b.nodes=base u 44)
    (countRoom : record.sites.layer.childCount<2^W)
    (listRoom : record.sites.layer.children+(record.sites.ord v).val*record.sites.layer.childCount<2^W)
    (ports : HistoryStageRoot.Ports L.ports ((R.target_eq branch).symm ▸ step.words.ports)
      (D₀).count (D₀).child z T (numeric m))
    (childSize : ∀ k : Fin record.sites.layer.childCount,L.ext (record.row.children v k).val≤V)
    (child : ∀ k : Fin record.sites.layer.childCount,let id:=record.data.child (record.sites.ord v) k
      (NodeValue.ofSite (Run.nodeOfSite L trees orig (record.row.children v k).val) pointer
        (streamAt u seedCount id) (endsAt u seedCount id)).Cached tag u id m)
    (rootPins : (atResult (numeric m) (T).kernel).pins=(D₀).rootWidth z)
    (rootRows : (atResult (numeric m) (T).kernel).rows=((D₀).root z).compile.cells)
    (rootBits : (atResult (numeric m) (T).kernel).bits=((D₀).root z).compile.internal)
    (kernel : HistoryCompiledRows.Records tag ((D₀).root z).compile (atResult (numeric m) (T).kernel).stream m)
    (earlier : ∀ k,k<Y→numeric m (numeric m (HistoryStageRoot.node T+3)+k)<(T).id)
    (listCells : ∀ k,k<Y→NavigationCell u (numeric m (HistoryStageRoot.node T+3)+k))
    (incident : ∀ j : Fin 2,NavigationCell u (numeric m (HistoryStageRoot.node T+6)+j.val))
    (last : 0<numeric m (numeric m (HistoryStageRoot.node T+6))→∀ j,2≤j→j≤3→
      NavigationCell u (HistoryStageBounds.lastIncident T (numeric m)+j))
    (widths : ∀ k,2+ar k+(N k).internal<2^W) (bits : ((D₀).assemble trees z).compile.internal<2^W)
    (pins : step.words.ports.form.width v<2^W) (ids : ∀ tt,tag tt<2^W)
    (rowVolume : 4*(∑ k,(N k).cells)≤V) (large : 162≤V) (exts : step.words.ext v≤V)
    (later : seedCount≤ idx) (entry : Memory W) (kernelTime : ℕ)
    (kernelExec : (HistoryMotifJoin.kernelProcedure A W C).Exec entry m kernelTime)
    (kernelKeep : ∀ a,OutsideNode u idx a→m a=entry a) :
    (HistoryStageBody.procedure A C W).Exec entry produced
        (kernelTime+((X).prepareCost+(B).ticks ops+writeCost A C T .result ((B).output ops))) ∧
    (NodeValue.ofSite (Run.nodeOfSite step.words (step.nextForest trees)
        (Run.pushedOrigin step orig) v) pointer (streamAt u seedCount idx) (endsAt u seedCount idx)).Cached
      tag u idx produced ∧
    ∀ a,OutsideNode u idx a→produced a=entry a :=
  (visit_cache_priced L step record v u seedCount bank family m trees orig pointer tag
    visit order g head cells inputs b directory source nodes countRoom listRoom ports childSize child
    rootPins rootRows rootBits kernel earlier listCells incident last widths bits pins ids rowVolume large exts
    later entry kernelTime kernelExec kernelKeep).1

end
end ThreeFlat.RAM.HistoryWordStepRun

namespace ThreeFlat.Diagonal.PhysicalStage

open RAM.NavigationNodeRows HistoryContraction
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F] [Fintype F]

/-- A single return bound for the chosen arm for every reachable input memory
at this site. The outer visit also reserves every tested family guard. -/
def Block.nativeArmTime (B : Block F) (height K : ℕ) (b : Banks) (mem : ℕ→ℕ) (i : ℕ) :=
  B.stageClockRate*K*(4*height+3)*(archiveColumn b mem i 0/b.unitWork)

def Block.nativeVisitCost (B : Block F) (height K : ℕ) (b : Banks) (mem : ℕ→ℕ) (i : ℕ) :=
  B.nativeVisitRate height K*(archiveColumn b mem i 0/b.unitWork)

theorem State.ArchiveSites.Charged.nativeVisitCost {d l : ℕ} {X : State d l}
    {O : X.ArchiveSites} {prev pairs : X.Site→ℕ} {b : Banks} {mem : ℕ→ℕ}
    (paid : O.Charged b mem prev pairs) (B : Block F) (height K : ℕ)
    (pos : 0<b.unitWork) (x : X.Site) :
    B.nativeVisitCost height K b mem (O.id x)=B.nativeVisitRate height K*prev x := by
  unfold Block.nativeVisitCost
  rw [(paid x).1,Nat.mul_div_cancel_left _ pos]

/-- The same numerical charge applies at every child id and at its true
owner id in the literal chronological array. -/
theorem Run.nativeVisit_stagePrices {d l : ℕ} {X : State d l} (B : Block F) (height K : ℕ)
    (r : Run F X) (h : r.plan.History) (C : r.Charges) (O : X.ArchiveSites)
    (p : r.ArchivePath h C O) (b : Banks) (mem : ℕ→ℕ) (pos : 0<b.unitWork)
    (written : r.ArchiveRowsStored b mem h C O p) (depth : ℕ) (prev pairs : X.Site→ℕ)
    (now : O.Charged b mem prev pairs) :
    r.StagePrices (B.nativeVisitCost height K b mem) (B.nativeVisitFee height K) h C O p depth prev := by
  induction r generalizing depth with
  | done=>trivial
  | step R next ih=>
    have after:=p.1.charged b mem prev pairs now written.1
    refine ⟨?_,ih h.1 (tailHistory R next h) (C.2 h.1) p.1.sites p.2 written.2.2
      (depth+1) (R.push h.1 (C.1 h.1) prev) (fiberMass (R.parent h.1) pairs) after⟩
    intro v
    rw [after.nativeVisitCost B height K pos]
    have inc : (∑ a : {x // R.parent h.1 x=v},prev a.val)≤R.push h.1 (C.1 h.1) prev v :=
      Nat.le_add_left _ _
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left (B.nativeVisitFee height K depth) inc) _).trans
    unfold Block.nativeVisitFee
    exact le_of_eq (by ring)

/-- At the actual terminal depth this interior tariff fits the stage reserve
used by the greedy root schedule. -/
theorem Block.nativeVisitFee_stageUnit (B : Block F) (u coeff : ℕ) :
    let height:=(B.repeat (u^8)).length
    B.nativeVisitFee height (coeff*(16*u^10+1)^3) height≤B.stageUnit u coeff := by
  intro height
  let K:=coeff*(16*u^10+1)^3
  have scalar : (height+1)*(4*height+4)≤10*(height+2)^2 := by nlinarith
  calc
    B.nativeVisitFee height K height = ((height+1)*(4*height+4))*(B.stageClockRate*K) := by
      unfold Block.nativeVisitFee Block.nativeVisitRate
      ring
    _ ≤ (10*(height+2)^2)*(B.stageClockRate*K):=Nat.mul_le_mul_right _ scalar
    _ = B.stageUnit u coeff:=by unfold Block.stageUnit; dsimp only [height,K];ring

end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.RAM.HistoryStageBody.Physical

open Diagonal.PhysicalStage Diagonal.HistoryContraction Computability.VPVNP.BurstRAM PrivateRAM
open NavigationNodeRows
open scoped Classical BigOperators
noncomputable section

/-- Combine the genuinely chosen family's kernel and join time with the
memory-independent allowance assigned to this S44 row. -/
theorem CacheWrite.stage_price_at_id {F : Type} [Field F] [Fintype F] (B : Block F)
    {u start pages height K idx arity : ℕ} (A : Archive) (b : Banks) (mem : ℕ→ℕ)
    (entry : Memory (16*u^10)) (f : Family) (seed : ℕ) (arm : Family→ℕ)
    (member : f∈families B start pages) (guard : (families B start pages).find? (matchesFamily u entry)=some f)
    (tree : Tree F arity) (kernel : ℕ)
    (joined : arm f≤kernel+(6*StageRun.rootRate (layout u A f) f.childBound)*tree.resources)
    (kernelTicks : kernel≤B.stageClockRate*
      (K*(archiveColumn b mem idx 0/b.unitWork)+tree.resources))
    (size : tree.resources≤((2*height+1)*K)*(archiveColumn b mem idx 0/b.unitWork)) :
    bodyCost u entry seed arm (families B start pages)≤B.nativeVisitCost height K b mem idx := by
  have both:=CacheWrite.stage_price A B start pages entry f seed arm member guard tree kernel joined
  let mass:=archiveColumn b mem idx 0/b.unitWork
  calc
    _ ≤ kernel+B.stageClockRate*tree.resources:=both
    _ ≤ B.stageClockRate*(K*mass+((2*height+1)*K)*mass)+B.stageClockRate*(((2*height+1)*K)*mass) :=
      Nat.add_le_add (kernelTicks.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left size _)))
        (Nat.mul_le_mul_left _ size)
    _ ≤ B.nativeVisitCost height K b mem idx:=by
      dsimp only [Block.nativeVisitCost,Block.nativeVisitRate,mass]
      rw [show 4*height+4=(4*height+3)+1 by omega]
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one]
      nlinarith

/-- The seed arm uses the same S43 tariff as all later selected rows. -/
theorem CacheWrite.seed_price_at_id {F : Type} [Field F] [Fintype F] (B : Block F)
    {u start pages height K idx : ℕ} (b : Banks) (mem : ℕ→ℕ)
    (entry : Memory (16*u^10)) (seed : ℕ) (arm : Family→ℕ)
    (guard : (families B start pages).find? (matchesFamily u entry)=none)
    (unit : 1≤K) (nonempty : 1≤archiveColumn b mem idx 0/b.unitWork)
    (priced : seed≤B.stageClockRate*(archiveColumn b mem idx 0/b.unitWork)) :
    bodyCost u entry seed arm (families B start pages)≤B.nativeVisitCost height K b mem idx := by
  let mass:=archiveColumn b mem idx 0/b.unitWork
  have choose:=selection_cost B start pages u entry seed arm
  rw [guard] at choose
  change bodyCost u entry seed arm (families B start pages)≤blockGuardFee B+seed at choose
  have guardRate : blockGuardFee B≤B.stageClockRate:=by unfold Block.stageClockRate;omega
  have guards : blockGuardFee B≤B.stageClockRate*mass :=
    guardRate.trans (by simpa using Nat.mul_le_mul_left B.stageClockRate nonempty)
  have twice : 2*(B.stageClockRate*mass)≤B.nativeVisitCost height K b mem idx := by
    have scalar : 2≤K*(4*height+4) :=
      (by omega : 2≤4*height+4).trans (Nat.le_mul_of_pos_left _ unit)
    exact (Nat.mul_le_mul_right (B.stageClockRate*mass) scalar).trans_eq (by
      dsimp only [mass,Block.nativeVisitCost,Block.nativeVisitRate];ring)
  exact choose.trans ((Nat.add_le_add guards priced).trans (by simpa [two_mul] using twice))

end
end ThreeFlat.RAM.HistoryStageBody.Physical

namespace ThreeFlat.Diagonal.PhysicalStage

open RAM RAM.NavigationNodeRows RAM.HistoryStageBody HistoryContraction
open private priced_forest from OAI.ThreeFlat.Diagonal.PhysicalTypedAdmission
open scoped Classical BigOperators
noncomputable section

variable {F Pins : Type} [Field F] [Fintype F]
variable {d l D lanes height K cap W : ℕ} {S : State d l} {R : Move F S D lanes}
  {i : Fin R.rules.count} {L : S.Words Pins} {s : R.WordStep Pins L i}
  {old : S.ArchiveSites} {fresh : (R.next i).Site→ℕ} {row : R.ArchiveStep i old fresh}
  {b : Banks} {mem : ℕ→ℕ}

/-- Both refresh and shrink charge their kernel against the multiplicities
on this very archive row. Its issued tree can have any realizing forest. -/
theorem Move.ResourceReceipt.kernel_at_id
    (issued : R.ResourceReceipt K height cap b mem L s old fresh row) (B : Block F)
    (pos : 0<b.unitWork) (wordFee : (W+1)^3≤K) (N : Forest F L.ports.form)
    (v : (R.next i).Site) (ticks : ℕ)
    (run : ticks≤Physical.blockKernelRate B*((W+1)^3*(1+(row.data.motifCopies (row.sites.ord v)).sum)+1+
      (s.stage.root ((Equiv.cast (congrArg Shape.Site (R.target_eq i))).symm v)).resources)) :
    ticks≤B.stageClockRate*
      (K*(archiveColumn b mem (row.sites.id v) 0/b.unitWork)+(s.nextForest N v).resources) := by
  let z:=(Equiv.cast (congrArg Shape.Site (R.target_eq i))).symm v
  have paid : 1+(row.data.motifCopies (row.sites.ord v)).sum≤fresh v:=by
    have h:=row.row.fresh v
    omega
  have rate : Physical.blockKernelRate B≤B.stageClockRate:=by unfold Block.stageClockRate;omega
  have e := StageRun.kernel_ticks_from_site s.stage N z issued.prev paid wordFee rate run
  rw [(issued.after v).1,Nat.mul_div_cancel_left _ pos,priced_forest]
  rw [s.child_sum v issued.prev] at e
  exact e

end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.RAM.HistoryStageBody.Physical

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.PhysicalStage Diagonal.HistoryContraction NavigationNodeRows
noncomputable section
variable {F : Type} [Field F] [Fintype F] (B : Block F) {height K idx : ℕ} (b : Banks) (mem : ℕ→ℕ)
local notation "mass" => (archiveColumn b mem idx 0/b.unitWork)

/-- Price the single uniform seed/stage clock used by the dispatch theorem. -/
theorem nativeArm_dispatch {W u : ℕ} (start pages : ℕ) (entry : Memory W)
    (live : 1≤ mass) (unit : 1≤K) :
    bodyCost u entry (B.nativeArmTime height K b mem idx) (fun _=>B.nativeArmTime height K b mem idx)
      (families B start pages)≤B.nativeVisitCost height K b mem idx := by
  have chosen:=bodyCost_le_guardFee u entry (B.nativeArmTime height K b mem idx) (families B start pages)
  rw [guardFee_families] at chosen
  have one : 1≤K*mass:=by simpa only [Nat.one_mul] using Nat.mul_le_mul unit live
  have small : blockGuardFee B≤B.stageClockRate:=by unfold Block.stageClockRate;omega
  have saved : blockGuardFee B≤B.stageClockRate*(K*mass):=
    small.trans (by simpa using Nat.mul_le_mul_left B.stageClockRate one)
  calc
    _ ≤ B.nativeArmTime height K b mem idx+blockGuardFee B:=chosen
    _ ≤ B.nativeArmTime height K b mem idx+B.stageClockRate*(K*mass):=Nat.add_le_add_left saved _
    _ = B.nativeVisitCost height K b mem idx:=by
      unfold Block.nativeVisitCost Block.nativeArmTime Block.nativeVisitRate
      ring

/-- Raise the runtime from the actual chosen kernel and root scans to the
common per-row arm clock, keeping its exact output memory. -/
theorem nativeArm_stage {W u : ℕ} (start pages : ℕ) (A : Archive)
    (f : Family) (member : f∈families B start pages) {n : ℕ} (tree : Tree F n)
    (kernel full : ℕ) (sz : tree.resources≤((2*height+1)*K)*mass)
    (ker : kernel≤B.stageClockRate*(K*mass+tree.resources))
    (work : full≤kernel+(6*StageRun.rootRate (layout u A f) f.childBound)*tree.resources)
    (m out : Memory W) (run : (HistoryStageBody.procedure (layout u A f) f.childBound W).Exec m out full) :
    (HistoryStageBody.procedure (layout u A f) f.childBound W).Exec m out (B.nativeArmTime height K b mem idx) := by
  have fixed:=block_root_rate B start pages u A f member
  have rate : 6*StageRun.rootRate (layout u A f) f.childBound≤B.stageClockRate:=
    (Nat.mul_le_mul_left 6 fixed).trans (by unfold Block.stageClockRate;omega)
  apply PhysicalProcedure.Procedure.Spec.mono run (fun _ h=>h) (fun _ _ h=>h)
  calc
    _ ≤ kernel+(6*StageRun.rootRate (layout u A f) f.childBound)*tree.resources:=work
    _ ≤ B.stageClockRate*(K*mass+((2*height+1)*K)*mass)+B.stageClockRate*(((2*height+1)*K)*mass):=
      Nat.add_le_add (ker.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left sz _))) (Nat.mul_le_mul rate sz)
    _ = B.nativeArmTime height K b mem idx:=by unfold Block.nativeArmTime;ring

theorem nativeArm_seed {W : ℕ} (A : PhysicalProcedure.Procedure W) (m out : Memory W) (full : ℕ)
    (unit : 1≤K) (work : full≤B.stageClockRate*mass) (run : A.Exec m out full) :
    A.Exec m out (B.nativeArmTime height K b mem idx) := by
  apply PhysicalProcedure.Procedure.Spec.mono run (fun _ h=>h) (fun _ _ h=>h)
  have factor : 1≤K*(4*height+3):=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul unit (show 1≤4*height+3 by omega)
  calc
    full≤B.stageClockRate*mass:=work
    _ ≤ (K*(4*height+3))*(B.stageClockRate*mass):=Nat.le_mul_of_pos_left _ factor
    _ = B.nativeArmTime height K b mem idx:=by unfold Block.nativeArmTime;ring

end
end ThreeFlat.RAM.HistoryStageBody.Physical

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open PhysicalStage RAM RAM.HistoryNodeDirectory Computability.VPVNP.BurstRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] {d l : ℕ} {X : State d l}

/-- The actual S43 work columns cover every picked chronological row at its original
native group and slot, with no per-row execution or cached forest hypotheses. -/
theorem native_visit_quota (a : RootArchive) (B : Block F) (r : Run F X) (h : r.plan.History)
    (C : r.Charges) (O : X.ArchiveSites) (p : r.ArchivePath h C O) (m : Memory (16*a.age^10))
    (rows : r.ArchiveRowsStored a.nodeBank (fun z=>(m z).val) h C O p)
    (zero : O.layer.first=0) (first : a.firstFinal=(r.finalArchive h C O p).1.first)
    (card : a.rootCount=(r.finalArchive h C O p).1.count) (start pairs : X.Site→ℕ)
    (paid : O.Charged a.nodeBank (fun z=>(m z).val) start pairs)
    (stages : r.StageLength (B.repeat (a.age^8)).length)
    (positive : 0<a.nodeBank.unitWork) (tariff : B.stageUnit a.age B.localCoefficient≤a.nodeBank.unitWork)
    (slots : ℕ) (facts : let N:=nodesOfRun a r h C O p m rows zero first card start pairs
      ScheduleFacts a (16*a.age^10) slots N.work N.pairs a.ids)
    (groupsFit : a.groups≤2^(16*a.age^10)) (slotFit : slots≤2^(16*a.age^10))
    (rootFit : a.rootCount≤2^(16*a.age^10)) (g : Fin a.groups) (s : Fin slots) :
    let N:=nodesOfRun a r h C O p m rows zero first card start pairs
    let D:=a.selectedDirectory N slots (g.val:Word (16*a.age^10)) (s.val:Word (16*a.age^10))
    let cost:=B.nativeVisitCost (B.repeat (a.age^8)).length (B.localCoefficient*(16*a.age^10+1)^3)
      a.nodeBank (fun z=>(m z).val)
    (∑ i : Fin a.rootsTotal,if Selected.picked D i.val then cost i.val else 0)≤a.slotBudget/4 := by
  intro N D cost
  let height:=(B.repeat (a.age^8)).length
  let K:=B.localCoefficient*(16*a.age^10+1)^3
  refine selected_of_stage_prices a r h C O p m rows zero first card start pairs slots cost
    (B.nativeVisitFee height K) 0
    (r.nativeVisit_stagePrices B height K h C O p a.nodeBank (fun z=>(m z).val) positive rows 0 start pairs paid) ?_ ?_ facts groupsFit slotFit rootFit g s
  · intro x
    rw [show cost (O.id x)=B.nativeVisitRate height K*start x from paid.nativeVisitCost B height K positive x]
    simp [Block.nativeVisitFee]
  · rw [r.endLevel_stageLength h 0 _ stages,Nat.zero_add]
    exact (B.nativeVisitFee_stageUnit a.age B.localCoefficient).trans tariff
end
end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM PhysicalStage HistoryContraction
open TickWorkspace RAM.HistoryStageBody.Physical RAM.HistoryStageSetup RAM.NavigationNodeRows
open RAM.HistoryNodeDirectory RAM.HistoryNodeDirectory.Selected
open RAM.HistoryPartyBatchExec CompressorPacking Native RefreshStageNav
open scoped Classical BigOperators Fin.CommRing

noncomputable section
variable {F Pins : Type} [Field F] [Fintype F] {u K heads rom n : ℕ}
    {cur ctr : Word (16*u^10)} (q : RefreshReceipt F K cur) (B : Block F)
    (L : q.input.Words Pins) (y : (q.move.next q.term).Site) (b : Banks)
local notation "W" => 16*u^10
local notation "V" => volume u
local notation "step" => q.wordStep L
local notation "node" => q.step.sites.id y
local notation "target" => Move.WordStep.targetSite (R:=q.move) (i:=q.term) y
local notation "next₀" => ((q.move.target_eq q.term).symm ▸ (step).words.ports :
  PortLayout (q.move.rules.target q.term) Pins)
local notation "child" => (StageAddress.refreshInputIso q.input.graph q.input.chart (splitWord q.s q.rem)
    (tagOrdinal q.s).symm q.input.width).site.symm (q.chosenBlock y,(q.kernelSite y).1.2)
local notation "saves" => TickTerminalRoot.slotKeep u
local notation "safe" => (fun i=>saves i ∧ i<2^W)
variable {D : HistoryNodeDirectory.Selected.Directory (16*u^10) n} {tag : ((Fin 3→Bool)→F)→ℕ}
    {vals : Fin n→NodeValue F} {initial m final : Memory (16*u^10)} {idx : Fin n}
    (ledger : Ledger u D tag vals (TickTerminalRoot.slotKeep u) initial idx.val m)
local notation "before" => bump (ownerData W u) m


open private priced_forest from OAI.ThreeFlat.Diagonal.PhysicalTypedAdmission

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1900000 in
/-- Price the actual refresh kernel at the selected S43 node, using its issued
copies and the particular typed forest that the chronological stage inherits. -/
theorem kernel_ticks_at_id {fee levels cap ticks : ℕ} {bn : Banks} {paidMem : ℕ→ℕ}
    (paid : q.move.ResourceReceipt fee levels cap bn paidMem L step q.old q.charge q.step)
    (positive : 0<bn.unitWork) (wordFee : (W+1)^3≤fee) (trees : Forest F L.ports.form)
    (price : ticks≤blockKernelRate B*((W+1)^3*(1+refreshBinaryCopies q.tile q.input (q.chosenBlock y))+
      ((step).stage.root target).resources)) :
    ticks≤B.stageClockRate*(fee*(archiveColumn bn paidMem (q.step.sites.id y) 0/bn.unitWork)+
      ((step).nextForest trees y).resources) := by
  have rate : blockKernelRate B≤B.stageClockRate:=by unfold Block.stageClockRate;omega
  have full : ticks≤blockKernelRate B*((W+1)^3*(1+refreshBinaryCopies q.tile q.input (q.chosenBlock y))+1+
      ((step).stage.root target).resources):=price.trans (Nat.mul_le_mul_left _ (by omega))
  have e:=HistoryStageBody.StageRun.kernel_ticks_from_site (step).stage trees target paid.prev
    (q.issued_unit_copies_charge y) wordFee rate full
  have childWork := Move.WordStep.child_sum (R:=q.move) (i:=q.term) (step) y paid.prev
  have forestWork := priced_forest (R:=q.move) (i:=q.term) (step) trees y
  rw [(paid.after y).1,Nat.mul_div_cancel_left _ positive]
  exact e.trans_eq (congrArg₂ (fun children tree : ℕ =>
    B.stageClockRate*(fee*(q.charge y+children)+tree)) childWork forestWork.symm)

set_option maxRecDepth 23000 in
set_option maxHeartbeats 4300000 in
include ledger in
/-- Enter the refresh body at the cursor bump of the real selected-interior
ledger. The code and archive rows are read from durable banks. The actual
stage receipt pays for the selected copies and bounds both half tables. -/
theorem emit_bumped {fee levels cap degree : ℕ} {paidMem : ℕ→ℕ}
    (supported : B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (saved : SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (bounds : RefreshBounds heads q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
    (arrays : OldArrayBounds heads q.cursor q.input) (ord : q.input.OrderedHalves L)
    (paid : q.move.ResourceReceipt fee levels cap b paidMem L (q.wordStep L) q.old q.charge q.step)
    (unit : B.archiveUnit u B.localCoefficient degree≤b.unitWork) (positive : 0<b.unitWork) (peak : cap≤V)
    (age : 16≤u) (threshold : B.archiveConstant B.localCoefficient≤u)
    (index : idx.val=node) (nr : node<V^2)
    (nodes : b.nodes=base u 44) (charges : base u 19≤b.charges)
    (headsHigh : base u 19≤heads) (headersHigh : base u 19≤q.cursor.header)
    (romHigh : base u 19≤rom) (romFit : rom+libraryWords B W<2^W)
    (resident : Mounted B W W rom initial)
    (retained : ∀ i,(q.cursor.header≤ i ∧ i<q.entry.next.header ∨ heads≤ i)→i<q.entry.next.heap→initial i=final i)
    (row : DirectoryRow b q.step.sites.layer (q.step.sites.ord y) initial)
    (pred : DirectoryRow b q.old.layer (q.old.ord child) initial)
    (oldHalf : State.HalfRows q.old safe (numeric initial))
    (T : HistoryStageRoot.Input) (id : T.id=node) (bank : T.nodeBase=b.nodes) (cache : T.resultBase=base u 13)
    (ports : HistoryStageRoot.Ports L.ports next₀ (step).stage.count (step).stage.child target T (numeric before)) :
    ∃ post ticks, q.Emitted (height:=W) (rom:=rom) (initial:=before) B L y post ticks := by
  classical
  have big : 128≤V:=Nat.pow_le_pow_right (by decide:0<2)
    ((show 7≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have sq : V^2 ≤ TickWorkspace.stride u:=Nat.pow_le_pow_right (by omega : 0<V) (by decide:2≤4)
  have huge : 18<TickWorkspace.stride u:=by have low : V≤V^2:=Nat.le_self_pow (by decide) _;omega
  have wide:=word_space (u:=u) (i:=18) (by omega) huge
  have ctrl : base u 18<2^W:=by omega
  have fit : idx.val+1<2^W:=by omega
  have now:=NativeNavigation.bumped_index ledger ctrl fit
  have stay:=NativeNavigation.bumped_kept ledger ctrl (by omega : 0<TickWorkspace.stride u)
  have hi (i : ℕ) (hi₀ : base u 19≤ i) : before i=initial i:=stay i (.inr hi₀)
  have archive (i : ℕ) (lower : heads≤ i) (upper : i<q.entry.next.heap) : before i=final i:=
    (hi i (headsHigh.trans lower)).trans (retained i (.inr lower) upper)
  have hdr (i : ℕ) (lo : q.cursor.header≤ i) (top : i<q.entry.next.header) (hi₀ : i<q.entry.next.heap) :
      before i=final i:=(hi i (headersHigh.trans lo)).trans (retained i (.inl ⟨lo,top⟩) hi₀)
  have born : Mounted B W W rom before:=⟨fun i=>(hi _ (by omega)).trans (resident.words i)⟩
  have nodeHi : base u 19≤b.nodes:=by rw [nodes];exact Nat.mul_le_mul_right _ (by decide)
  have dir {s : Layer} {j : Fin s.count} (source : DirectoryRow b s j initial) : DirectoryRow b s j before:=
    source.retain (fun _ _=>hi _ (by omega)) (hi _ (by omega))
  have curr : numeric before (base u 18)=node+1:=now.trans (congrArg (·+1) index)
  let img : PartyImage (heads:=heads) q B W rom b y final before:=⟨born,archive,dir row,by omega⟩
  have literal:=q.issued_data y saved bounds (by omega : node<2^W)
  have oldData:=literal.2
  have original (i : ℕ) (h : q.cursor.heap≤ i ∧ i<q.entry.next.heap) : numeric before i=numeric final i:=
    congrArg Fin.val (archive i (bounds.header.trans h.1) h.2)
  have footprint : q.step.data.Footprint (fun i => base u 19 ≤ i ∧ i < 2^W) (numeric final) :=
    oldData.mono (fun i h=>⟨headsHigh.trans (bounds.header.trans h.1),
      h.2.trans (bounds.controls.1.trans_lt cur.isLt)⟩)
  have cells:=footprint.transfer oldData original
  have data:=literal.1.of_footprint oldData original
  have older (x : q.input.Site) : q.old.id x<node:=by
    have order:=q.step.row.contiguous
    have h:=(q.old.ord x).isLt
    unfold State.ArchiveSites.id
    omega
  have children j : q.step.data.child (q.step.sites.ord y) j<V^2:=by
    rw [q.step.row.childId];exact (older _).trans nr
  have price : q.charge y≤q.move.push q.term q.charge paid.prev y:=Nat.le_add_right ..
  have amount:=q.charge_positive y
  have margin:=B.grid_page_margin (show refreshGrid B∈grids B by simp [grids])
    amount unit ((Nat.mul_le_mul_left b.unitWork price).trans ((paid.newCap y).trans peak))
  have copies:=q.issued_copies_charge y
  have height:=q.elected_height B y b img supported (q.charge y) copies margin
  have boundsWidth:=q.funded_widths paid positive peak
  let lib:=q.issued_layout B rom W supported age (B.blockPageRate_at_age threshold) romHigh romFit
  have oldDegree : 2^q.s≤V:=by
    have num:=lib.cap;rw [lib.parties,lib.motifs] at num;omega
  have small:=q.issued_incident_fits B supported age oldDegree boundsWidth.2
  have newData:=q.halfRows (le_refl _) saved ⟨bounds.header,bounds.controls⟩ small
  have newHalf:=newData.transfer (fun i h=>congrArg Fin.val (archive i h.1 h.2))
    (fun i h=>show safe i from ⟨.inr (headsHigh.trans h.1),h.2.trans (bounds.controls.1.trans_lt cur.isLt)⟩)
  have old:=oldHalf.transfer (fun i h=>congrArg Fin.val (stay i h.1)) (fun _ h=>h)
  exact q.emit_recorded_refresh B L y b img supported saved bounds hdr arrays ord nodes charges headsHigh headersHigh
    romHigh romFit age (B.blockPageRate_at_age threshold) nr ((older _).trans nr) curr data cells children
    (fun _ h=>h) old newHalf (dir pred) T id bank cache ports height _ copies margin boundsWidth.1 boundsWidth.2

end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

namespace ThreeFlat.RAM.HistoryShrinkEmitter

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression Diagonal Diagonal.PhysicalStage
open Diagonal.HistoryContraction Diagonal.CompressorPacking Diagonal.CompressorPacking.Native
open Diagonal.CompressorPacking.Native.ShrinkStage Diagonal.NavigationPass Diagonal.ShrinkStageNav
open HistoryStageBody.Physical NavigationNodeRows
open scoped Classical BigOperators
open private priced_forest from OAI.ThreeFlat.Diagonal.PhysicalTypedAdmission

noncomputable section
variable {F Pins : Type} [Field F] [Fintype F] (B : Block F) (level : Fin B.levels)
    {u rem : ℕ}
local notation "s" => B.exponent level.val
local notation "D" => 2^B.exponent (level.val+1)
local notation "W" => 16*u^10
variable (hD : 0 < 2^(B.exponent (level.val+1)))
    (small : let degree : ℕ := 2^(B.exponent level.val)
      ((2^(2*degree+1)*degree*degree : ℕ) : ℝ) / (2^(B.exponent (level.val+1)) : ℕ) ≤ 1/1024)
    (A : State (2^(B.exponent level.val)) (shrinkCharge (B.exponent level.val)+rem))
local notation "M" => shrinkBinary B.shrink s D rem hD small A
variable (branch : Fin (shrinkBinary B.shrink (B.exponent level.val)
      (2^(B.exponent (level.val+1))) rem hD small A).rules.count)
    (L : A.Words Pins)
    (z : ((shrinkBinary B.shrink (B.exponent level.val)
      (2^(B.exponent (level.val+1))) rem hD small A).next branch).Site)
local notation "step" => shrinkBinary_assembler B.shrink s D rem hD small A L branch
local notation "charge" => shrinkBinaryCharge B.shrink s D rem hD small A branch
local notation "many" => shrinkRecordCopies B.shrink s rem A
variable (v : Computability.VPVNP.Compression.Site (shrinkRecordState (B.exponent level.val) rem A).Base
      (BitWord (Diagonal.CompressorPacking.tagBits (2^(B.exponent level.val)))) (BitWord rem))
    (order : let exponent := B.exponent level.val
      let nextDegree := 2^(B.exponent (level.val+1))
      let layout := ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink exponent nextDegree rem hD small A branch)
      Incidents.SiteOrder («S»:=shrinkStage exponent nextDegree) (shrinkRecordPacking exponent rem A)
        (shrinkRecordState exponent rem A).order layout v (16*u^10))
local notation "total" => ∑ i,many ((order.equiv i).val)
local notation "target" => Move.WordStep.targetSite (R:=M) (i:=branch) z

private theorem sum_site_enumeration {α : Type*} {n : ℕ} (e : Fin n ≃ α)
    (weights : α → ℕ) (enumeration : Fintype α) :
    (∑ i, weights (e i)) = (@Finset.univ α enumeration).sum weights := by
  let : Fintype α := enumeration
  exact e.sum_comp weights

set_option maxRecDepth 18000 in
set_option maxHeartbeats 2400000 in
/-- Price the kernel against the previous work stored at this very S43 row.
The roster enumerates precisely the active motifs in the issued word. -/
theorem kernel_ticks_at_id {fee levels cap ticks : ℕ} {bn : Banks} {paidMem : ℕ→ℕ}
    {old : A.ArchiveSites} {row : (M).ArchiveStep branch old charge}
    (placed : shrinkPackOrder s D rem A v=
      shrinkNextOrder B.shrink s D rem hD small A branch (((M).next branch).chart.symm z))
    (paid : (M).ResourceReceipt fee levels cap bn paidMem L step old charge row)
    (positive : 0<bn.unitWork) (wordFee : (W+1)^3≤fee) (trees : Forest F L.ports.form)
    (price : ticks≤blockKernelRate B*((W+1)^3*(1+total)+1+((step).stage.root target).resources)) :
    ticks≤B.stageClockRate*(fee*(archiveColumn bn paidMem (row.sites.id z) 0/bn.unitWork)+
      ((step).nextForest trees z).resources) := by
  have copies : total=(shrinkBinary_siteCopies B.shrink s D rem hD small A).copies branch z := by
    rw [shrinkBinary_copies_at,←placed,Equiv.symm_apply_apply]
    exact sum_site_enumeration order.equiv (fun a=>many a.val) _
  have paidCopies : 1+total≤charge z := by
    rw [copies]
    unfold shrinkBinaryCharge
    omega
  have rate : blockKernelRate B≤B.stageClockRate := by unfold Block.stageClockRate;omega
  have charged:=HistoryStageBody.StageRun.kernel_ticks_from_site (step).stage trees target paid.prev
    paidCopies wordFee rate price
  rw [(paid.after z).1,Nat.mul_div_cancel_left _ positive,priced_forest]
  have childSum : (∑ i, paid.prev ((step).stage.child target i).val) =
      ∑ x : {x // (M).parent branch x = z}, paid.prev x.val :=
    (step).child_sum z paid.prev
  rw [childSum] at charged
  exact charged

end
end ThreeFlat.RAM.HistoryShrinkEmitter

end OAI
