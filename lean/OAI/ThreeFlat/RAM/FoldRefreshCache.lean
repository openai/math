import OAI.ThreeFlat.Diagonal.HistoryCursorVisits
import OAI.ThreeFlat.Diagonal.TraceSeedPublishedFrame
import OAI.ThreeFlat.RAM.HistoryWordStepRanges

namespace OAI
/-! # Replaying an admitted stage from its chronological S43, S44 and child cache rows -/
set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryWordStepRun
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.HistoryContraction Diagonal.PhysicalStage Diagonal.TickWorkspace
open HistoryStageRoot HistoryStageBody HistoryStageSetup HistoryStageSnapshots
open HistoryPartyBatchExec HistoryStageBody.Physical HistoryStageBankArena HistoryBoundedBody HistoryBoundedJoin
open HistoryStageShapeWires NavigationNodeRows HistoryNodeDirectory HistoryNodeDirectory.Selected
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F Pins E : Type} [Field F] {d l D lanes : ℕ} {S : State d l} {R : Move F S D lanes}
  {branch : Fin R.rules.count} (L : S.Words Pins) (step : R.WordStep Pins L branch)
  {old : S.ArchiveSites} {charge : (R.next branch).Site→ℕ} (row : R.ArchiveStep branch old charge)
  (v : (R.next branch).Site) (u seedCount : ℕ) (bank : Archive) (family : Family)
  (trees : Forest F L.ports.form) (orig : ∀x,Fin (L.ext x)→E) (pointer : E→ℕ) (tag : ((Fin 3→Bool)→F)→ℕ)
local notation "W" => (16*u^10)
local notation "V" => volume u
local notation "A" => Physical.layout u bank family
local notation "C" => family.childBound
local notation "idx" => row.sites.id v
local notation "z" => Move.WordStep.targetSite (R:=R) (i:=branch) v
local notation "N" => fun k=>(step.stage.tapeFactor trees z k).compile
local notation "wire" => step.stage.tapePin trees z
local notation "ar" => step.stage.tapeArity trees z
local notation "rnk" => row.sites.ord v
local notation "childN" k:arg => NodeValue.ofSite (Run.nodeOfSite L trees orig (row.row.children v k).val) pointer
  (streamAt u seedCount (row.data.child rnk k)) (endsAt u seedCount (row.data.child rnk k))
local notation "outN" => NodeValue.ofSite (Run.nodeOfSite step.words (step.nextForest trees) (Run.pushedOrigin step orig) v)
  pointer (streamAt u seedCount idx) (endsAt u seedCount idx)

/-- The communication rows and paid endpoint bit count read at this actual stage.
All read addresses belong to one of the retained navigation intervals. -/
structure StageRows (b : Banks) (m : Memory W) : Prop where
  kind : m (b.nodes+8*idx)=(row.sites.layer.kind:Word W)
  directory : DirectoryRow b row.sites.layer rnk m
  reads : row.data.Reads (numeric m)
  footprint : row.data.Footprint (NavigationCell u) (numeric m)
  halves : State.HalfRows row.sites (NavigationCell u) (numeric m)
  pairs : 2*numeric m (b.charges+2*idx+1)=step.words.ext v

theorem StageRows.retain {b : Banks} {m out : Memory W}
    (h : StageRows L step row v u b m) (frame : ∀ a,NavigationCell u a→ out a=m a)
    (node : ∀ i : Fin 8,out (b.nodes+8*idx+i.val)=m (b.nodes+8*idx+i.val))
    (pairs : out (b.charges+2*idx+1)=m (b.charges+2*idx+1)) :
    StageRows L step row v u b out := by
  have n : ∀ a,NavigationCell u a→numeric out a=numeric m a:=fun a ha=>congrArg Fin.val (frame a ha)
  have atRoot : out (b.nodes+8*idx)=m (b.nodes+8*idx) := by
    simpa only [Fin.val_zero, Nat.add_zero] using node (0 : Fin 8)
  refine ⟨atRoot.trans h.kind,
    h.directory.retain (fun i _=>node i) pairs,h.reads.of_footprint h.footprint n,?_,
    h.halves.transfer n (fun _ h=>h),?_⟩
  · exact h.footprint.transfer h.footprint n
  · exact (congrArg (fun x : Word W=>2*x.val) pairs).trans h.pairs

/-- Each chronological move carries the genuine successor's row and every address
it reads inside the allocated histogram arena. -/
theorem recorded_data [Fintype F] {K head heap : ℕ} {cur ctr : Word W} {mid : Memory W}
    {allow : StaticMotif F→Prop}
    (record : Diagonal.NavigationPass.RecordedWordStep K cur ctr head heap mid Pins allow
      R branch L step old charge row) (fit : idx<2^W) :
    row.data.Reads (numeric mid) ∧ row.data.Footprint (fun i=>head≤ i ∧ i<heap) (numeric mid) := by
  rcases record with shrink|refresh
  · exact shrink.published_data
  · cases refresh with
    | native q limit saved bounds arrays layout allowed =>
      obtain ⟨read,fp⟩:=q.issued_data v saved bounds fit
      exact ⟨read,fp.mono (fun _ h=>⟨bounds.header.trans h.1,h.2.trans_le limit⟩)⟩

/-- Recovering the stage records after the loop increments S18. Its journal
and S43 words come from the actual retained bank and the same native node id. -/
theorem StageRows.of_bumped_source [Fintype F]
    {b : Banks} {K head heap : ℕ} {cur ctr : Word W} {mid out warm prev : Memory W}
    {xs : List Diagonal.PhysicalStage.NodeRow} {allow : StaticMotif F→Prop}
    {n : ℕ} {D₀ : HistoryNodeDirectory.Selected.Directory W n} {j : Fin n}
    {vals : Fin n→NodeValue F} {tt : ((Fin 3→Bool)→F)→ℕ}
    (ledger : Ledger u D₀ tt vals (TickTerminalRoot.slotKeep u) warm j.val prev)
    (source : Diagonal.NavigationPass.NativeNavigation.WarmSources u b xs mid out warm)
    (record : Diagonal.NavigationPass.RecordedWordStep K cur ctr head heap mid Pins allow
      R branch L step old charge row)
    (dir : Diagonal.NavigationPass.NativeNavigation.warmDirectoryVisit b warm R branch L step old charge row)
    (half : State.HalfRows row.sites (NavigationCell u) (numeric warm))
    (ext : 2*archiveColumn b (numeric out) idx 1=step.words.ext v)
    (cash : b.charges=base u 43) (nodes : b.nodes=base u 44)
    (low : base u 20≤head) (high : heap≤base u 40) (small : idx<V^2)
    (large : 40≤u) :
    StageRows L step row v u b (bump (ownerData W u) prev) := by
  obtain ⟨big,_,_,_,word⟩:=HistoryWordStepRanges.scale large small (show 0≤V from Nat.zero_le _)
  have stridePos : 0<Diagonal.TickWorkspace.stride u:=by unfold Diagonal.TickWorkspace.stride;positivity
  have under : V^2 ≤ Diagonal.TickWorkspace.stride u:=Nat.pow_le_pow_right (by omega) (by decide : 2≤4)
  have fit : idx<2^W:=by change 20*Diagonal.TickWorkspace.stride u<2^W at word;omega
  have cap : base u 18<2^W:=by change 19*Diagonal.TickWorkspace.stride u<2^W; change 20*Diagonal.TickWorkspace.stride u<2^W at word;omega
  have high40:=apart (u:=u) (by decide : 40<60)
  have span (a : ℕ) (h : head≤a ∧ a<heap) : NavigationCell u a :=
    ⟨low.trans h.1,(h.2.trans_le high).trans_le (by omega)⟩
  have frame (a : ℕ) (h : head≤a ∧ a<heap) : numeric warm a=numeric mid a :=
    congrArg Fin.val (source.journal a (low.trans h.1) (h.2.trans_le high))
  obtain ⟨reads,fp⟩:=recorded_data L step row v u record fit
  have loPair : base u 43≤b.charges+2*idx+1:=by rw [cash];omega
  have hiPair : b.charges+2*idx+1<base u 45:=by
    rw [cash];change 44*Diagonal.TickWorkspace.stride u+2*idx+1<46*Diagonal.TickWorkspace.stride u;omega
  have data : StageRows L step row v u b warm :=
    ⟨(dir.2 rnk).2,(dir.2 rnk).1,reads.of_footprint fp frame,
      (fp.transfer fp frame).mono span,half,
      (congrArg (fun x : Word W=>2*x.val) (source.published _ loPair hiPair)).trans ext⟩
  have kept (a : ℕ) (h : base u 19≤a) : bump (ownerData W u) prev a=warm a :=
    Diagonal.NavigationPass.NativeNavigation.bumped_kept ledger cap stridePos a (Or.inr h)
  exact StageRows.retain L step row v u data (fun a h=>kept a (by have:=apart (u:=u) (by decide : 19<20);have h':=h.1;omega))
    (fun i=>kept _ (by rw [nodes];have:=apart (u:=u) (by decide : 19<44);omega))
    (kept _ (by rw [cash];have:=apart (u:=u) (by decide : 19<43);omega))

variable (m : Memory (16*u^10)) (b : Banks)
local notation "T" => numInput A C (numeric m)
local notation "Y" => childCount T (numeric m)
local notation "X" => HistoryStageSetup.run A C m
local notation "q0" => Typed.copy T (numeric m) N wire
local notation "ops" => Tape.tape («W»:=W) N wire tag q0
local notation "produced" => adjust A C T .result ((X).compiled.output ops)

private theorem prior_id (i : Fin row.sites.layer.childCount) : row.data.child rnk i< idx := by
  have a:=(old.ord (row.row.children v i).val).isLt
  have seq:=row.row.contiguous
  have b:=row.row.childId v i
  change row.data.child rnk i=old.layer.first+_ at b
  change _<row.sites.layer.first+_
  omega

/-- On both sides of the elected kernel the same chronological slot has the
inherited endpoint arity and the genuine successor's incident width. -/
theorem StageRows.ports (h : StageRows L step row v u b m) (order : step.ChildOrder row)
    (id : (T).id=idx) (nodes : b.nodes=base u 44)
    (countRoom : row.sites.layer.childCount<2^W)
    (listRoom : row.sites.layer.children+(rnk).val*row.sites.layer.childCount<2^W)
    (halfRoom : row.sites.layer.incident+(rnk).val*2<2^W)
    (extRoom : step.words.ext v<2^W)
    (child : ∀ i : Fin row.sites.layer.childCount,(childN i).Cached tag u (row.data.child rnk i) m) :
    HistoryStageRoot.Ports L.ports ((R.target_eq branch).symm ▸ step.words.ports)
      step.stage.count step.stage.child z T (numeric m) := by
  exact stage_ports_of_outer L step row order v T m b u h.directory h.reads id nodes.symm rfl
    countRoom listRoom (by rw [h.pairs];exact extRoom) h.pairs h.halves halfRoom trees orig pointer tag
    (fun k=>⟨_,_,child k⟩)

/-- Convert the real source list and two-word incidence descriptor into the
three retained reads required by the native header, including the last width and
prefix when the port is nonempty. -/
private theorem retained_cells (h : StageRows L step row v u b m) (id : (T).id=idx)
    (nodes : b.nodes=base u 44) (countRoom : row.sites.layer.childCount<2^W)
    (listRoom : row.sites.layer.children+(rnk).val*row.sites.layer.childCount<2^W)
    (halfRoom : row.sites.layer.incident+(rnk).val*2<2^W) :
    (∀ i,i<Y→NavigationCell u (numeric m (HistoryStageRoot.node T+3)+i)) ∧
    (∀ a : Fin 2,NavigationCell u (numeric m (HistoryStageRoot.node T+6)+a.val)) ∧
    (0<numeric m (numeric m (HistoryStageRoot.node T+6))→∀ a,2≤a→a≤3→
      NavigationCell u (HistoryStageBounds.lastIncident T (numeric m)+a)) := by
  have addr : HistoryStageRoot.node T=b.nodes+8*idx:=by rw [HistoryStageRoot.node,id,nodes];rfl
  have list : numeric m (HistoryStageRoot.node T+3)=row.sites.layer.children+(rnk).val*row.sites.layer.childCount:=by
    rw [addr];exact (congrArg Fin.val h.directory.childPtr).trans (Fin.val_cast_of_lt listRoom)
  have head : numeric m (HistoryStageRoot.node T+6)=row.sites.layer.incident+(rnk).val*2:=by
    rw [addr];exact (congrArg Fin.val h.directory.incident).trans (Fin.val_cast_of_lt halfRoom)
  have degree : Y=row.sites.layer.childCount:=by
    change numeric m (HistoryStageRoot.node T+4)=_;rw [addr]
    exact (congrArg Fin.val h.directory.childCount).trans (Fin.val_cast_of_lt countRoom)
  have tail:=(Diagonal.NavigationPass.halfRows_tail h.halves h.reads).2
  refine ⟨?_,?_,?_⟩
  · intro i hi;rw [list];exact h.footprint.child _ ⟨i,degree ▸ hi⟩
  · intro i;rw [head];exact tail.header _ i
  · intro pos a lo hi
    rw [head,h.reads.halves] at pos
    have both:=tail.last rnk pos
    dsimp only [HistoryStageBounds.lastIncident]
    rw [head,h.reads.halves]
    rcases (show a=2 ∨ a=3 by omega) with rfl|rfl
    · exact both.1
    · exact both.2


set_option maxRecDepth 30000 in
set_option maxHeartbeats 1400000 in
/-- Complete the selected stage for the actual post-kernel image. The tiled
source rows and four published kernel header words determine every join input. -/
theorem finish_recorded {K hEnd eEnd : ℕ} {cur ctr : Word W} {mid : Memory W} {allow : StaticMotif F→Prop}
    (visit : Diagonal.NavigationPass.RecordedWordStep K cur ctr hEnd eEnd mid Pins allow
      R branch L step old charge row) (order : step.ChildOrder row)
    (h : StageRows L step row v u b m) (id : (T).id=idx) (nodes : b.nodes=base u 44)
    (age : 40≤u) (small : idx<V^2) (degree : row.sites.layer.childCount≤C) (capSmall : C≤V)
    (listRoom : row.sites.layer.children+(rnk).val*row.sites.layer.childCount<2^W)
    (halfRoom : row.sites.layer.incident+(rnk).val*2<2^W)
    (sector : (2*(family.parties+2)*8+5)*32+8≤V)
    (capacity : (family.motifs+2)*(family.parties+2)*8*32≤V)
    (refresh : ∀ a c d,family.mode=.refresh a c d→0<family.motifs)
    (child : ∀ k : Fin row.sites.layer.childCount,(childN k).Cached tag u (row.data.child rnk k) m)
    (paid : 4*(step.nextForest trees v).resources≤V) (arity : step.words.ports.form.width v≤V)
    (ext : step.words.ext v≤V) (ids : ∀tt,tag tt<2^W)
    (entry : Memory W) (kernelTime : ℕ) (later : seedCount≤ idx)
    (run : (HistoryMotifJoin.kernelProcedure A W C).Exec entry m kernelTime)
    (records : HistoryCompiledRows.Records tag (step.stage.root z).compile (kernelBase u idx family 0) m)
    (info : ∀ i : Fin 4,m (kernelBase u idx family 1+i.val)=
      (Info.words ⟨kernelBase u idx family 0,step.stage.rootWidth z,(step.stage.root z).rows,
        (step.stage.root z).bits⟩ i : Word W))
    (frame : ∀ a,OutsideNode u idx a→m a=entry a) :
    let extra:=(X).prepareCost+(X).compiled.ticks ops+writeCost A C T .result ((X).compiled.output ops)
    ((HistoryStageBody.procedure A C W).Exec entry produced (kernelTime+extra) ∧
      (outN).Cached tag u idx produced ∧ ∀ a,OutsideNode u idx a→produced a=entry a) ∧
    kernelTime+extra≤kernelTime+(6*StageRun.rootRate A C)*(step.nextForest trees v).resources := by
  classical
  intro extra
  obtain ⟨big,sc,arena,cache,limit⟩:=HistoryWordStepRanges.scale age small capSmall
  have space : 2+V<2^W:=by
    have low : V ≤ Diagonal.TickWorkspace.stride u:=Nat.le_self_pow (by decide : 4≠0) _
    change 20*Diagonal.TickWorkspace.stride u<2^W at limit
    omega
  obtain ⟨pins,rows,widths,bits⟩:=HistoryWordStepRanges.tape_fits (u:=u) («W»:=16*u^10) (L:=L) (step:=step) (v:=v) (trees:=trees) paid space
  have countRoom : row.sites.layer.childCount<2^W:=by omega
  obtain ⟨count,addr⟩:=recorded_child_addresses T m b row.data rnk h.directory h.reads id nodes.symm countRoom listRoom
  have countCap : Y≤C:=count.trans_le degree
  have port:=StageRows.ports (L:=L) (step:=step) (row:=row) (v:=v) (u:=u) (seedCount:=seedCount)
    (bank:=bank) (family:=family) (trees:=trees) (orig:=orig) (pointer:=pointer) (tag:=tag)
    (m:=m) (b:=b) h order id nodes countRoom listRoom halfRoom (by omega) child
  obtain ⟨list,incident,last⟩:=retained_cells L step row v u bank family m b h id nodes countRoom listRoom halfRoom
  have kptr:=kernel_pointer u idx bank family m id
  have sel:=kernel_sectors u idx bank family m id capacity refresh 0 (by decide)
  have ub : kernelBase u idx family 0<2^W:=by have := sel.2.1;have:=apart (u:=u) (by decide : 13<19);omega
  have rootPin : step.stage.rootWidth z<2^W:=by have i:=widths 0;change 2+step.stage.rootWidth z+_<2^W at i;omega
  have rootBits : (step.stage.root z).bits<2^W:=by
    have i:=widths 0
    change 2+step.stage.rootWidth z+(step.stage.root z).compile.internal<2^W at i
    rw [Tree.compiled_bits] at i;omega
  have rootRows : (step.stage.root z).rows<2^W:=by
    have a:=(Finset.single_le_sum (f:=fun k=>(N k).cells) (fun _ _=>Nat.zero_le _) (Finset.mem_univ 0))
    change (step.stage.root z).compile.cells≤_ at a;rw [Tree.compiled_rows] at a;omega
  have ks : (atResult (numeric m) (T).kernel).stream=kernelBase u idx family 0:=by
    change numeric m (T).kernel=_
    rw [kptr]
    have stream := (congrArg Fin.val (info 0)).trans (Fin.val_cast_of_lt ub)
    change numeric m (kernelBase u idx family 1 + 0) = kernelBase u idx family 0 at stream
    simpa only [Nat.add_zero] using stream
  have kp : (atResult (numeric m) (T).kernel).pins=step.stage.rootWidth z:=by
    change numeric m ((T).kernel+1)=_;rw [kptr]
    exact (congrArg Fin.val (info 1)).trans (Fin.val_cast_of_lt rootPin)
  have kr : (atResult (numeric m) (T).kernel).rows=(step.stage.root z).compile.cells:=by
    rw [Tree.compiled_rows];change numeric m ((T).kernel+2)=_;rw [kptr]
    exact (congrArg Fin.val (info 2)).trans (Fin.val_cast_of_lt rootRows)
  have kb : (atResult (numeric m) (T).kernel).bits=(step.stage.root z).compile.internal:=by
    rw [Tree.compiled_bits];change numeric m ((T).kernel+3)=_;rw [kptr]
    exact (congrArg Fin.val (info 3)).trans (Fin.val_cast_of_lt rootBits)
  let tagEq:=step.count_eq row v
  have childExt (k : Fin row.sites.layer.childCount) : L.ext (row.row.children v k).val≤V:=by
    have e:=HistoryWordStepRanges.child_external (L:=L) (step:=step) (v:=v) (u:=u) (trees:=trees) paid space (k.cast tagEq)
    have ord := order v k
    change (row.row.children v k).val = (step.stage.child z (k.cast tagEq)).val at ord
    rw [ord]
    exact e
  have earlier (i) (hi : i<Y) : numeric m (numeric m (HistoryStageRoot.node T+3)+i)<(T).id:=by
    let k : Fin row.sites.layer.childCount:=⟨i,count ▸ hi⟩
    have ptr:=addr k
    change (T).resultBase+8*numeric m (numeric m (HistoryStageRoot.node T+3)+i)=
      (T).resultBase+8*row.data.child rnk k at ptr
    have := prior_id row v k;omega
  have stops (i) (hi : i<Y) :
      Endpoints.srcAddr T (numeric m) i+Endpoints.width T (numeric m) i≤base u 12+(T).id*V^2:=by
    let k : Fin row.sites.layer.childCount:=⟨i,count ▸ hi⟩
    have H : atResult (numeric m) (base u 13+8*row.data.child rnk k) = (childN k).info :=
      (child k).header
    have bound:=(address_limits (u:=u) (seedCount:=seedCount) (i:=row.data.child rnk k)
      (rows:=0) big (by omega) (childExt k)).2.2
    change (atResult (numeric m) (childPtr T (numeric m) k.val)).ext+
      (atResult (numeric m) (childPtr T (numeric m) k.val)).extCount≤_
    rw [addr k,show (T).resultBase=base u 13 from rfl,H,id]
    exact previous_stream_before u idx (prior_id row v k) bound
  have total : HistoryStageRoot.prefix T (numeric m) Y Result.extCount≤V:=by
    rw [port.degree,prefix_value («T»:=T) (m:=numeric m) Result.extCount
      (fun k=>L.ext (step.stage.child z k).val) port.childExt _ le_rfl]
    have e:=(step.originOrder v).choose
    change step.words.ext v=∑ k,L.ext (step.stage.child z k).val at e
    simpa only [Fin.castLE_rfl, id_eq, e] using ext
  obtain ⟨head,cells,inputs,_⟩:=header_at_scale_geometry u bank family m age capSmall countCap
    (id.symm ▸ small) sector earlier list incident last stops total
  have g:=HistoryWordStepRanges.of_children L step row v u seedCount bank family m trees orig pointer tag
    order id b h.directory h.reads nodes countRoom listRoom child ks kp countCap big sc arena cache limit
    capacity refresh ext pins rows
  exact visit_cache_priced L step row v u seedCount bank family m trees orig pointer tag visit order g head cells
    inputs b h.directory h.reads nodes countRoom listRoom port childExt child kp kr kb (ks.symm ▸ records)
    earlier list incident last widths bits (by omega) ids rows big ext later entry kernelTime run frame

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1400000 in
/-- Execute the common CacheWrite from the native occupied/vacant kernel
output. The stage budget is the amount stored in the chronological S43 table. -/
theorem write_recorded [Fintype F] {K hEnd eEnd : ℕ} {cur ctr : Word W}
    {issued : Memory W} {allow : StaticMotif F→Prop}
    (visit : Diagonal.NavigationPass.RecordedWordStep K cur ctr hEnd eEnd issued Pins allow
      R branch L step old charge row) (order : step.ChildOrder row)
    (B : Block F) (start pages height tariff : ℕ) (record : ℕ→ℕ)
    (budget : b.unitWork>0) (fee : (W+1)^3≤tariff)
    (tariffed : R.ResourceReceipt tariff height (2^((3*u^10+4)/5)) b record L step old charge row)
    (cost : Run.PricedAt b record tariff height (2^((3*u^10+4)/5)) idx
      (Run.nodeOfSite step.words (step.nextForest trees) (Run.pushedOrigin step orig) v))
    (margin : 10*(height+2)^2*tariff≤b.unitWork)
    (age : 40≤u) (small : idx<V^2) (degree : row.sites.layer.childCount≤C) (capSmall : C≤V)
    (listRoom : row.sites.layer.children+(rnk).val*row.sites.layer.childCount<2^W)
    (halfRoom : row.sites.layer.incident+(rnk).val*2<2^W)
    (sector : (2*(family.parties+2)*8+5)*32+8≤V)
    (capacity : (family.motifs+2)*(family.parties+2)*8*32≤V)
    (refresh : ∀ a c d,family.mode=.refresh a c d→0<family.motifs)
    (entry : Memory W) (cursor : (numInput A C (numeric entry)).id=idx)
    (observed : StageRows L step row v u b entry) (nodes : b.nodes=base u 44)
    (charges : b.charges=base u 43)
    (prior : ∀ k : Fin row.sites.layer.childCount,(childN k).Cached tag u (row.data.child rnk k) entry)
    (ids : ∀tt,tag tt<2^W) (later : seedCount≤ idx) (kernelTime : ℕ)
    (run : (HistoryMotifJoin.kernelProcedure A W C).Exec entry m kernelTime)
    (records : HistoryCompiledRows.Records tag (step.stage.root z).compile (kernelBase u idx family 0) m)
    (info : ∀ i : Fin 4,m (kernelBase u idx family 1+i.val)=
      (Info.words ⟨kernelBase u idx family 0,step.stage.rootWidth z,(step.stage.root z).rows,
        (step.stage.root z).bits⟩ i : Word W))
    (frame : ∀ a,OutsideNode u idx a→m a=entry a)
    (kernelPrice : kernelTime≤B.stageClockRate*(tariff*(archiveColumn b record idx 0/b.unitWork)+
      (step.nextForest trees v).resources))
    (which : (families B start pages).find? (matchesFamily u entry)=some family)
    (header : stageAddress u entry+48<2^W) (degrees : 2^B.exponent B.levels<2^W)
    (shape : TraceBucketAtom.Layout) (pub : Fin TraceEndpointROM.params→Word W)
    {n : ℕ} (vals : Fin n→NodeValue F) (j : Fin n) (number : j.val=idx) (same : vals j=outN) :
    let arm:=fun i : Fin n=>B.nativeArmTime height tariff b record i.val
    CacheWrite bank shape pub (families B start pages) vals tag (B.nativeVisitCost height tariff b record)
      arm (fun i _=>arm i) j entry := by
  classical
  intro arm
  obtain ⟨big,_,arena,cache,word⟩:=HistoryWordStepRanges.scale age small capSmall
  have high (a : ℕ) (hi : base u 19≤a) : m a=entry a:=by
    have s12:=apart (u:=u) (by decide : 13<19);have s13:=apart (u:=u) (by decide : 14<19)
    exact frame _ ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (Or.inl hi)⟩
  have atCtr : m (base u 18)=entry (base u 18):=by
    have s12:=apart (u:=u) (by decide : 13<18);have s13:=apart (u:=u) (by decide : 14<18)
    exact frame _ ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (Or.inr (Or.inl rfl))⟩
  have id : (T).id=idx:=by
    change (m (base u 18)).val-1=_
    rw [atCtr];exact cursor
  have here : StageRows L step row v u b m := by
    apply StageRows.retain L step row v u observed
    · intro a ha
      apply high a
      exact (Nat.le_add_right _ _).trans ((apart (u:=u) (by decide : 19<20)).trans ha.1)
    · intro i
      apply high
      rw [nodes]
      have h := apart (u:=u) (by decide : 19<44)
      omega
    · apply high
      rw [charges]
      have h := apart (u:=u) (by decide : 19<43)
      omega
  have scale : 2≤tariff:=by
    have smallW : 2≤W+1:=by have p:=Nat.one_le_pow 10 u (by omega);omega
    exact smallW.trans ((Nat.le_self_pow (by decide : 3≠0) _).trans fee)
  obtain ⟨rowsNow,extNow,inner⟩:=cost.native_words (by omega) scale margin
  obtain ⟨_,_,_,paid⟩:=cost.slab (by omega) scale margin
  have charged : 4*(step.nextForest trees v).resources≤V:=by change 8*(step.nextForest trees v).resources≤V at paid;omega
  have ext : step.words.ext v≤V:=extNow
  have width : step.words.ports.form.width v≤V:=by change _+step.words.ports.form.width v≤V at inner;omega
  have smallWord : 2+V<2^W:=by
    have sq : V ≤ Diagonal.TickWorkspace.stride u:=Nat.le_self_pow (by decide : 4≠0) _
    change 20*Diagonal.TickWorkspace.stride u<2^W at word
    omega
  have earlier (k : Fin row.sites.layer.childCount) : (childN k).Cached tag u (row.data.child rnk k) m:=by
    apply NodeValue.Cached.retain (childN k) tag (prior k)
    intro a use
    let e:=step.count_eq row v
    let i:=k.cast e
    have order':=order v k
    have oldExt:=HistoryWordStepRanges.child_external (L:=L) (step:=step) (v:=v) (u:=u) (trees:=trees) charged smallWord i
    have total:=(HistoryWordStepRanges.tape_fits (L:=L) (step:=step) (v:=v) (u:=u) (trees:=trees) charged smallWord).2.1
    have rc : 4*(N i.succ).cells≤V:=(Nat.mul_le_mul_left 4
      (Finset.single_le_sum (f:=fun part=>(N part).cells) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i.succ))).trans total
    have room:=address_limits (u:=u) (seedCount:=seedCount) (i:=row.data.child rnk k) big rc oldExt
    apply frame
    apply ((childN k).earlier_outside u idx (prior_id row v k) arena cache _ _ use).1
    · change streamAt _ _ _+4*(trees _).compile.cells≤_;rw [order'];exact room.2.1.trans (by omega)
    · change endsAt _ _ _+L.ext _≤_;rw [order'];exact room.2.2
  obtain ⟨⟨exec,cached,frame'⟩,ticks⟩:=finish_recorded L step row v u seedCount bank family trees orig pointer tag m b
    visit order here id nodes age small degree capSmall listRoom halfRoom sector capacity refresh earlier charged width ext ids
    entry kernelTime later run records info frame
  have price:=cost.horizon budget
  have member : family∈families B start pages:=List.mem_of_find?_eq_some which
  have actual : (HistoryStageBody.procedure A C W).Exec entry produced
      (B.nativeArmTime height tariff b record idx) :=
    nativeArm_stage (height:=height) (K:=tariff) («idx»:=idx) B b record start pages bank family member
      (step.nextForest trees v) kernelTime _ price kernelPrice ticks entry produced exec
  have one : 1≤archiveColumn b record idx 0/b.unitWork:=by
    rw [(tariffed.after v).1,Nat.mul_div_cancel_left _ budget]
    have:=tariffed.nextFloor v;omega
  have baseWord:=word_space (u:=u) (i:=44) (by omega) (by change 44<V^4;have:=Nat.le_self_pow (by decide : 4≠0) V;omega)
  have near : nodeAddress u entry+5<2^W:=by
    change base u 44+8*(entry (base u 18)).val.pred+5<_
    change (entry (base u 18)).val.pred = idx at cursor
    rw [cursor, Nat.add_assoc]
    have digits : 8 ≤ V^2 := by have := Nat.le_self_pow (by decide : 2 ≠ 0) V; omega
    have off : 8 * idx + 5 ≤ V^4 := calc
      8 * idx + 5 ≤ (idx+1) * 8 := by omega
      _ ≤ (idx+1) * V^2 := Nat.mul_le_mul_left _ digits
      _ ≤ V^2 * V^2 := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt small)
      _ = V^4 := by ring
    change base u 44 + V^4 < 2^W at baseWord
    exact (Nat.add_le_add_left off _).trans_lt baseWord
  apply CacheWrite.of_stage bank shape pub (families B start pages) vals tag _ _ _ j entry produced family near
    (fun f hf _=>⟨header,(family_ports_bound B start pages f hf).trans_lt degrees⟩)
    (nativeArm_dispatch (height:=height) (K:=tariff) («idx»:=j.val) B b record start pages entry
      (number.symm ▸ one) (by omega)) which
  have armTime : arm j = B.nativeArmTime height tariff b record idx :=
    congrArg (B.nativeArmTime height tariff b record) number
  have elected := congrArg (fun ticks => (HistoryStageBody.procedure A C W).Exec entry produced ticks) armTime.symm
  exact ⟨elected.mp (@actual),by simpa only [same,number] using cached,
    fun a ha=>frame' a (number ▸ ha)⟩

end
end ThreeFlat.RAM.HistoryWordStepRun

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM PhysicalStage HistoryContraction
open RAM.HistoryWordStepRun RAM.HistoryStageBody RAM.HistoryMotifJoin RAM.HistoryBoundedJoin TickWorkspace RAM.HistoryStageBody.Physical RAM.HistoryStageSetup RAM.NavigationNodeRows
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
variable {D : HistoryNodeDirectory.Selected.Directory (16*u^10) n} {tag : ((Fin 3→Bool)→F)→ℕ} {vals : Fin n→NodeValue F}
    {initial m final : Memory (16*u^10)} {idx : Fin n}
    (ledger : Ledger u D tag vals (TickTerminalRoot.slotKeep u) initial idx.val m)
local notation "before" => bump (ownerData W u) m


variable {E : Type} (seedCount : ℕ) (trees : Forest F L.ports.form) (orig : ∀ x,Fin (L.ext x)→E)
    (pointer : E→ℕ) {heapEnd : ℕ}
local notation "tag₀" => RAM.HistoryRefreshEmitter.tag (K:=F)
local notation "arc" => archive B rom W K
local notation "family" => refreshFamily B rom W
local notation "A₀" => layout u arc family
local notation "C" => (family).childBound
local notation "T" => numInput A₀ C (numeric before)
local notation "rank₀" => q.step.sites.ord y
local notation "rig" => q.step
local notation "childN" i:arg => NodeValue.ofSite (Run.nodeOfSite L trees orig ((rig).row.children y i).val)
  pointer (streamAt u seedCount ((rig).data.child rank₀ i)) (endsAt u seedCount ((rig).data.child rank₀ i))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
include ledger in
/-- The refresh constructor in the selected chronology emits the actual
numerical kernel banks of this stage. Its prior cache records compute all
pins of the native join, and the exact physical party code publishes its root. -/
theorem emit_occurrence {fee levels cap degree : ℕ} {paidMem : ℕ→ℕ}
    (supported : B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (saved : SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (bounds : RefreshBounds heads q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
    (arrays : RecordedArrayBounds W heads q.cursor q.input) (ord : q.input.OrderedHalves L)
    (paid : q.move.ResourceReceipt fee levels cap b paidMem L (q.wordStep L) q.old q.charge q.step)
    (unit : B.archiveUnit u B.localCoefficient degree≤b.unitWork) (positive : 0<b.unitWork) (peak : cap≤V)
    (age : 16≤u) (threshold : B.archiveConstant B.localCoefficient≤u)
    (index : idx.val=node) (nr : node<V^2)
    (nodes : b.nodes=base u 44) (charges : base u 19≤b.charges)
    (headsHigh : base u 19≤heads) (limit : q.entry.next.heap≤heapEnd)
    (romHigh : base u 19≤rom) (romFit : rom+libraryWords B W<2^W)
    (resident : Mounted B W W rom initial)
    (retained : ∀ i,(q.cursor.header≤ i ∧ i<q.entry.next.header ∨ heads≤ i)→i<q.entry.next.heap→initial i=final i)
    (row : DirectoryRow b q.step.sites.layer (q.step.sites.ord y) initial)
    (pred : DirectoryRow b q.old.layer (q.old.ord child) initial)
    (oldHalf : State.HalfRows q.old safe (numeric initial))
    (entryRows : StageRows L (step) (rig) y u b before)
    (listRoom : (rig).sites.layer.children+(rank₀).val*(rig).sites.layer.childCount<2^W)
    (halfRoom : (rig).sites.layer.incident+(rank₀).val*2<2^W)
    (external : (step).words.ext y<2^W)
    (children : ∀i : Fin (rig).sites.layer.childCount,(childN i).Cached tag₀ u ((rig).data.child rank₀ i) before)
    (wordFee : (W+1)^3≤fee) :
    ∃ post ticks,(kernelProcedure A₀ W C).Exec before post ticks ∧
      HistoryCompiledRows.Records tag₀ ((step).stage.root target).compile (kernelBase u node family 0) post ∧
      (∀j:Fin 4,post (kernelBase u node family 1+j.val)=(Info.words ⟨kernelBase u node family 0,
        (step).stage.rootWidth target,((step).stage.root target).rows,((step).stage.root target).bits⟩ j:Word W)) ∧
      (∀i,OutsideNode u node i→post i=before i) ∧
      ticks≤B.stageClockRate*(fee*(archiveColumn b paidMem node 0/b.unitWork)+((step).nextForest trees y).resources) := by
  classical
  let visit : RefreshWordVisit K cur ctr heads heapEnd final B.publicTemplate q.move q.term L (step) q.old q.charge q.step :=
    .native q limit saved bounds arrays L supported
  have one : (rig).sites.layer.childCount=1:=by rw [q.issued_layer];rfl
  have H : 128≤V:=Nat.pow_le_pow_right (by decide:0<2)
    ((show 7≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have sq : V^2 ≤ Diagonal.TickWorkspace.stride u:=Nat.pow_le_pow_right (by omega : 0<V) (by decide:2≤4)
  have wide:=word_space (u:=u) (i:=18) (by omega) (by have low : V≤V^2:=Nat.le_self_pow (by decide) _;omega)
  have idxNow:=NativeNavigation.bumped_index ledger (by omega) (by omega)
  have num : (T).id=node:=by change (before (base u 18)).val-1=node;omega
  have pre:=StageRows.ports (L:=L) («step»:=q.wordStep L) (row:=q.step) (v:=y) (u:=u)
    (seedCount:=seedCount) (bank:=arc) («family»:=family) (trees:=trees) (orig:=orig)
    (pointer:=pointer) (tag:=tag₀) (m:=before) (b:=b) entryRows
    visit.childOrder num nodes (by omega) listRoom halfRoom external children
  obtain ⟨post,ticks,emitted⟩:=q.emit_bumped B L y b ledger supported saved bounds arrays.toOldArrayBounds ord paid
    unit positive peak age threshold index nr nodes charges headsHigh arrays.header_at romHigh romFit resident retained
    row pred oldHalf T num nodes.symm rfl pre
  have library:=q.issued_layout B rom W supported age (B.blockPageRate_at_age threshold) romHigh romFit
  have coordinates (j : ℕ) :
      resultBank (withMotif A₀ 0) node true j=kernelBase u node family j:=by
    unfold kernelBase
    rw [library.mode]
    rfl
  obtain ⟨run,records,info,frame,price⟩:=emitted
  rw [coordinates] at records
  simp only [coordinates] at info
  have finalCost:=q.kernel_ticks_at_id B L y paid positive wordFee trees price
  exact ⟨post,ticks,library.childBound.symm ▸ run,records,info,frame,finalCost⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
include ledger in
/-- Run the fully compiled refresh family in the native dispatch. The two degree
comparisons read the records emitted by this very refresh. -/
theorem write_occurrence_with_selection {fee levels degree : ℕ} {paidMem : ℕ→ℕ}
    (supported : B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (saved : SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (bounds : RefreshBounds heads q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
    (arrays : RecordedArrayBounds W heads q.cursor q.input) (ord : q.input.OrderedHalves L)
    (paid : q.move.ResourceReceipt fee levels (2^((3*u^10+4)/5)) b paidMem L (q.wordStep L) q.old q.charge q.step)
    (unit : B.archiveUnit u B.localCoefficient degree≤b.unitWork) (positive : 0<b.unitWork)
    (age : 40≤u) (threshold : B.archiveConstant B.localCoefficient≤u)
    (index : idx.val=node) (nr : node<V^2)
    (nodes : b.nodes=base u 44) (charges : b.charges=base u 43)
    (headsHigh : base u 19≤heads) (limit : q.entry.next.heap≤heapEnd)
    (romHigh : base u 19≤rom) (romFit : rom+libraryWords B W<2^W)
    (resident : Mounted B W W rom initial)
    (retained : ∀ i,(q.cursor.header≤ i ∧ i<q.entry.next.header ∨ heads≤ i)→i<q.entry.next.heap→initial i=final i)
    (row : DirectoryRow b q.step.sites.layer (q.step.sites.ord y) initial)
    (pred : DirectoryRow b q.old.layer (q.old.ord child) initial)
    (oldHalf : State.HalfRows q.old safe (numeric initial))
    (entryRows : StageRows L (step) (rig) y u b before)
    (listRoom : (rig).sites.layer.children+(rank₀).val*(rig).sites.layer.childCount<2^W)
    (halfRoom : (rig).sites.layer.incident+(rank₀).val*2<2^W)
    (external : (step).words.ext y<2^W)
    (children : ∀i : Fin (rig).sites.layer.childCount,(childN i).Cached tag₀ u ((rig).data.child rank₀ i) before)
    (wordFee : (W+1)^3≤fee)
    (later : seedCount≤node) (shape : TraceBucketAtom.Layout) (pub : Fin TraceEndpointROM.params→Word W)
    (margin : 10*(levels+2)^2*fee≤b.unitWork)
    (resource : Run.PricedAt b paidMem fee levels (2^((3*u^10+4)/5)) node
      (Run.nodeOfSite (step).words ((step).nextForest trees) (Run.pushedOrigin (step) orig) y))
    (same : vals idx=NodeValue.ofSite (Run.nodeOfSite (step).words ((step).nextForest trees)
      (Run.pushedOrigin (step) orig) y) pointer (streamAt u seedCount node) (endsAt u seedCount node)) :
    let arm:=fun i : Fin n=>B.nativeArmTime levels fee b paidMem i.val
    (∃ f, (families B rom W).find? (matchesFamily u before)=some f) ∧
    CacheWrite arc shape pub (families B rom W) vals tag₀ (B.nativeVisitCost levels fee b paidMem)
      arm (fun i _=>arm i) idx before := by
  classical
  let actual : RefreshWordVisit K cur ctr heads heapEnd final B.publicTemplate
      q.move q.term L (step) q.old q.charge q.step:=.native q limit saved bounds arrays L supported
  have real : RecordedWordStep K cur ctr heads heapEnd final Pins B.publicTemplate
      q.move q.term L (step) q.old q.charge q.step:=Or.inr actual
  let lib:=q.issued_layout B rom W supported (by omega) (B.blockPageRate_at_age threshold) romHigh romFit
  have pos : 0<u^10:=Nat.pow_pos (by omega : 0<u)
  have peak : 2^((3*u^10+4)/5)≤V:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega)
  have cap : C=1:=lib.childBound
  have mounts:=apart (u:=u) (by decide : 19<43)
  obtain ⟨post,ticks,run,records,info,frame,price⟩:=q.emit_occurrence B L y b ledger seedCount trees orig pointer
    supported saved bounds arrays ord paid unit positive peak (by omega) threshold index nr nodes
    (by rw [charges];omega) headsHigh limit romHigh romFit resident retained row pred oldHalf
    entryRows listRoom halfRoom external children wordFee
  have big : 128≤V:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) ((show 7≤u by omega).trans
    (Nat.le_self_pow (by decide) _))
  obtain ⟨_,_,_,_,space⟩:=HistoryWordStepRanges.scale age nr (show C≤V by omega)
  have vhi : V^2 ≤ Diagonal.TickWorkspace.stride u:=Nat.pow_le_pow_right (by omega : 0<V) (by decide : 2≤4)
  have lower:=apart (u:=u) (by decide : 18<19)
  have idxNow:=NativeNavigation.bumped_index ledger (by omega)
    (by rw [index];change 20*Diagonal.TickWorkspace.stride u<2^W at space;omega)
  have current : numeric before (base u 18)-1=node:=by change (before (base u 18)).val-1=node;omega
  let z:=q.kernelSite y
  let P:=CursorSpace.recordPointers q.entry
  let j:=(rank₀).val
  let kp:=P.kernel+j*5
  have cell (a) (hi : base u 19≤a) : before a=initial a:=
    NativeNavigation.bumped_kept ledger (by omega) (by unfold Diagonal.TickWorkspace.stride;positivity) a (Or.inr hi)
  have restored (a) (hlo : q.cursor.header≤a ∧ a<q.entry.next.header ∨ heads≤a)
      (hi : a<q.entry.next.heap) : before a=final a:=by
    obtain low|high:=hlo
    · exact (cell _ (arrays.header_at.trans low.1)).trans (retained _ (Or.inl low) hi)
    · exact (cell _ (headsHigh.trans high)).trans (retained _ (Or.inr high) hi)
  have keep (a) (lo : q.cursor.heap≤a) (hi : a<q.entry.next.heap) : before a=final a:=
    restored _ (Or.inr (bounds.header.trans lo)) hi
  have inc:=q.incidence_at_entry saved ⟨bounds.header,bounds.controls⟩ keep family lib.parties y b nodes
    entryRows.directory current lib.mask
  have num : nodeAddress u before=base u 44+8*node:=congrArg (fun t=>base u 44+8*t) current
  have mark : (before (nodeAddress u before)).val=2:=by
    rw [num,←nodes,entryRows.kind,q.issued_layer]
    exact Fin.val_cast_of_lt (by have:=cur.isLt;change 2<2^W;change 20*Diagonal.TickWorkspace.stride u<2^W at space;omega)
  have kptr : (before (nodeAddress u before+5)).val=kp:=by rw [num];exact inc.kernel
  have offset : (Records.rowOrder (1+q.h+q.pad) .kernel (z,(0:Fin 5))).val=j*5:=by
    have site : Records.siteId (z.1.1,z.2) z.1.2=j:=q.kernelSite_index y
    rw [Records.rowOrder,RefreshStageLayout.pair_index,Records.siteOrder_val,site]; rfl
  have interval:=q.record_interval .kernel (Records.rowOrder (1+q.h+q.pad) .kernel (z,(0:Fin 5)))
  rw [offset] at interval
  have heap:=q.issued.headerBelow
  have few : q.cursor.header+48<q.entry.next.heap:=by have:=interval.1;have:=interval.2;omega
  have headerFits : q.cursor.header+48<2^W:=by have:=cur.isLt;have:=bounds.controls.1;omega
  have raw:=q.at_entry saved ⟨bounds.header,bounds.controls⟩ keep .kernel (z,(0:Fin 5))
  change before (P.kernel+(Records.rowOrder (1+q.h+q.pad) .kernel (z,(0:Fin 5))).val)=(q.cursor.header:Word W) at raw
  rw [offset] at raw
  have head : (before kp).val=q.cursor.header:=(congrArg Fin.val raw).trans (Fin.val_cast_of_lt (by omega))
  have degreeAt : (before (q.cursor.header+48)).val=2^q.s:=by
    rw [restored _ (Or.inl ⟨by omega,by change _<q.cursor.header+64;omega⟩) few]
    exact SavedFrame.familyDegree (K:=K) q.cursor
      (.refresh (Fintype.card q.input.Base) (2^q.s) (2^q.rem) q.h q.pad)
      saved q.issued.headerBelow bounds.controls.1
      (bounds.controls.1.trans bounds.controls.2.le) q.issued.degreeWord
  have choice:=select_supported_refresh B supported rom W u before kp q.cursor.header mark kptr head degreeAt
  let exponentOf : StaticMotif F→ℕ
    | .shrink s .. => s
    | .refresh s .. => s
  have exponent : q.s=B.exponent B.levels:=congrArg exponentOf choice.1
  have oldD : 2^B.exponent B.levels<2^W:=by
    have cost:=lib.cap;rw [lib.motifs,lib.parties] at cost
    have one : V ≤ Diagonal.TickWorkspace.stride u:=Nat.le_self_pow (by decide : 4≠0) _
    rw [←exponent];change 20*Diagonal.TickWorkspace.stride u<2^W at space;omega
  have sector : (2*((family).parties+2)*8+5)*32+8≤V:=by
    have fee:=lib.cap;rw [lib.motifs] at fee;omega
  have list : (rig).sites.layer.childCount≤C:=by rw [q.issued_layer,cap]; exact le_rfl
  have tags (tt : (Fin 3→Bool)→F) : tag₀ tt<2^W:=
    lt_of_lt_of_le (Fintype.equivFin _ tt).isLt lib.tags
  refine ⟨⟨_, choice.2⟩, ?_⟩
  exact HistoryWordStepRun.write_recorded L (step) (rig) y u seedCount arc family trees orig pointer tag₀ post b
    real actual.childOrder B rom W levels fee paidMem positive wordFee paid resource margin age nr list
    (by omega) listRoom halfRoom sector lib.cap (fun _ _ _ _=>by rw [lib.motifs];decide) before
    current entryRows nodes charges children tags later ticks run records info frame price choice.2
    (by simpa only [stageAddress,kptr,head] using headerFits) oldD shape pub vals idx index same

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
include ledger in
/-- The cache-writing projection used by the original receiver. -/
theorem write_occurrence {fee levels degree : ℕ} {paidMem : ℕ→ℕ}
    (supported : B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (saved : SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (bounds : RefreshBounds heads q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
    (arrays : RecordedArrayBounds W heads q.cursor q.input) (ord : q.input.OrderedHalves L)
    (paid : q.move.ResourceReceipt fee levels (2^((3*u^10+4)/5)) b paidMem L (q.wordStep L) q.old q.charge q.step)
    (unit : B.archiveUnit u B.localCoefficient degree≤b.unitWork) (positive : 0<b.unitWork)
    (age : 40≤u) (threshold : B.archiveConstant B.localCoefficient≤u)
    (index : idx.val=node) (nr : node<V^2)
    (nodes : b.nodes=base u 44) (charges : b.charges=base u 43)
    (headsHigh : base u 19≤heads) (limit : q.entry.next.heap≤heapEnd)
    (romHigh : base u 19≤rom) (romFit : rom+libraryWords B W<2^W)
    (resident : Mounted B W W rom initial)
    (retained : ∀ i,(q.cursor.header≤ i ∧ i<q.entry.next.header ∨ heads≤ i)→i<q.entry.next.heap→initial i=final i)
    (row : DirectoryRow b q.step.sites.layer (q.step.sites.ord y) initial)
    (pred : DirectoryRow b q.old.layer (q.old.ord child) initial)
    (oldHalf : State.HalfRows q.old safe (numeric initial))
    (entryRows : StageRows L (step) (rig) y u b before)
    (listRoom : (rig).sites.layer.children+(rank₀).val*(rig).sites.layer.childCount<2^W)
    (halfRoom : (rig).sites.layer.incident+(rank₀).val*2<2^W)
    (external : (step).words.ext y<2^W)
    (children : ∀i : Fin (rig).sites.layer.childCount,(childN i).Cached tag₀ u ((rig).data.child rank₀ i) before)
    (wordFee : (W+1)^3≤fee)
    (later : seedCount≤node) (shape : TraceBucketAtom.Layout) (pub : Fin TraceEndpointROM.params→Word W)
    (margin : 10*(levels+2)^2*fee≤b.unitWork)
    (resource : Run.PricedAt b paidMem fee levels (2^((3*u^10+4)/5)) node
      (Run.nodeOfSite (step).words ((step).nextForest trees) (Run.pushedOrigin (step) orig) y))
    (same : vals idx=NodeValue.ofSite (Run.nodeOfSite (step).words ((step).nextForest trees)
      (Run.pushedOrigin (step) orig) y) pointer (streamAt u seedCount node) (endsAt u seedCount node)) :
    let arm:=fun i : Fin n=>B.nativeArmTime levels fee b paidMem i.val
    CacheWrite arc shape pub (families B rom W) vals tag₀ (B.nativeVisitCost levels fee b paidMem)
      arm (fun i _=>arm i) idx before := by
  apply And.right
  exact write_occurrence_with_selection
    (q:=q) (B:=B) (L:=L) (y:=y) (b:=b) (ledger:=ledger) (seedCount:=seedCount) (trees:=trees)
    (orig:=orig) (pointer:=pointer)
    supported saved bounds arrays ord paid unit positive age
    threshold index nr nodes charges headsHigh limit romHigh romFit
    resident retained row pred oldHalf entryRows listRoom halfRoom external
    children wordFee later shape pub margin resource same


end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

end OAI
