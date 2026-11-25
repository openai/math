import OAI.ThreeFlat.Diagonal.NavigationTraversalCore

namespace OAI
namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows RAM.PhysicalProcedure PhysicalStage
open CompressorPacking Native NavigationDirectory HistoryContraction
open Native.ShrinkStage Native.ShrinkStage.Resident PhysicalShrink
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F]
open private castSites numbered_castSites recovered_recast prepend_recovered recordedAtStage rows_of_one_stage
  saved_after cursor_monotone extend_stagePost JournalSpace.tail JournalSpace.local interleave
  from OAI.ThreeFlat.Diagonal.NavigationTraversalCore
variable {a : Archive} {u Z tariff H MCap : ℕ} {cur ctr : Word (16*u^10)}
  {«protected» : ℕ → Prop} {allow : StaticMotif F → Prop}
open Expander
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3200000 in
theorem recoverWordRefresh (s t h pad : ℕ) (g : Fin (2^s) → Fin (2^s) → ℕ) (γ cost : ℝ)
      (G : RefreshMotif.Table F g (1+h+pad) cost) (hm : 2≤2^s) (hh : 0<h)
      (sym : ∀ i j,g i j=g j i) (rows : ∀ i, ∑ j,g i j=h) (zero : ∀ i,g i i=0)
      (conn : Bound (transition g h) ℝ γ) (degree : 1+h+pad=2^t) (tail : Program F t)
    (ih : WordRecoveryFor (a:=a) (u:=u) (cur:=cur) (ctr:=ctr) Z tariff «protected» H MCap allow tail) (_age : 40≤u) (controls : cur.val<ctr.val) :
    WordRecoveryFor (a:=a) (u:=u) (cur:=cur) (ctr:=ctr) Z tariff «protected» H MCap allow (.refresh s t h pad g γ cost G hm hh sym rows zero conn degree tail) := by
  intro bounds costs rem X reach c raw input final journal old num first data seed space support headerDense headerStart denseStart
  let b:=tail.charge+rem
  let e:=Nat.add_assoc s tail.charge rem
  let B : State (2^s) (s+b):=e ▸ X
  let R:=refreshBinary G B hm hh sym rows zero conn
  let R':=Program.recastMove degree R
  let next:=fun j=>tail.run rem (R'.next j)
  let Q:=refreshBinaryFamily G B hm hh sym rows zero conn
  let old' := castSites e X old
  let op:=Stage.refresh (Fintype.card B.Base) (2^s) (2^b) h pad
  rcases journal with ⟨mid,out,fit,j,boot,hit,shape,localRoom,⟨oldArrays,oldStored⟩,actual,published,frame,cont⟩
  rw [shape] at space headerDense
  conv => arg 7; rw [shape]
  conv => arg 9; rw [shape]
  conv => arg 10; rw [shape]
  let k := Program.degreeTerm degree R j
  have arrays : RecordedArrayBounds (16*u^10) (finish a.K (op::tail.directory rem (Fintype.card (R'.next k).Base)) c).header c B :=
    recordedAtStage (X:=B) op _ oldArrays headerDense headerStart denseStart localRoom.width localRoom.wire
  let ce : (Run.step R' next).WidthCeiling Z := Program.beforeRecast e X _ reach
  let bs : ∀ n∈tail.recordBounds,n.1≤a.K ∧ n.2*Z<2^(16*u^10) := fun n hn=>bounds n (List.mem_cons_of_mem _ hn)
  let cs : ∀ n∈tail.factors,n≤tariff := fun n hn=>costs n (List.mem_cons_of_mem _ hn)
  let transported:=Program.degreeFamily degree R (Fintype.card B.Base*2^b) (Fintype.card B.Base*2^s) Q fit
    rfl (refreshBinary_next_base G B hm hh sym rows zero conn)
  have baseCard : Fintype.card B.Base=Fintype.card X.Base := Program.baseCast e X
  let nextTables := fun z => tail.table a.K (16*u^10) Z bs rem (R'.next z) (ce.2 z)
  let stepTable : Program.RecordTable (Run.step R' next) a.K (16*u^10)
      ((Fintype.card X.Base*2^b)::(tail.directory rem (Fintype.card X.Base*2^s)).map Stage.motifs) :=
    Program.consTable R' next transported.1 transported.2.1
      (transported.2.2.1.trans (congrArg (fun card => card*2^b) baseCard))
      (fun z => (nextTables z).changeSizes (congrArg (fun card => (tail.directory rem card).map Stage.motifs)
        ((transported.2.2.2 z).trans (congrArg (fun card => card*2^s) baseCard))))
  let record : (Run.step R' next).Records :=
    ⟨transported.1.record transported.2.1,fun z=>(tail.table a.K (16*u^10) Z bs rem (R'.next z) (ce.2 z)).records⟩
  have selected : record.1.read (raw.take record.1.width)=some k := by
    have eq := Program.degree_read degree R _ _ Q fit rfl (refreshBinary_next_base G B hm hh sym rows zero conn) raw
    exact eq.trans (by rw [hit];rfl)
  have wid : record.1.width=(Q.record fit).width := by
    change transported.1.motifs*a.K*(16*u^10)=Q.motifs*a.K*(16*u^10)
    rw [transported.2.2.1]; rfl
  have funding (z : Fin R.rules.count) := (refreshBinaryCharge_sum G B hm hh sym rows zero conn z).trans
      (Nat.mul_le_mul_right _ (costs _ (List.mem_cons_self ..)))
  let nativeCharge : Program.siteCharge R tariff :=
    ⟨refreshBinaryCharge G B hm hh sym rows zero conn, funding⟩
  let certificate : Program.Certified (Run.step R' next) tariff :=
    Program.consCert R' next (Program.siteRecast degree R nativeCharge)
      (fun z => tail.certifiedCharges tariff cs rem (R'.next z))
  let chosenAssembler (Pins : Type) : (Run.step R' next).Assembler Pins :=
    Run.assembleStep R' next
      (Move.outputAssembler degree R (refreshBinary_assembler G B hm hh sym rows zero conn))
      (fun z => tail.assembly (Pins:=Pins) rem (R'.next z))
  let following := tail.directory rem (Fintype.card (R'.next k).Base)
  have stageSpace : JournalSpace a.K (16*u^10) H MCap (op::following) c old.layer «protected» := space
  have here := JournalSpace.local (K:=a.K) (W:=16*u^10) (op:=op) (ops:=following) stageSpace
  have copies (i : Fin Q.motifs) : out (c.heap+i.val*3)=(Q.copies i:Word (16*u^10)) := by
    simpa only [Fin.val_zero, Nat.add_zero, eq_self, ite_true] using published.1 i 0
  obtain ⟨row,numbered,lay,ptr,reads,below,foot,parents,paddr,nSize,nativeRow⟩ :=
    refresh_archive_step_at_scale G B hm hh sym rows zero conn degree c cur j _ out actual fit copies
      (localRoom.heap.trans cur.isLt.le) here.1 old' (numbered_castSites e X old num) first funding
  have caps:=stageSpace.caps op (List.mem_cons_self ..)
  have source:=rows_of_one_stage R' k old' row data op c tail rem (R'.next k) _ cont «protected» seed
    controls stageSpace.header localRoom.heap here.2 reads foot parents paddr
    (fun i=>⟨(nSize i).1.trans caps.1,(nSize i).2.trans caps.2⟩)
  have tailSpace := JournalSpace.tail (K:=a.K) (op:=op) (ops:=following) stageSpace
  rw [←lay] at tailSpace
  have succFirst : row.sites.layer.first=(allocate a.K c op).next.node := by rw [lay];rfl
  have tailRun := ih bs cs (rem:=rem) (X:=R'.next k) (ce.2 k) (allocate a.K c op).next
    (raw.drop (Q.record fit).width) cont row.sites numbered succFirst row.data source.1 tailSpace support.2 headerDense
    (headerStart.trans (cursor_monotone a.K c op).1) (denseStart.trans (cursor_monotone a.K c op).2)
  let stop := finish a.K (op::following) c
  have localEnd : (allocate a.K c op).next.heap ≤ stop.heap := by
    change (allocate a.K c op).next.heap ≤ (finish a.K following (allocate a.K c op).next).heap
    rw [heap_finish]
    exact Nat.le_add_right ..
  let ordinary : Move.VisitPredicate F := RecordedStep (F:=F) a.K cur ctr stop.header stop.heap final
  let withWords (Pins : Type) : Run.WordVisit F Pins := RecordedWordStep (F:=F) a.K cur ctr stop.header stop.heap final Pins allow
  let post := stagePost a.K (op::following) c old.layer «protected» (fun i=>(final i).val) H MCap
  let pricedRow : R'.ArchiveStep k old' (certificate.1.1 k) := row
  apply recovered_recast e X (.step R' next) stepTable certificate old data raw ordinary chosenAssembler withWords post
  apply prepend_recovered R' next record certificate.1 old' data raw ordinary chosenAssembler withWords post k selected pricedRow
  · apply Or.inr
    exact RefreshVisit.of_native G B hm hh sym rows zero conn degree c cur ctr _ _ j mid out final old'
      (numbered_castSites e X old num) first oldStored arrays actual fit published.1 published.2.1 funding
      localEnd (saved_after tail rem (R'.next k) (allocate a.K c op).next _ cont)
      ⟨space.header,⟨localRoom.heap,controls⟩,(by simpa only [header_finish,List.length_cons,Program.directory_length] using published.2.2)⟩ row nativeRow
  · intro Pins L
    apply Or.inr
    exact RefreshWordVisit.of_native G B hm hh sym rows zero conn degree c cur ctr _ _ j mid out final old'
      (numbered_castSites e X old num) first oldStored arrays actual fit published.1 published.2.1 funding
      localEnd (saved_after tail rem (R'.next k) (allocate a.K c op).next _ cont)
      ⟨space.header,⟨localRoom.heap,controls⟩,(by simpa only [header_finish,List.length_cons,Program.directory_length] using published.2.2)⟩ row nativeRow L support.1
  rw [wid]
  obtain ⟨h',suffix,p,parse,finalNum,seen,wordSeen,post⟩:=tailRun
  refine ⟨h',suffix,p,parse,finalNum,seen,wordSeen,extend_stagePost rfl ?_ lay source.2 post⟩
  change Parent.mk false row.sites.layer.first row.ownerPtr=_
  rw [succFirst,ptr]

end
end ThreeFlat.Diagonal.NavigationPass

end OAI
