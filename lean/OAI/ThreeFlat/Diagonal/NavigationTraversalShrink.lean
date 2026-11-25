import OAI.ThreeFlat.Diagonal.NavigationTraversalCore

namespace OAI
namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows RAM.PhysicalProcedure PhysicalStage
open CompressorPacking Native NavigationDirectory HistoryContraction
open Native.ShrinkStage Native.ShrinkStage.Resident PhysicalShrink
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]
open private castSites numbered_castSites recovered_recast prepend_recovered recordedAtStage rows_of_one_stage
  saved_after cursor_monotone extend_stagePost JournalSpace.tail JournalSpace.local interleave
  from OAI.ThreeFlat.Diagonal.NavigationTraversalCore
variable {a : Archive} {u Z tariff H MCap : ℕ} {cur ctr : Word (16*u^10)}
  {«protected» : ℕ → Prop} {allow : StaticMotif F → Prop}
set_option maxRecDepth 10000 in
set_option maxHeartbeats 6400000 in
theorem recoverWordShrink (s t : ℕ) (G : ShrinkMotif.Table F)
      (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/2^t ≤ 1/1024)
      (tail : Program F t)
    (ih : WordRecoveryFor (a:=a) (u:=u) (cur:=cur) (ctr:=ctr) Z tariff «protected» H MCap allow tail) (age : 40≤u) (controls : cur.val<ctr.val) :
    WordRecoveryFor (a:=a) (u:=u) (cur:=cur) (ctr:=ctr) Z tariff «protected» H MCap allow (.shrink s t G small tail) := by
  intro bounds costs rem X reach c raw input final journal old num first data seed space support headerDense headerStart denseStart
  let b:=tail.charge+rem
  let e:=Nat.add_assoc (shrinkCharge s) tail.charge rem
  let B : State (2^s) (shrinkCharge s+b):=e ▸ X
  let ok : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/(2^t:ℕ)≤1/1024 := by exact_mod_cast small
  let R:=shrinkBinary G s (2^t) b (Nat.two_pow_pos _) ok B
  let next:=fun j=>tail.run rem (R.next j)
  let Q:=shrinkBinaryFamily G s (2^t) b (Nat.two_pow_pos _) ok B
  let old' := castSites e X old
  let op:=Stage.shrink (dims (shrinkStage s (2^t)) (Fintype.card (shrinkRecordState s b B).Base) (CompressorPacking.tagBits (2^s)) b)
  rcases journal with ⟨mid,out,fit,j,boot,hit,shape,localRoom,⟨oldArrays,oldStored⟩,actual,cont⟩
  rw [shape] at space headerDense
  conv => arg 7; rw [shape]
  conv => arg 9; rw [shape]
  conv => arg 10; rw [shape]
  let following := tail.directory rem (Fintype.card (R.next j).Base)
  let destination := (allocate a.K c op).next
  let endpoint := finish a.K following destination
  have heapRoom : destination.heap ≤ endpoint.heap := by
    change destination.heap ≤ (finish a.K following destination).heap
    rw [heap_finish]
    exact Nat.le_add_right ..
  have stageSpace : JournalSpace a.K (16*u^10) H MCap (op::following) c old.layer «protected» := space
  have here := JournalSpace.local (K:=a.K) (W:=(16*u^10)) (op:=op) (ops:=following) stageSpace
  change (finish a.K (op::following) c).header ≤ a.cursor.dense at headerDense
  have recordCaps := shrinkNativeCaps_at_scale G s (2^t) b (Nat.two_pow_pos _) ok B age localRoom.fixed localRoom.volume localRoom.wire
  have arrays : RecordedArrayBounds (16*u^10) (finish a.K (op::tail.directory rem (Fintype.card (R.next j).Base)) c).header c B :=
    recordedAtStage (X:=B) op _ oldArrays headerDense headerStart denseStart localRoom.width localRoom.wire
  let ce : (Run.step R next).WidthCeiling Z:=Program.beforeRecast e X _ reach
  let bs : ∀ n∈tail.recordBounds,n.1≤a.K ∧ n.2*Z<2^(16*u^10) := fun n hn=>bounds n (List.mem_cons_of_mem _ hn)
  let cs : ∀ n∈tail.factors,n≤tariff := fun n hn=>costs n (List.mem_cons_of_mem _ hn)
  let record : (Run.step R next).Records :=
    ⟨Q.record fit,fun k=>(tail.table a.K (16*u^10) Z bs rem (R.next k) (ce.2 k)).records⟩
  have bv : Fintype.card B.Base=Fintype.card X.Base := Program.baseCast e X
  let qt := fun term => tail.table a.K (16*u^10) Z bs rem (R.next term) (ce.2 term)
  let stepTable : Program.RecordTable (.step R next) a.K (16*u^10)
      (((Program.shrink s t G small tail).directory rem (Fintype.card X.Base)).map Stage.motifs) := by
    apply Program.consTable R next Q fit
    · dsimp only [Q]
      rw [shrinkBinaryFamily_motifs,bv]
      rfl
    · intro term
      exact (qt term).changeSizes (by dsimp only [R]; rw [shrinkBinary_next_base,bv])
  let fee := shrinkBinaryCharge G s (2^t) b (Nat.two_pow_pos _) ok B
  let nativeCharge : Program.siteCharge R tariff :=
    ⟨fee,fun term => (shrinkBinaryCharge_sum G s (2^t) b (Nat.two_pow_pos _) ok B term).trans
      (Nat.mul_le_mul_right _ (costs _ (List.mem_cons_self ..)))⟩
  let certificate : Program.Certified (.step R next) tariff :=
    Program.consCert R next nativeCharge (fun term => tail.certifiedCharges tariff cs rem (R.next term))
  let charges : (Run.step R next).Charges := certificate.1
  let assembly (Pins : Type) : (Run.step R next).Assembler Pins :=
    Run.assembleStep R next (shrinkBinary_assembler (Pins:=Pins) G s (2^t) b (Nat.two_pow_pos _) ok B)
      (fun k => tail.assembly (Pins:=Pins) rem (R.next k))
  let visit (Pins : Type) : Run.WordVisit F Pins := RecordedWordStep a.K cur ctr endpoint.header endpoint.heap final Pins allow
  let visits : Move.VisitPredicate F := RecordedStep a.K cur ctr endpoint.header endpoint.heap final
  let stageResult := stagePost a.K (op::following) c old.layer «protected» (fun i=>(final i).val) H MCap
  obtain ⟨row,numbered,lay,ptr,reads,below,foot,parents,paddr,nHalf,nMotif,⟨siteOrder,nativeRow⟩⟩:=
    shrink_archive_step_at_scale G s (2^t) b (Nat.two_pow_pos _) ok B age cur mid out c j actual
      localRoom.fixed localRoom.volume localRoom.wire localRoom.width here.1
      old' (numbered_castSites e X old num) first
  have issuedHalves := shrink_half_rows_at_scale (K:=a.K) G s (2^t) b (Nat.two_pow_pos _) ok B age cur mid out c j actual
    localRoom.fixed localRoom.volume localRoom.wire
  have memoryAgrees (i : ℕ) (hi : c.heap ≤ i ∧ i < destination.heap) :
      (final i).val=(out i).val := congrArg Fin.val
    (Archive.Journal.frame tail rem (R.next j) destination _ cont
      (ne_of_lt (hi.2.trans_le localRoom.heap)) (ne_of_lt ((hi.2.trans_le localRoom.heap).trans controls))
      ⟨Or.inr (stageSpace.header.trans hi.1),Or.inl hi.2⟩)
  have inside (i : ℕ) (hi : c.heap ≤ i ∧ i < destination.heap) :
      endpoint.header ≤ i ∧ i < endpoint.heap :=
    ⟨stageSpace.header.trans hi.1,hi.2.trans_le heapRoom⟩
  have finalHalves : State.HalfRows row.sites (fun i=>endpoint.header ≤ i ∧ i < endpoint.heap)
      (fun i=>(final i).val) := by
    rw [nativeRow]
    exact issuedHalves.transfer memoryAgrees inside
  have finalData : row.data.Reads (fun i=>(final i).val) ∧
      row.data.Footprint (fun i=>endpoint.header ≤ i ∧ i < endpoint.heap) (fun i=>(final i).val) :=
    ⟨reads.of_footprint foot memoryAgrees,(foot.transfer foot memoryAgrees).mono inside⟩
  have nativeWord (Pins : Type) (L : B.Words Pins) :
      ShrinkWordVisit a.K cur ctr endpoint.header endpoint.heap final allow R j L
        (shrinkBinary_assembler G s (2^t) b (Nat.two_pow_pos _) ok B L j) old' (fee j) row :=
    ShrinkWordVisit.of_native (Pins:=Pins) (W:=16*u^10) (K:=a.K) (cur:=cur) (ctr:=ctr)
      (headerEnd:=endpoint.header) (heapEnd:=endpoint.heap) (final:=final) (allow:=allow)
      (T:=G) (s:=s) (D:=2^t) (rem:=b) (hD:=Nat.two_pow_pos _) (small:=ok)
      (A:=B) (c:=c) (b:=j) (mid:=mid) (out:=out) (raw:=raw) (old:=old') (L₀:=L) (row:=row)
      fit hit oldStored arrays recordCaps actual siteOrder (numbered_castSites e X old num)
      first nativeRow finalHalves (saved_after tail rem (R.next j) destination _ cont) heapRoom support.1 finalData
  have caps:=stageSpace.caps op (List.mem_cons_self ..)
  have source:=rows_of_one_stage R j old' row data op c tail rem (R.next j) _ cont «protected» seed
    controls stageSpace.header localRoom.heap here.2 reads foot parents paddr
    (fun k=>⟨(nHalf k).trans caps.1,(nMotif k).trans caps.2⟩)
  have tailSpace := JournalSpace.tail (op:=op) (ops:=following) stageSpace
  rw [←lay] at tailSpace
  have succFirst : row.sites.layer.first=(allocate a.K c op).next.node := by rw [lay];rfl
  have tailRun := ih bs cs (rem:=rem) (X:=R.next j) (ce.2 j) (allocate a.K c op).next
    (raw.drop (Q.record fit).width) cont row.sites numbered succFirst row.data source.1 tailSpace support.2 headerDense
    (headerStart.trans (cursor_monotone a.K c op).1) (denseStart.trans (cursor_monotone a.K c op).2)
  have parsed : record.1.read (raw.take record.1.width)=some j := by
    change (Q.record fit).read (raw.take (Q.record fit).width)=some j
    exact hit
  let pricedRow : R.ArchiveStep j old' (charges.1 j) := row
  apply recovered_recast e X (.step R next) stepTable certificate old data raw visits assembly visit stageResult
  apply prepend_recovered R next record charges old' data raw visits assembly visit stageResult j parsed pricedRow
  · exact Or.inl ((nativeWord Unit (State.halfWords B Unit)).erase)
  · intro Pins L
    exact Or.inl (nativeWord Pins L)
  obtain ⟨h,suffix,p,parse,finalNum,seen,wordSeen,post⟩:=tailRun
  refine ⟨h,suffix,p,parse,finalNum,seen,wordSeen,extend_stagePost rfl ?_ lay source.2 post⟩
  change Parent.mk false row.sites.layer.first row.ownerPtr = _
  rw [succFirst,ptr]

end
end ThreeFlat.Diagonal.NavigationPass

end OAI
