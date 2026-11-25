import OAI.ThreeFlat.Diagonal.TraceJournalWordRecoveryCore

namespace OAI
/-! # Recovering the recorded shrink word from its selected RAM stage -/

namespace ThreeFlat.Diagonal.NavigationPass.TraceWordRecovery
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open PhysicalStage PhysicalStage.Run NavigationDirectory HistoryContraction CompressorPacking Native
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F]

open private saved prepend monotone from OAI.ThreeFlat.Diagonal.TraceJournalWordRecoveryCore

variable {a : Archive} {W limit Z tariff H MCap : ℕ} {cur ctr : Word W}
    {«protected» : ℕ→Prop} {initial : Layer→Prop} {allow : StaticMotif F→Prop}
open Native.ShrinkStage Native.ShrinkStage.Resident PhysicalShrink
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3200000 in
theorem recoverShrinkWords (s t : ℕ) (G : ShrinkMotif.Table F)
      (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/2^t ≤ 1/1024)
      (tail : Program F t)
    (ih : WordRecoveryFor (a:=a) (limit:=limit) (cur:=cur) (ctr:=ctr) Z tariff «protected» H MCap initial allow tail)
    (room : Hierarchy.TraceRetainedRoom.Room limit W) (wide : 8≤W) (controls : cur.val<ctr.val)
    (wireBase : limit ≤ 2^(W/16)) :
    WordRecoveryFor (a:=a) (limit:=limit) (cur:=cur) (ctr:=ctr) Z tariff «protected» H MCap initial allow (.shrink s t G small tail) := by
  intro bounds costs rem X reach c raw input final journal old num first data seed space support headerDense headerStart denseStart
  let b:=tail.charge+rem
  let e:=Nat.add_assoc (shrinkCharge s) tail.charge rem
  let B : State (2^s) (shrinkCharge s+b):=e ▸ X
  let ok : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/(2^t:ℕ)≤1/1024 := by exact_mod_cast small
  let R:=shrinkBinary G s (2^t) b (Nat.two_pow_pos _) ok B
  let next:=fun j=>tail.run rem (R.next j)
  let Q:=shrinkBinaryFamily G s (2^t) b (Nat.two_pow_pos _) ok B
  let old' := TraceRecovery.castSites e X old
  let op:=Stage.shrink (dims (shrinkStage s (2^t)) (Fintype.card (shrinkRecordState s b B).Base) (CompressorPacking.tagBits (2^s)) b)
  rcases journal with ⟨mid,out,fit,j,boot,hit,shape,localRoom,⟨oldArrays,oldStored⟩,actual,cont⟩
  rw [shape] at space headerDense
  conv => arg 8; rw [shape]
  conv => arg 9; rw [shape]
  let following := tail.directory rem (Fintype.card (R.next j).Base)
  let destination := (allocate a.K c op).next
  let endpoint := finish a.K following destination
  have heapReach : destination.heap ≤ endpoint.heap := by
    change destination.heap ≤ (finish a.K following destination).heap
    rw [heap_finish]
    exact Nat.le_add_right _ _
  have stageSpace : TraceRecovery.JournalSpace a.K W H MCap (op::following) c old.layer «protected» := space
  have here := TraceRecovery.JournalSpace.local (K:=a.K) (W:=W) (op:=op) (ops:=following) stageSpace
  have recordCaps := Hierarchy.TraceShrinkWordVisitData.caps G s (2^t) b
    (Nat.two_pow_pos _) ok B room localRoom.fixed localRoom.volume localRoom.wire
  change (finish a.K (op::following) c).header ≤ a.cursor.dense at headerDense
  have arrays : RecordedArrayBounds W (finish a.K (op::following) c).header c B :=
    { toOldArrayBounds := OldArrayBounds.lower (lo:=(finish a.K (op::following) c).header)
        (hi:=a.cursor.dense) (c:=c) (X:=B) oldArrays headerDense
      headerLow:=headerStart
      denseLow:=headerDense.trans denseStart
      headerDense:=by
        have h:=headerDense.trans denseStart
        rw [NavigationDirectory.header_finish] at h
        simp only [List.length_cons] at h
        omega
      widthPos:=localRoom.width
      wire:=localRoom.wire.trans (Nat.pow_le_pow_left wireBase _) }
  let ce : (Run.step R next).WidthCeiling Z:=Program.beforeRecast e X _ reach
  let bs : ∀ n∈tail.recordBounds,n.1≤a.K ∧ n.2*Z<2^W := fun n hn=>bounds n (List.mem_cons_of_mem _ hn)
  let cs : ∀ n∈tail.factors,n≤tariff := fun n hn=>costs n (List.mem_cons_of_mem _ hn)
  let record : (Run.step R next).Records :=
    ⟨Q.record fit,fun k=>(tail.table a.K W Z bs rem (R.next k) (ce.2 k)).records⟩
  have bv : Fintype.card B.Base=Fintype.card X.Base := Program.baseCast e X
  let qt := fun term => tail.table a.K W Z bs rem (R.next term) (ce.2 term)
  let stepTable : Program.RecordTable (.step R next) a.K W
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
  let stageResult := TraceRecovery.stagePost a.K (op::following) c old.layer «protected»
    (fun i=>(final i).val) H MCap initial
  obtain ⟨row,numbered,lay,ptr,reads,below,foot,parents,paddr,nHalf,nMotif,⟨siteOrder,nativeRow⟩⟩:=
    Hierarchy.TraceShrinkRetained.archive (K:=a.K) (W:=W) (q:=limit) G s (2^t) b (Nat.two_pow_pos _) ok B room wide cur mid out c j actual
      localRoom.fixed localRoom.volume localRoom.wire localRoom.width here.1
      old' (TraceRecovery.numbered_castSites e X old num) first
  have issuedHalves := Hierarchy.TraceShrinkWordVisitData.halfRows (K:=a.K) G s (2^t) b (Nat.two_pow_pos _) ok B room cur mid out c j actual
    localRoom.fixed localRoom.volume localRoom.wire
  have memoryAgrees (i : ℕ) (hi : c.heap ≤ i ∧ i < destination.heap) :
      (final i).val=(out i).val := congrArg Fin.val
    (Archive.TraceJournal.frame tail rem (R.next j) destination _ cont
      (ne_of_lt (hi.2.trans_le localRoom.heap)) (ne_of_lt ((hi.2.trans_le localRoom.heap).trans controls))
      ⟨Or.inr (stageSpace.header.trans hi.1),Or.inl hi.2⟩)
  have inside (i : ℕ) (hi : c.heap ≤ i ∧ i < destination.heap) :
      endpoint.header ≤ i ∧ i < endpoint.heap :=
    ⟨stageSpace.header.trans hi.1,hi.2.trans_le heapReach⟩
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
    ShrinkWordVisit.of_native (Pins:=Pins) (W:=W) (K:=a.K) (cur:=cur) (ctr:=ctr)
      (headerEnd:=endpoint.header) (heapEnd:=endpoint.heap) (final:=final) (allow:=allow)
      (T:=G) (s:=s) (D:=2^t) (rem:=b) (hD:=Nat.two_pow_pos _) (small:=ok)
      (A:=B) (c:=c) (b:=j) (mid:=mid) (out:=out) (raw:=raw) (old:=old') (L₀:=L) (row:=row)
      fit hit oldStored arrays recordCaps actual siteOrder (TraceRecovery.numbered_castSites e X old num)
      first nativeRow finalHalves (saved tail rem (R.next j) destination _ cont) heapReach support.1 finalData
  have caps:=stageSpace.caps op (List.mem_cons_self ..)
  have source:=TraceRecovery.rows_of_one_stage R j old' row data op c tail rem (R.next j) _ cont «protected» seed
    controls stageSpace.header localRoom.heap here.2 reads foot parents paddr
    (fun k=>⟨(nHalf k).trans caps.1,(nMotif k).trans caps.2⟩)
  have tailSpace := stageSpace.tail
  rw [←lay] at tailSpace
  have succFirst : row.sites.layer.first=(allocate a.K c op).next.node := by rw [lay];rfl
  have tailRun := ih bs cs (rem:=rem) (X:=R.next j) (ce.2 j) (allocate a.K c op).next
    (raw.drop (Q.record fit).width) cont row.sites numbered succFirst row.data (Or.inr source.1) tailSpace support.2 headerDense
    (headerStart.trans (monotone a.K c op).1) (denseStart.trans (monotone a.K c op).2)
  have parsed : record.1.read (raw.take record.1.width)=some j := by
    change (Q.record fit).read (raw.take (Q.record fit).width)=some j
    exact hit
  let pricedRow : R.ArchiveStep j old' (charges.1 j) := row
  apply recast e X (.step R next) stepTable certificate old data raw assembly visit stageResult
  apply prepend R next record charges old' data raw assembly visit stageResult j parsed pricedRow
  · intro Pins L
    exact Or.inl (nativeWord Pins L)
  · obtain ⟨h,suffix,p,parse,finalNum,wordSeen,post⟩:=tailRun
    refine ⟨h,suffix,p,parse,finalNum,wordSeen,?_⟩
    apply TraceRecovery.extend_stagePost rfl _ lay source.2 post
    change Parent.mk _ row.sites.layer.first row.ownerPtr=_
    rw [succFirst,ptr]


end
end ThreeFlat.Diagonal.NavigationPass.TraceWordRecovery

end OAI
