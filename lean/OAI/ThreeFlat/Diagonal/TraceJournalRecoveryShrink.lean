import OAI.ThreeFlat.Diagonal.TraceJournalRecoveryGoal
import OAI.Hierarchy.TraceShrinkArchive

namespace OAI
/-! # Recover the selected shrink row and continue through the original tail -/
namespace ThreeFlat.Diagonal.NavigationPass.TraceRecovery
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open PhysicalStage PhysicalStage.Run NavigationDirectory HistoryContraction CompressorPacking Native
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F]

open private recoverJoinedStage from OAI.ThreeFlat.Diagonal.TraceJournalRecoveryGoal

variable {a : Archive} {W limit Z tariff H MCap : ℕ} {cur ctr : Word W}
    {«protected» : ℕ→Prop} {initial : Layer→Prop}
open Native.ShrinkStage Native.ShrinkStage.Resident PhysicalShrink
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3200000 in
theorem recoverShrink (s t : ℕ) (G : ShrinkMotif.Table F)
      (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/2^t ≤ 1/1024)
      (tail : Program F t)
    (ih : RecoveryFor (a:=a) (limit:=limit) (cur:=cur) (ctr:=ctr) Z tariff «protected» H MCap initial tail)
    (room : Hierarchy.TraceRetainedRoom.Room limit W) (wide : 8≤W) (controls : cur.val<ctr.val) :
    RecoveryFor (a:=a) (limit:=limit) (cur:=cur) (ctr:=ctr) Z tariff «protected» H MCap initial (.shrink s t G small tail) := by
  intro bounds costs rem X reach c raw input final journal old num first data seed space
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
  rw [shape] at space
  conv => arg 7; rw [shape]
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
  let following := tail.directory rem (Fintype.card (R.next j).Base)
  have stageSpace : JournalSpace a.K W H MCap (op::following) c old.layer «protected» := space
  have here := JournalSpace.local (K:=a.K) (W:=W) (op:=op) (ops:=following) stageSpace
  obtain ⟨row,numbered,lay,ptr,reads,below,foot,parents,paddr,nHalf,nMotif,_⟩:=
    Hierarchy.TraceShrinkRetained.archive (K:=a.K) (W:=W) (q:=limit) G s (2^t) b (Nat.two_pow_pos _) ok B room wide cur mid out c j actual
      localRoom.fixed localRoom.volume localRoom.wire localRoom.width here.1
      old' (numbered_castSites e X old num) first
  have caps:=stageSpace.caps op (List.mem_cons_self ..)
  have source:=rows_of_one_stage R j old' row data op c tail rem (R.next j) _ cont «protected» seed
    controls stageSpace.header localRoom.heap here.2 reads foot parents paddr
    (fun k=>⟨(nHalf k).trans caps.1,(nMotif k).trans caps.2⟩)
  have tailSpace := stageSpace.tail
  rw [←lay] at tailSpace
  have succFirst : row.sites.layer.first=(allocate a.K c op).next.node := by rw [lay];rfl
  have tailRun := ih bs cs (rem:=rem) (X:=R.next j) (ce.2 j) (allocate a.K c op).next
    (raw.drop (Q.record fit).width) cont row.sites numbered succFirst row.data (Or.inr source.1) tailSpace
  have parsed : record.1.read (raw.take record.1.width)=some j := by
    change (Q.record fit).read (raw.take (Q.record fit).width)=some j
    exact hit
  let stageResult := stagePost a.K (op::following) c old.layer «protected»
    (fun i=>(final i).val) H MCap initial
  let pricedRow : R.ArchiveStep j old' (charges.1 j) := row
  have joined := recoverJoinedStage R next record charges old' data raw j parsed pricedRow
    (K:=a.K) (op:=op) (ops:=following) (c:=c) succFirst ptr lay source.2 tailRun
  exact recovered_recast e X (.step R next) stepTable certificate old data raw stageResult joined


end
end ThreeFlat.Diagonal.NavigationPass.TraceRecovery

end OAI
