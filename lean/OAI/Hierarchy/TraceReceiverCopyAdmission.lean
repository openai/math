import OAI.ThreeFlat.Diagonal.TraceReceiverNodeCopy
import OAI.ThreeFlat.Diagonal.TraceArchiveExtent
import OAI.ThreeFlat.Diagonal.PhysicalBlockLength
import OAI.ThreeFlat.Diagonal.PhysicalBlockTreeSize
import OAI.ThreeFlat.Diagonal.ProgramDirectory
import OAI.Hierarchy.TraceRecordScale

namespace OAI
/-! # All S44 words in a selected receiver history fit the startup clock -/

namespace Hierarchy.TraceAdmission
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open NavigationPass NavigationDirectory NodePublication RAM RAM.NavigationNodeRows
open Computability.VPVNP.BurstRAM PrivateRAM TraceDistribution Filter
noncomputable section
variable {F : Type} [Field F] (B : Block F)

/-- The copy operand is the extent of the fixed structural directory, independently of
every raw control bit, owned endpoint, and selected histogram. -/
def receiverDirectoryCount (K : ℕ) (ops : List Stage) (c : Cursor) (seed : Layer) :=
  let last:=TraceRecovery.lastLayer K ops c seed
  last.first+last.count

theorem receiver_count_eq {K ops c seed «protected» m H M initial xs last}
    (seen : TraceRecovery.stagePost K ops c seed «protected» m H M initial xs last) :
    last.first+last.count=receiverDirectoryCount K ops c seed := by
  exact congrArg (fun row : Layer => row.first+row.count) seen.2.1

/-- Budget for the entire fixed receiver publication, with no history quantified in its code. -/
theorem eventual_receiver_directory_count {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ (k : ℕ) (_axes : k=u w+1-w/2) (_fits : B.blockCharge*s w≤k)
      (K : ℕ) (c : Cursor) (seed : Layer) (_zero : c.node=0) (_first : seed.first=c.node)
      (_size : seed.count=k*2^k),
      let P:=B.repeat (s w)
      let ops:=P.directory (k-P.charge) k
      receiverDirectoryCount K ops c seed ≤ 2^(3*w/5) := by
  let rate:=(B.levels+1)*B.allocations.sum
  filter_upwards [record_room scale (rate+1)] with w bound
  intro k axes fits K c seed zero first size P ops
  have split : P.charge+(k-P.charge)=k := by
    have h : P.charge≤k := by simpa only [P,B.charge_repeat] using fits
    omega
  have heap:=P.allocation_words B.allocations.sum (B.allocation_bound (s w)) (k-P.charge) k
  rw [split,show P.length=(B.levels+1)*s w from B.length_repeat (s w)] at heap
  let last:=TraceRecovery.lastLayer K ops c seed
  obtain ⟨q,hit,e⟩:=TraceRecovery.lastLayer_mem K ops c seed
  have span:=actual_span K ops c seed first q hit
  rw [e,zero,size,Nat.zero_add] at span
  rw [←axes] at bound
  have p := Nat.le_mul_of_pos_right ((rate+1)*(s w+1)*(1+k*2^k)) (by omega : 0<64*w+1)
  have major : 1+(B.levels+1)*s w*B.allocations.sum≤(rate+1)*(s w+1) := by
    dsimp only [rate]
    ring_nf
    omega
  calc
    last.first+last.count ≤ k*2^k+(ops.map Stage.heapWords).sum := span
    _ ≤ (1+(B.levels+1)*s w*B.allocations.sum)*(1+k*2^k) := by
      change (ops.map Stage.heapWords).sum≤_ at heap
      rw [Nat.add_mul,Nat.one_mul]
      omega
    _ ≤ (rate+1)*(s w+1)*(1+k*2^k) := Nat.mul_le_mul_right _ major
    _ ≤ _ := p.trans bound

/-- The same static copy holds all the concrete members of a genuinely mounted history. -/
theorem eventual_receiver_node_count {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ (k : ℕ) (_axes : k=u w+1-w/2) (_fits : B.blockCharge*s w≤k)
      (K : ℕ) (c : Cursor) (seed : Layer) (_zero : c.node=0) (_first : seed.first=c.node)
      (_size : seed.count=k*2^k),
      let P:=B.repeat (s w)
      let ops:=P.directory (k-P.charge) k
      ∀ {«protected» : ℕ→Prop} {m : ℕ→ℕ} {H M : ℕ} {initial : Layer→Prop}
        {xs : List NodeRow} {last : Layer}, TraceRecovery.stagePost K ops c seed «protected» m H M initial xs last →
        last.first+last.count≤2^(3*w/5) := by
  filter_upwards [eventual_receiver_directory_count B scale] with w bound
  intro k axes fits K c seed zero first size P ops «protected» m H M initial xs last seen
  rw [receiver_count_eq seen]
  exact bound k axes fits K c seed zero first size


end
end Hierarchy.TraceAdmission

end OAI
