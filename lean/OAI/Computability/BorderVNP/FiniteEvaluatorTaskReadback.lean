import OAI.Computability.BorderVNP.FiniteEvaluatorCubeReadSet
import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsMemory
import OAI.Computability.BorderVNP.RoutingISATypedTaskMemory
import OAI.Computability.BorderVNP.CellPacketSupplementalBatchMemory

/-! # Finite cube words across the three physical task writers

The report counters follow the immutable cube deck. Report guesses occupy
the cell input banks, and supplemental descriptor patches occupy the earlier
sorted geometry. The typed task table follows the deck and publishes its
count at primary word 90. These addresses give exact readback of the earlier
cube operands after all three writes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.TaskReadback

open VPVNP.BurstRAM RoutingISA
open CellPacket.Supplement

variable {w n b h K s : ℕ} {F : Type*} [Fintype F]
variable (pub : Arg → Word w) (Y : CubePacket.Inputs n b h K s F)

/-- The three possible address regions of a lookup input in the actual allocation. -/
def located (frame packet cell deck stop addr : ℕ) : Prop :=
  (∃ j ∈ CubePacket.frameWords, addr=frame+j) ∨
  (packet ≤ addr ∧ addr < cell) ∨ (deck ≤ addr ∧ addr < stop)

/-- The task writers occupy the sorted geometry, received cell suffixes, and
post-deck work space at their actual source and output addresses. -/
structure Placement (pub : Arg → Word w) (Y : CubePacket.Inputs n b h K s F)
    (reports : Reports.Layout) (rows : List Reports.Row) (tasks : TypedTaskBuilder.Layout)
    (supp : ℕ → Batch.Cell) (count packet cell deck stop : ℕ) : Prop where
  frame : tasks.frame=(pub 0).val
  ordered : (pub 0).val+112 ≤ packet ∧ packet ≤ cell ∧ cell ≤ deck ∧ deck ≤ stop
  operands : ∀ a, CubePacket.ReadAt Y pub a → located (pub 0).val packet cell deck stop a
  reportCounts : stop ≤ reports.tails ∧ stop ≤ reports.counters
  reportBits : ∀ row∈rows, cell ≤ row.start ∧ row.start+row.bits.length ≤ deck
  outputs : stop ≤ tasks.calls ∧ stop ≤ tasks.tasks
  patch : ∀ i < count, (pub 0).val+112 ≤ (supp i).layout.tail ∧ (supp i).layout.tail+12 ≤ packet ∧ stop ≤ (supp i).layout.merged

variable {reports : Reports.Layout} {rows : List Reports.Row} {tasks : TypedTaskBuilder.Layout}
variable {supp : ℕ → Batch.Cell} {count packet cell deck stop : ℕ}
variable (placed : Placement pub Y reports rows tasks supp count packet cell deck stop)

omit [Fintype F] in
include placed in
/-- Every actual input word avoids the three report counters, the guessed tail,
the task writer, and all supplemental patches. -/
theorem outside (a : ℕ) (read : CubePacket.ReadAt Y pub a) :
    (∀ row∈rows, row.Outside reports a) ∧ ¬tasks.outputAt a ∧ (∀ i < count, (supp i).Outside a) := by
  obtain ⟨frameBefore,packetBefore,cellBefore,deckBefore⟩ := placed.ordered
  obtain ⟨tails,counters⟩ := placed.reportCounts
  obtain ⟨calls,taskStart⟩ := placed.outputs
  have address := placed.operands a read
  have facts : a < stop ∧ a≠tasks.frame+90 ∧ (a < cell ∨ deck ≤ a) ∧
      (a < (pub 0).val+112 ∨ packet ≤ a) := by
    rw [placed.frame]
    rcases address with ⟨j,hj,rfl⟩|⟨lo,hi⟩|⟨lo,hi⟩
    · simp only [CubePacket.frameWords,List.mem_cons,List.not_mem_nil,or_false] at hj
      omega
    · omega
    · omega
  refine ⟨?_,?_,?_⟩
  · intro row inRows
    obtain ⟨lo,hi⟩ := placed.reportBits row inRows
    unfold Reports.Row.Outside
    omega
  · rintro (⟨lo,_⟩|⟨i,hi,ha⟩|ha)
    · omega
    · dsimp only [TypedTaskBuilder.Layout.call] at ha
      omega
    · exact facts.2.1 ha
  · intro i hi
    obtain ⟨lo,upper,merged⟩ := placed.patch i hi
    unfold Batch.Cell.Outside Outside
    omega

include placed in
/-- The three actual output memories preserve every dynamic lookup precondition,
including selector-indexed recipes, after the native task preparations. -/
theorem prepared {m first second : Memory w} (original : CubePacket.Prepared Y pub m)
    (bits : readings first=Reports.image reports rows (readings m))
    (built : readings second=tasks.published (readings first)) :
    CubePacket.Prepared Y pub (Batch.written second supp count) := by
  apply CubePacket.Prepared.transfer Y original
  intro a read
  obtain ⟨re,ta,su⟩ := outside pub Y placed a read
  rw [Batch.preserve second supp (i:=0) (Nat.zero_le _) a (fun i _ hi => su i hi)]
  apply Fin.ext
  change readings second a=readings m a
  rw [built,TypedTaskBuilder.Layout.published,Function.update_of_ne (fun eq => ta (Or.inr (Or.inr eq))),
    tasks.image_outside _ _ le_rfl _ ta,bits,Reports.image_outside _ _ _ re]

end FiniteEvaluator.TaskReadback

end BorderVNP
end Computability
end OAI
