import OAI.Computability.BorderVNP.RoutingISAScheduleClockTypedInput
import OAI.Computability.BorderVNP.RoutingISAScheduleClockArguments
import OAI.Computability.BorderVNP.CellSparseExteriorBatchRun
import OAI.Computability.BorderVNP.CellSparseExteriorSupplementalCost

/-! # Native argument and directory charges after sparse exterior encoding

The supplemental descriptor writer executes first. The exterior encoder reads
its output and replaces the external pointer and length of each owned task.
The last initializer reads these replacements and publishes the actual bursts
in the private directory. The charge applies at the end of initialization,
including paths whose subsequent private calls reject.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM CellDispatch CompactMachine CellSparse Finset

/-- The typed entry's instruction count plus the private directory traversals
and reads of the published packed arguments. -/
def typedDirectoryTicks {w : ℕ} (tasks : ℕ → TypedBatch.Task) (f : Frame) (mt : Memory w) (count : ℕ) :=
  TypedBatch.loadDirectory.slots+TypedBatch.setup.slots+
    (∑ i ∈ range count, TypedBatch.rowCharge (fun j => (tasks j).cell.cost w) i)+1+
    (17+7*f.count+4*(f.ownedRows mt 0 f.count).length+∑ i ∈ range count, ((tasks i).cell.burst w).length)

/-- At any return from the physical typed entry the cost of its event stream
and the probe lengths in its resulting directory are bounded together. -/
theorem typedDirectory_charge {w table count n : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s m es t mt} {tasks : ℕ → TypedBatch.Task} {cells : ℕ → CellInput}
    (input : TypedDirectoryInput pub m table count n tasks cells) (run : Runs pub mac TypedBatch.entry s m es t mt) :
    traceCost es+privateDirectoryTicks pub mt ≤ typedDirectoryTicks tasks (Frame.ofMemory pub m) mt count := by
  obtain ⟨fs,u,first,cost,_⟩ := TypedBatch.entry_run pub mac s m tasks input.frame input.width input.base input.length
    input.space input.allocated input.stored input.room
  obtain ⟨events,_,image⟩ := run.unique_of_deterministic (by decide) first
  subst mt
  rw [events]
  have burst := input.placed.total_burst_le input.allocated (fun i hi => (input.room i hi).2) input.control
  unfold privateDirectoryTicks typedDirectoryTicks
  simp only [input.control.survives.1]
  exact Nat.add_le_add cost (Nat.add_le_add_left burst _)

open CellPacket.Supplement.Batch

/-- The instruction allowance of the consecutive supplemental and sparse passes,
plus the typed and private argument-directory charge on their real output. -/
def sparseCallTicks {w : ℕ} (l : SparseExterior.Layout) (owned : ℕ → SparseExterior.Owned)
    (tasks : ℕ → TypedBatch.Task) (f : Frame) (mt : Memory w) (count : ℕ) :=
  (17+62*count)+(SparseExterior.setup.slots+(∑ i ∈ range l.count, (owned i).charge w)+1)+
    typedDirectoryTicks tasks f mt count

/-- The actual compressed initializer charge is the supplemental native
charge for those rewritten placements together with the exterior pass. -/
theorem sparseCallTicks_eq_nativeCharge {w : ℕ} {Site : Type} (l : SparseExterior.Layout)
    (os : ℕ → SparseExterior.Owned) (source : ℕ → Owned Site) (f : Frame) (mt : Memory w) (count : ℕ) :
    sparseCallTicks l os (fun i => (os i).typed l (source i).typed) f mt count =
      nativeCharge (fun i => (os i).supplemental l (source i)) f mt count+
      (SparseExterior.setup.slots+(∑ i ∈ range l.count, (os i).charge w)+1) := by
  dsimp only [sparseCallTicks,typedDirectoryTicks,nativeCharge,SparseExterior.Owned.supplemental_typed]
  omega

/-- Replay the three native programs in their actual order. The sparse pass
reads the descriptor-writer output and the typed initializer uses the rewritten
task table in the exterior writer's precise memory image. -/
theorem sparse_preparedDirectory_charge {w table controls count n : ℕ} {pub : Arg → Word w}
    {mac : TeamOpcode.Macros w 8} {s m es t mt} (merge : ℕ → CellPacket.Supplement.Batch.Cell)
    (frame : (pub 0).val+92 < 2^w) (pointer : readings m ((pub 0).val+92)+11 < 2^w)
    (len : readings m ((pub 0).val+90)=count) (base : readings m ((pub 0).val+89)=table)
    (ctrl : readings m (readings m ((pub 0).val+92)+11)=controls) (space : table+7*count ≤ 2^w)
    (controlSpace : controls+4*count ≤ 2^w)
    (source : ∀ i < count, Stored (merge i) table controls i m ∧ Room (merge i) w)
    (apart : ∀ i < count, ∀ j < i, ∀ a ∈ (merge i).sources table controls i, (merge j).Outside a)
    (l : SparseExterior.Layout) (owned : ℕ → SparseExterior.Owned) (tasks : ℕ → TypedBatch.Task)
    (cells : ℕ → CellInput) (fp : (pub 0).val=l.frame) (header : l.control+36 < 2^w) :
    let patched := written m merge count
    l.Loaded (readings patched) → (∀ i < l.count, (owned i).Initial l i patched) →
    (∀ i < l.count, ∀ j < i, ∀ a, (owned i).Source l i a → (owned j).Outside l j a) →
    ∀ (compressed : Memory w), readings compressed=SparseExterior.written l owned (readings patched) l.count →
      TypedDirectoryInput pub compressed table count n tasks cells →
      Runs pub mac (.block [entry,SparseExterior.prepare,TypedBatch.entry]) s m es t mt →
      traceCost es+privateDirectoryTicks pub mt ≤ sparseCallTicks l owned tasks (Frame.ofMemory pub compressed) mt count := by
  intro patched loaded initial safe compressed image typed run
  obtain ⟨xs,u,first,cx,_,_⟩ := entry_run (pub:=pub) (mac:=mac) s m merge frame pointer len base ctrl
    space controlSpace source apart
  obtain ⟨ys,v,mv,second,cy,updated,_⟩ := SparseExterior.prepare_run (pub:=pub) (mac:=mac) u patched l owned fp loaded
    (fp ▸ frame) header initial safe
  have actual : mv=compressed := funext fun a => Fin.ext (congrFun (updated.trans image.symm) a)
  subst mv
  obtain ⟨zs,z,last,_,_⟩ := TypedBatch.entry_run pub mac v compressed tasks typed.frame typed.width typed.base typed.length
    typed.space typed.allocated typed.stored typed.room
  have ct := typedDirectory_charge typed last
  have all := first.seq (second.seq last)
  obtain ⟨events,_,out⟩ := run.unique_of_deterministic (by decide) all
  rw [events,out]
  simp only [Transmission.cost_append,sparseCallTicks]
  omega

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
