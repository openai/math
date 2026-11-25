import OAI.Computability.BorderVNP.RoutingISACompactBatchModel
import OAI.Computability.BorderVNP.RoutingISACompactWriteBurst

/-!
# Preservation of live data across a batch of compact cell writers

Earlier tasks can share read-only source words. They may reuse scratch storage once
a row is complete. Only future inputs, directory fields, and previously delivered
burst words must survive the writes that can still reach them.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactBatch

open VPVNP.BurstRAM Packing.Directory.ISA CellDispatch

/-- Both write intervals of the task are disjoint from the indicated protected span. -/
def Task.Apart (t : Task) (w start len : ℕ) : Prop :=
  CompactWrite.Disjoint start len t.scratch (12*t.external.length) ∧
    CompactWrite.Disjoint start len t.dest (CompactFrame.pack w t.payload).length

/-- A physical address inside a protected interval retains its previous word through both stores. -/
theorem Task.write_keeps {w start len : ℕ} (t : Task) (m : Memory w) (apart : t.Apart w start len)
    (a : ℕ) (lo : start ≤ a) (hi : a < start+len) : t.write m a = m a := by
  obtain ⟨pre,pack⟩ := apart
  unfold CompactWrite.Disjoint at pre pack
  rw [Task.write, putWords_outside _ _ _ _ (by omega), Task.seed, putWords_outside]
  simp only [List.length_map, CompactMachine.length_externalRecords]
  omega

/-- After any contiguous sequence of task executions disjoint from a given read address,
the value is exactly the word at the start of the sequence. -/
private theorem preserve {w : ℕ} (m : Memory w) (tasks : ℕ → Task) {start finish base len : ℕ}
    (range : start ≤ finish) (apart : ∀ j, start ≤ j → j < finish → (tasks j).Apart w base len)
    (a : ℕ) (lo : base ≤ a) (hi : a < base+len) :
    written m tasks finish a = written m tasks start a := by
  induction finish with
  | zero => have := Nat.eq_zero_of_le_zero range; subst start; rfl
  | succ k ih =>
    by_cases h : start = k+1
    · rw [h]
    · rw [written, (tasks k).write_keeps _ (apart k (by omega) (by omega)) a lo hi]
      exact ih (by omega) (fun j hj hk => apart j hj (by omega))

/-- The physically allocated batch table stays intact, future input words are retained
until their task starts, and completed compact bursts are preserved through later rows. -/
structure Allocation (w table count : ℕ) (tasks : ℕ → Task) : Prop where
  /-- The task pointer table is read-only during the scan. -/
  tableWords : ∀ i < count, (tasks i).Apart w table (5*count)
  /-- Future external bit arrays survive both write intervals of any earlier task. -/
  external : ∀ i j, i < j → j < count → (tasks i).Apart w (tasks j).extBase (tasks j).external.length
  /-- Future serialized program suffixes survive earlier writes. -/
  suffix : ∀ i j, i < j → j < count → (tasks i).Apart w
    ((tasks j).scratch+12*(tasks j).external.length) (tasks j).suffix.length
  /-- An earlier packed word burst cannot be overwritten by a later task. -/
  outputs : ∀ i j, i < j → j < count → (tasks j).Apart w (tasks i).dest
    (CompactFrame.pack w (tasks i).payload).length

/-- A statically stored, fitted batch layout supplies its live register and input
preconditions throughout the native scan. -/
theorem Allocation.ready {w table count : ℕ} {tasks : ℕ → Task} (a : Allocation w table count tasks)
    (m : Memory w) (init : ∀ i < count, (tasks i).Stored m table i ∧ (tasks i).Input m ∧ (tasks i).Fits w) :
    ∀ i < count, (tasks i).Stored (written m tasks i) table i ∧
      (tasks i).Input (written m tasks i) ∧ (tasks i).Fits w := by
  intro i hi
  obtain ⟨row,⟨input,body⟩,fit⟩ := init i hi
  have field (k : ℕ) (hk : k < 5) : written m tasks i (table+5*i+k) = m (table+5*i+k) :=
    preserve m tasks (start := 0) (Nat.zero_le i) (fun j _ hj => a.tableWords j (hj.trans hi)) _
      (by omega) (by omega)
  refine ⟨?_,⟨?_,?_⟩,fit⟩
  · unfold Task.Stored
    simp only [show written m tasks i (table+5*i) = m (table+5*i) from field 0 (by decide),
      field 1 (by decide), field 2 (by decide), field 3 (by decide), field 4 (by decide)]
    exact row
  · intro k hk
    rw [preserve m tasks (start := 0) (Nat.zero_le i) (fun j _ hj => a.external j i hj hi) _ (by omega) (by omega)]
    exact input k hk
  · intro k hk
    rw [preserve m tasks (start := 0) (Nat.zero_le i) (fun j _ hj => a.suffix j i hj hi) _ (by omega) (by omega)]
    exact body k hk

/-- The output burst of any completed task has exactly its canonical descriptor words,
even after all other tasks have finished. -/
theorem Allocation.result {w table count : ℕ} {tasks : ℕ → Task} (a : Allocation w table count tasks)
    (m : Memory w) (i : ℕ) (hi : i < count) :
    TeamRAM.previous (written m tasks count) (.burst (tasks i).dest (CompactFrame.pack w (tasks i).payload).length) =
      CompactFrame.pack w (tasks i).payload := by
  let xs := CompactFrame.pack w (tasks i).payload
  change List.ofFn (fun k : Fin xs.length => written m tasks count ((tasks i).dest+k.val)) = xs
  have val (k : Fin xs.length) : written m tasks count ((tasks i).dest+k.val) = xs[k] := by
    rw [preserve m tasks (start := i+1) hi (fun j hj hk => a.outputs i j (by omega) hk) _
      (Nat.le_add_right ..) (Nat.add_lt_add_left k.isLt _), written, Task.write]
    exact putWords_read ..
  simp_rw [val]
  exact List.ofFn_getElem ..

/-- Stores in the batch preserve the common frame and all three words of each public cell row. -/
theorem preserve_directory {w count : ℕ} {tasks : ℕ → Task} (m : Memory w) (pub : Arg → Word w)
    (frame : ∀ j < count, (tasks j).Apart w (pub 0).val 16)
    (rows : ∀ j < count, (tasks j).Apart w (Frame.ofMemory pub m).base (3*(Frame.ofMemory pub m).count)) :
    Frame.ofMemory pub (written m tasks count) = Frame.ofMemory pub m ∧
      ∀ i < (Frame.ofMemory pub m).count, ∀ k < 3,
        written m tasks count ((Frame.ofMemory pub m).address i+k) = m ((Frame.ofMemory pub m).address i+k) := by
  have field (k : ℕ) (hk : k < 16) : written m tasks count ((pub 0).val+k) = m ((pub 0).val+k) :=
    preserve m tasks (start := 0) (Nat.zero_le _) (fun j _ hj => frame j hj) _ (by omega) (by omega)
  constructor
  · simp only [Frame.ofMemory, show written m tasks count (pub 0).val = m (pub 0).val from field 0 (by decide),
      field 14 (by decide), field 15 (by decide)]
  · intro i hi k hk
    apply preserve m tasks (start := 0) (Nat.zero_le _) (fun j _ hj => rows j hj)
    all_goals unfold Frame.address; omega

/-- A physical row may refer to any task of its owner. After the batch its actual
call interval supplies exactly the external literal prefix followed by the compact suffix. -/
theorem Allocation.row_result {w table count : ℕ} {tasks : ℕ → Task} (a : Allocation w table count tasks)
    (m : Memory w) (pub : Arg → Word w)
    (frame : ∀ j < count, (tasks j).Apart w (pub 0).val 16)
    (rows : ∀ j < count, (tasks j).Apart w (Frame.ofMemory pub m).base (3*(Frame.ofMemory pub m).count))
    {i j : ℕ} (hi : i < (Frame.ofMemory pub m).count) (hj : j < count)
    (ptr : (m ((Frame.ofMemory pub m).address i+1)).val = (tasks j).dest)
    (len : (m ((Frame.ofMemory pub m).address i+2)).val = (CompactFrame.pack w (tasks j).payload).length) :
    TeamRAM.previous (written m tasks count) ((Frame.ofMemory pub (written m tasks count)).burst (written m tasks count) i) =
      CompactFrame.pack w (tasks j).payload := by
  obtain ⟨hf,hr⟩ := preserve_directory m pub frame rows
  rw [hf, Frame.burst, hr i hi 1 (by decide), hr i hi 2 (by decide), ptr, len]
  exact a.result m j hj

end RoutingISA.CompactBatch

end BorderVNP
end Computability
end OAI
