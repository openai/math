import OAI.Computability.VPVNP.PrimedScheduleRAM
import OAI.Computability.VPVNP.RAMRecords

/-!
# Sequential generation of the endpoint owner table

The genuine-field and padding-field workers each scan a consecutive interval of
endpoint IDs. This pass lifts a single worker's native RAM execution to the
whole interval. The single-call proof may read any cell outside the completed
prefix, since all those cells still contain their initial words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotOwnerPass

open BurstRAM

variable {w : ℕ} {C : Type*}

/-- A worker for one endpoint ID. Only the output cells of earlier calls may
have changed when the worker starts. -/
def Visit (P : Program w C) (fuel probes ticks base start count : ℕ)
    (value : ℕ → Word w) (initial : Memory w) : Prop :=
  ∀ i, start ≤ i → i < start + count → ∀ mem : Memory w,
    (∀ a, a < base + start ∨ base + i ≤ a → mem a = initial a) →
    ∃ es, execute P fuel (P.start (Fin.ofNat _ i)) mem [] =
        some ⟨es, some (Fin.ofNat _ (i + 1))⟩ ∧
      after mem es = writeMemory mem (Fin.ofNat _ (base + i)) (value i) ∧
      countProbes es = probes ∧ es.length = ticks

/-- Running the worker with successive persistent cursors fills exactly the
specified interval of the table. Both the probe count and the instruction
trace length per call are exact. -/
theorem run (P : Program w C) (fuel probes ticks base start count : ℕ)
    (value : ℕ → Word w) (initial : Memory w) (fit : base + start + count ≤ 2 ^ w)
    (visit : Visit P fuel probes ticks base start count value initial) :
    ∃ rs, runSegment P fuel (some (Fin.ofNat _ start)) initial (List.replicate count []) = some rs ∧
      endState (some (Fin.ofNat _ start)) rs = some (Fin.ofNat _ (start + count)) ∧
      (∀ i, start ≤ i → i < start + count → after initial (eventLog rs) (base + i) = value i) ∧
      (∀ a, a < base + start ∨ base + start + count ≤ a → after initial (eventLog rs) a = initial a) ∧
      rs.length = count ∧ (∀ r ∈ rs, r.probes = probes ∧ r.events.length = ticks) ∧
      RAMBuckets.cost Report.probes rs = (1 + probes) * count := by
  induction count with
  | zero =>
    exact ⟨[], rfl, rfl, by omega, fun _ _ => rfl, rfl, by simp, by simp [RAMBuckets.cost]⟩
  | succ count ih =>
    obtain ⟨rs, hr, hs, hfilled, hframe, hlen, hwork, hcost⟩ :=
      ih (by omega) (fun i lo hi mem frame => visit i lo (by omega) mem frame)
    let k := start + count
    let mem := after initial (eventLog rs)
    obtain ⟨es, he, hw, hp, ht⟩ :=
      visit k (by dsimp [k]; omega) (by dsimp [k]; omega) mem
        (fun a ha => hframe a (by simpa only [k, Nat.add_assoc] using ha))
    let r : Report w := ⟨es, some (Fin.ofNat _ (k + 1))⟩
    have haddr : (Fin.ofNat (2 ^ w) (base + k)).val = base + k :=
      Nat.mod_eq_of_lt (by dsimp [k]; omega)
    have hm : after initial (eventLog (rs ++ [r])) =
        writeMemory mem (Fin.ofNat _ (base + k)) (value k) := by
      simpa only [eventLog, List.flatMap_append, List.flatMap_singleton, after, List.foldl_append, r,
        mem] using hw
    have hprobes : r.probes = probes := hp
    refine ⟨rs ++ [r], ?_, ?_, ?_, ?_, by simp [hlen], ?_, ?_⟩
    · rw [List.replicate_succ', PrimedSchedule.runSegment_append, hr]
      simp only [Option.bind_some, hs, runSegment, Option.map_some]
      change (match execute P fuel (P.start (Fin.ofNat _ k)) mem [] with
        | none => none | some t => some [t]).map (rs ++ ·) = some (rs ++ [r])
      rw [he]
      rfl
    · rw [endState_append]
      change some (Fin.ofNat _ (k + 1)) = _
      rw [show k + 1 = start + (count + 1) by dsimp [k]; omega]
    · intro i lo hi
      rw [hm, writeMemory, haddr]
      by_cases eq : i = k
      · simp [eq]
      · rw [ite_eq_right (fun h => eq (Nat.add_left_cancel h))]
        exact hfilled i lo (by dsimp [k] at eq; omega)
    · intro a ha
      rw [hm, writeMemory, haddr, ite_eq_right (by dsimp [k]; omega)]
      exact hframe a (by omega)
    · intro t h
      rcases List.mem_append.mp h with h | h
      · exact hwork t h
      · obtain rfl := List.mem_singleton.mp h
        exact ⟨hp, ht⟩
    · rw [RAMBuckets.cost_append, hcost, RAMBuckets.cost, hprobes, RAMBuckets.cost, Nat.mul_succ]
      omega

end CompressorRecords.SlotOwnerPass

end VPVNP
end Computability
end OAI
