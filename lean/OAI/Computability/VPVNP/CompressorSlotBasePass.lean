import OAI.Computability.VPVNP.PrimedScheduleRAM
import OAI.Computability.VPVNP.RAMRecords

/-!
# Scanning two output tables of the compressed base graph

The worker at cursor `i` writes the destination base arc and lane displacement
into separate tables. Outside their completed prefixes, all input words retain
their initial values. This lets one lift a single native call to a full scan
with an exact calls-plus-probes count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotBasePass

open BurstRAM

variable {w : ℕ} {C : Type*}

/-- Execution of one call under the frame left by all preceding calls. -/
def Visit (P : Program w C) (fuel probes ticks base₁ base₂ count : ℕ)
    (value₁ value₂ : ℕ → Word w) (initial : Memory w) : Prop :=
  ∀ i < count, ∀ mem : Memory w,
    (∀ a, (a < base₁ ∨ base₁ + i ≤ a) → (a < base₂ ∨ base₂ + i ≤ a) →
      mem a = initial a) →
    ∃ es, execute P fuel (P.start (Fin.ofNat _ i)) mem [] =
        some ⟨es, some (Fin.ofNat _ (i + 1))⟩ ∧
      after mem es = writeMemory (writeMemory mem (Fin.ofNat _ (base₁ + i)) (value₁ i))
        (Fin.ofNat _ (base₂ + i)) (value₂ i) ∧
      countProbes es = probes ∧ es.length = ticks

/-- The two completed tables, persistent state, and resource use of a scan. -/
structure FilledRun (P : Program w C) (fuel probes ticks base₁ base₂ count : ℕ)
    (value₁ value₂ : ℕ → Word w) (initial : Memory w) (rs : List (Report w)) : Prop where
  executed : runSegment P fuel (some 0) initial (List.replicate count []) = some rs
  cursor : endState (some 0) rs = some (Fin.ofNat _ count)
  first : ∀ i < count, after initial (eventLog rs) (base₁ + i) = value₁ i
  second : ∀ i < count, after initial (eventLog rs) (base₂ + i) = value₂ i
  frame : ∀ a, (a < base₁ ∨ base₁ + count ≤ a) → (a < base₂ ∨ base₂ + count ≤ a) →
    after initial (eventLog rs) a = initial a
  length : rs.length = count
  calls : ∀ r ∈ rs, r.probes = probes ∧ r.events.length = ticks
  cost : RAMBuckets.cost Report.probes rs = (1 + probes) * count

/-- Successive calls fill both disjoint output intervals in cursor order. -/
theorem run (P : Program w C) (fuel probes ticks base₁ base₂ count : ℕ)
    (value₁ value₂ : ℕ → Word w) (initial : Memory w)
    (fit₁ : base₁ + count ≤ 2 ^ w) (fit₂ : base₂ + count ≤ 2 ^ w)
    (disjoint : base₁ + count ≤ base₂ ∨ base₂ + count ≤ base₁)
    (visit : Visit P fuel probes ticks base₁ base₂ count value₁ value₂ initial) :
    ∃ rs, FilledRun P fuel probes ticks base₁ base₂ count value₁ value₂ initial rs := by
  induction count with
  | zero =>
    exact ⟨[], rfl, rfl, by omega, by omega, fun _ _ _ => rfl, rfl, by simp, by simp [RAMBuckets.cost]⟩
  | succ count ih =>
    obtain ⟨rs, prev⟩ := ih (by omega) (by omega) (by omega)
      (fun i hi => visit i (by omega))
    let mem := after initial (eventLog rs)
    obtain ⟨es, he, hw, hp, ht⟩ := visit count (Nat.lt_succ_self _) mem prev.frame
    let r : Report w := ⟨es, some (Fin.ofNat _ (count + 1))⟩
    have h₁ : (Fin.ofNat (2 ^ w) (base₁ + count)).val = base₁ + count :=
      Nat.mod_eq_of_lt (by omega)
    have h₂ : (Fin.ofNat (2 ^ w) (base₂ + count)).val = base₂ + count :=
      Nat.mod_eq_of_lt (by omega)
    have hm (a : ℕ) : after initial (eventLog (rs ++ [r])) a =
        if a = base₂ + count then value₂ count
        else if a = base₁ + count then value₁ count else mem a := by
      simpa only [eventLog, List.flatMap_append, List.flatMap_singleton, after, List.foldl_append,
        r, mem, writeMemory, h₁, h₂] using congrFun hw a
    refine ⟨rs ++ [r], ?_, ?_, ?_, ?_, ?_, by simp [prev.length], ?_, ?_⟩
    · rw [List.replicate_succ', PrimedSchedule.runSegment_append, prev.executed]
      simp only [Option.bind_some, prev.cursor, runSegment, Option.map_some]
      change (match execute P fuel (P.start (Fin.ofNat _ count)) mem [] with
        | none => none | some t => some [t]).map (rs ++ ·) = some (rs ++ [r])
      rw [he]
      rfl
    · rw [endState_append]
      rfl
    · intro i hi
      rw [hm, ite_eq_right (by omega)]
      by_cases eq : i = count
      · simp [eq]
      · rw [ite_eq_right (by omega)]
        exact prev.first i (by omega)
    · intro i hi
      rw [hm]
      by_cases eq : i = count
      · simp [eq]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact prev.second i (by omega)
    · intro a ha hb
      rw [hm, ite_eq_right (by omega), ite_eq_right (by omega)]
      exact prev.frame a (by omega) (by omega)
    · intro t h
      rcases List.mem_append.mp h with h | h
      · exact prev.calls t h
      · obtain rfl := List.mem_singleton.mp h
        exact ⟨hp, ht⟩
    · have hprobes : r.probes = probes := hp
      rw [RAMBuckets.cost_append, prev.cost, RAMBuckets.cost, hprobes, RAMBuckets.cost, Nat.mul_succ]
      omega

end CompressorRecords.SlotBasePass

end VPVNP
end Computability
end OAI
