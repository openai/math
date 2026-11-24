import OAI.Computability.VPVNP.LiveHeaderScan
import OAI.Computability.VPVNP.PrimedScheduleRAM

/-!
# Sequential execution of the distributed index scan

The invariant states exactly what the six probes per call have read and
written. Addresses for the three scratch regions are disjoint from the site
headers. Thus the last call sees the real highest position and population
count, even for a group index much larger than the RAM word modulus.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeader

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w r k : ℕ}

theorem trace_after {pub : Fin k → Word w} {state : Word w} {ops : List (Op r k)}
    {rs rs' : Regs w r} {m m' : Memory w} {es : List (Event w)}
    (ht : trace pub state ops rs m = some (es, rs', m')) : after m es = m' := by
  induction ops generalizing rs m es with
  | nil => simp [trace] at ht; rw [ht.1]; exact ht.2.2
  | cons op ops ih =>
    cases ho : op.effect pub state rs m with
    | none => simp [trace, ho] at ht
    | some out =>
      obtain ⟨e, r₁, m₁⟩ := out
      cases hrest : trace pub state ops r₁ m₁ with
      | none => simp [trace, ho, hrest] at ht
      | some out =>
        obtain ⟨rest, r₂, m₂⟩ := out
        simp [trace, ho, hrest] at ht
        obtain ⟨hes, rfl, rfl⟩ := ht
        rw [← hes]
        have hupdate : update m e = m₁ := by
          cases op <;> simp only [Op.effect, Option.some.injEq, Prod.mk.injEq] at ho
          all_goals first | exact ho.1 ▸ ho.2.2 | split at ho <;> simp at ho
          all_goals exact ho.1 ▸ ho.2.2
        change after (update m e) rest = _
        rw [hupdate]
        exact ih hrest

/-- Consecutive deterministic microcalls realize a memory invariant after
each cursor and cost at most `probeBound + 1` per cursor. -/
theorem run_cursor_segment_at {C : Type*} (P : Program w C) (start fuel count probeBound : ℕ)
    (inv : ℕ → Memory w → Prop) (m : Memory w) (h₀ : inv 0 m)
    (step : ∀ i < count, ∀ mem, inv i mem → ∃ es,
      execute P fuel (P.start ((start+i : ℕ) : Word w)) mem [] = some ⟨es, some ((start+(i+1) : ℕ) : Word w)⟩ ∧
      inv (i+1) (after mem es) ∧ countProbes es ≤ probeBound) :
    ∃ rs, runSegment P fuel (some (start : Word w)) m (List.replicate count []) = some rs ∧
      endState (some (start : Word w)) rs = some ((start+count : ℕ) : Word w) ∧ inv count (after m (eventLog rs)) ∧
      rs.length = count ∧ ∀ x ∈ rs, countProbes x.events ≤ probeBound := by
  have go (j : ℕ) (hj : j ≤ count) : ∃ rs, runSegment P fuel (some (start : Word w)) m (List.replicate j []) = some rs ∧
      endState (some (start : Word w)) rs = some ((start+j : ℕ) : Word w) ∧ inv j (after m (eventLog rs)) ∧
      rs.length = j ∧ ∀ x ∈ rs, countProbes x.events ≤ probeBound := by
    induction j with
    | zero => exact ⟨[], rfl, by simp [endState], h₀, rfl, by simp⟩
    | succ j ih =>
      obtain ⟨rs, hr, hs, hi, hl, hb⟩ := ih (by omega)
      obtain ⟨es, he, hnext, hp⟩ := step j (by omega) _ hi
      let z : Report w := ⟨es, some ((start+(j+1) : ℕ) : Word w)⟩
      refine ⟨rs ++ [z], ?_, ?_, ?_, by simp [hl], ?_⟩
      · rw [List.replicate_succ', PrimedSchedule.runSegment_append, hr]
        simp only [Option.bind_some, hs, runSegment, he, Option.map_some, z]
      · rw [endState_append]; rfl
      · simpa only [eventLog, List.flatMap_append, List.flatMap_singleton, after, List.foldl_append] using hnext
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hb x h
        · have hxz : x = z := List.mem_singleton.mp h
          exact hxz ▸ hp
  exact go count le_rfl

theorem run_cursor_segment {C : Type*} (P : Program w C) (fuel count probeBound : ℕ)
    (inv : ℕ → Memory w → Prop) (m : Memory w) (h₀ : inv 0 m)
    (step : ∀ i < count, ∀ mem, inv i mem → ∃ es,
      execute P fuel (P.start (i : Word w)) mem [] = some ⟨es, some ((i+1 : ℕ) : Word w)⟩ ∧
      inv (i+1) (after mem es) ∧ countProbes es ≤ probeBound) :
    ∃ rs, runSegment P fuel (some 0) m (List.replicate count []) = some rs ∧
      endState (some 0) rs = some (count : Word w) ∧ inv count (after m (eventLog rs)) ∧
      rs.length = count ∧ ∀ x ∈ rs, countProbes x.events ≤ probeBound := by
  simpa using run_cursor_segment_at P 0 fuel count probeBound inv m h₀ (by simpa using step)

/-- The concrete scratch layout for one scan: original site words below
`length`, an unpacked array beginning at `pub 0`, then the two scalar cells. -/
structure ScanLayout (pub : Fin 3 → Word w) (length : ℕ) : Prop where
  nonoverlap : length ≤ (pub 0).val
  highAfter : (pub 0).val + length ≤ (pub 1).val
  countAfter : (pub 1).val < (pub 2).val

/-- Exact invariant over the real external word memory after `cursor` cells. -/
structure ScanInv (pub : Fin 3 → Word w) (index length cursor : ℕ) (m : Memory w) : Prop where
  input : ∀ i < length, (m i).val.testBit 0 = index.testBit i
  high : m (pub 1).val = (prefixHigh index cursor : Word w)
  count : m (pub 2).val = ((prefixOnes index cursor).card : Word w)
  copied : ∀ i < cursor, m ((pub 0).val + i) = PrimedInputRAM.encodeBit w (index.testBit i)

private theorem scanInv_next (pub : Fin 3 → Word w) {index length j : ℕ} {m : Memory w}
    (layout : ScanLayout pub length) (hj : j < length) (hi : ScanInv pub index length j m) :
    ScanInv pub index length (j+1) (indexUpdate pub (j : Word w) m (index.testBit j)) := by
  have h₁ := layout.nonoverlap
  have h₂ := layout.highAfter
  have h₃ := layout.countAfter
  have h₄ := (pub 2).isLt
  have hjw : (j : Word w).val = j := (Fin.val_natCast ..).trans (Nat.mod_eq_of_lt (by omega))
  have hdst : (pub 0 + (j : Word w)).val = (pub 0).val + j := by
    rw [Fin.val_add, hjw, Nat.mod_eq_of_lt (by omega)]
  constructor
  · intro i hil
    simpa [indexUpdate, writeMemory, hdst, show i ≠ (pub 2).val by omega,
      show i ≠ (pub 1).val by omega, show i ≠ (pub 0).val + j by omega] using hi.input i hil
  · simp [indexUpdate, writeMemory, show (pub 1).val ≠ (pub 2).val by omega, prefixHigh_succ, hi.high]
  · simp [indexUpdate, writeMemory, prefixCount_succ, hi.count, PrimedInputRAM.encodeBit]
    cases index.testBit j <;> simp
  · intro i hij
    have hHigh : (pub 0).val + i ≠ (pub 1).val := by omega
    have hCount : (pub 0).val + i ≠ (pub 2).val := by omega
    simp only [indexUpdate, writeMemory, hHigh, hCount, ↓reduceIte, hdst, Nat.add_left_cancel_iff]
    by_cases he : i = j
    · simp [he]
    · simp [he, hi.copied i (by omega)]

/-- The native `indexCell` table reads exactly the occupied index positions.
Its end state points to the next phase and each call costs seven calls-plus-probes. -/
theorem index_scan_native (hw : 4 ≤ w) (pub : Fin 3 → Word w) (index length : ℕ)
    (m : Memory w) (layout : ScanLayout pub length) (h₀ : ScanInv pub index length 0 m) :
    let P := ((template indexCell 11).instantiate w pub).program
    ∃ rs, runSegment P 22 (some 0) m (List.replicate length []) = some rs ∧
      endState (some 0) rs = some (length : Word w) ∧
      ScanInv pub index length length (after m (eventLog rs)) ∧ rs.length = length ∧
      ∀ x ∈ rs, countProbes x.events ≤ 6 := by
  apply run_cursor_segment _ _ _ _ _ _ h₀
  intro j hj mem hi
  have jfit : j < 2 ^ w := lt_of_lt_of_le hj (layout.nonoverlap.trans (pub 0).isLt.le)
  have hjv : (j : Word w).val = j := (Fin.val_natCast ..).trans (Nat.mod_eq_of_lt jfit)
  obtain ⟨es, rs, ht, hr, _, hp, _⟩ := indexCell_trace hw pub (j : Word w) (fun _ => 0) mem
  refine ⟨es, ?_, ?_, hp.le⟩
  · change execute ((template indexCell 11).instantiate w pub).program (1 + indexCell.length)
      ⟨_,(j : Word w),fun _ => 0,fun _ => 0⟩ mem [] = _
    rw [execute_template, run_eq_trace, ht]
    simp [hr]
  · rw [trace_after ht, hjv, hi.input j hj]
    exact scanInv_next pub layout hj hi

end LiveHeader

end VPVNP
end Computability
end OAI
