import OAI.Computability.VPVNP.SliceArithmeticRound
import OAI.Computability.VPVNP.RAMTapeWordDivision

/-!
# Testing a packed field element for zero

A two-state bit scan records whether every bit is zero. It saves the input in
reverse order on a scratch stack, then restores it before returning the single
output bit. The running time depends only on the length of the packed input.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmeticZero

open RAMTape SliceArithmetic SliceArithmeticRound

set_option backward.isDefEq.respectTransparency false in
/-- Input, decision flag, and scratch ports of the packed scalar zero test. -/
inductive Port where
  | input | flag | scratch
  deriving DecidableEq, Fintype

/-- Finite control that tracks whether all bits seen so far are zero while reading, saving, and
marking the result. -/
inductive State where
  | read (z : Bool) | save (z b : Bool) | mark (z : Bool)
  deriving DecidableEq, Fintype

private def scanBody : Routine Port State where
  entry := .read true
  code
    | .read z => .pop .input fun
      | none => some (.mark z)
      | some b => some (.save (z && !b) b)
    | .save z b => .push .scratch b (some (.read z))
    | .mark z => .push .flag z none

/-- After the scan, move the input back from scratch in its original order. -/
def machine : FiniteRoutine Port :=
  (FiniteRoutine.ofRoutine scanBody).followedBy (EvaluatorRadixDivision.reverseOnto .scratch .input)

/-- The packed input, flag suffix, and saved bits at a stage of the zero-test scan. -/
def frame (bits flag scratch : List Bool) : Stacks Port
  | .input => bits
  | .flag => flag
  | .scratch => scratch

private theorem updateInput (a b c v : List Bool) :
    Function.update (frame a b c) .input v = frame v b c := by funext i; cases i <;> rfl

private theorem updateFlag (a b c v : List Bool) :
    Function.update (frame a b c) .flag v = frame a v c := by funext i; cases i <;> rfl

private theorem updateScratch (a b c v : List Bool) :
    Function.update (frame a b c) .scratch v = frame a b v := by funext i; cases i <;> rfl

private theorem scan_run (bits flag scratch : List Bool) (z : Bool) :
    StackRuns scanBody.standalone (2 * bits.length + 2) (some (.read z)) (frame bits flag scratch)
      none (frame [] ((z && !(bits.any id)) :: flag) (bits.reverse ++ scratch)) := by
  induction bits generalizing scratch z with
  | nil =>
    refine StackRuns.cons (.pop rfl) ?_
    rw [updateInput]
    refine StackRuns.cons (.push rfl) ?_
    simp only [List.any_nil, Bool.not_false, Bool.and_true, List.reverse_nil, List.nil_append]
    rw [updateFlag]
    exact .nil ..
  | cons b bits ih =>
    rw [List.length_cons, Nat.mul_succ]
    refine StackRuns.cons (.pop rfl) ?_
    rw [updateInput]
    refine StackRuns.cons (.push rfl) ?_
    rw [updateScratch]
    cases b with
    | false => simpa [frame] using ih (false :: scratch) z
    | true => simpa [frame] using ih (true :: scratch) false

/-- One output bit, with the input restored and scratch empty. -/
theorem machine_runs (bits flag : List Bool) :
    machine.Runs (4 * bits.length + 3) (frame bits flag []) (frame bits ((!(bits.any id)) :: flag) []) := by
  have hscan : scanBody.Runs (2 * bits.length + 2) (frame bits flag [])
      (frame [] ((!(bits.any id)) :: flag) bits.reverse) := by
    change StackRuns scanBody.standalone _ (some (State.read true)) _ none _
    simpa using scan_run bits flag [] true
  have hrestore := EvaluatorRadixDivision.reverseOnto_runs (src := Port.scratch) (dst := .input)
    (by decide) (frame [] ((!(bits.any id)) :: flag) bits.reverse) (frame bits ((!(bits.any id)) :: flag) [])
    rfl (by simp [frame]) (by intro i hi hj; cases i <;> simp_all [frame])
  simpa only [machine, frame, List.length_reverse, show 2 * bits.length + 2 + (2 * bits.length + 1) =
    4 * bits.length + 3 by omega] using FiniteRoutine.Runs.followedBy (a := .ofRoutine scanBody) hscan hrestore

private theorem any_packed_iff {p w : ℕ} [NeZero p] (hw : Word.workingWidth p ≤ w)
    (xs : List (Fin p)) : (packed w xs).any id = true ↔ ∃ x ∈ xs, x ≠ 0 := by
  induction xs with
  | nil => simp [packed]
  | cons a xs ih =>
    change ((BurstRAM.wordBits (Word.limb w a)) ++ packed w xs).any id = true ↔ _
    rw [List.any_append, Bool.or_eq_true, ih, TapeWord.anyBit_iff, TapeWord.value_wordBits, Word.limb_val hw]
    have ha : 0 < a.val ↔ a ≠ 0 := by
      rw [Nat.pos_iff_ne_zero]
      exact not_congr ⟨fun h => Fin.ext h, fun h => h ▸ rfl⟩
    rw [ha]
    simp only [List.mem_cons, exists_eq_or_imp]

/-- On a canonical scalar the flag is true precisely when its coefficient
vector is zero. An arbitrary existing flag suffix is retained. -/
theorem vector_runs {p e w : ℕ} [NeZero p] (hw : Word.workingWidth p ≤ w)
    (v : Vector p e) (flag : List Bool) :
    machine.Runs (4 * (e*w) + 3) (frame (packed w (List.ofFn v)) flag [])
      (frame (packed w (List.ofFn v)) (decide (v = zero p e) :: flag) []) := by
  have hbit : (!((packed w (List.ofFn v)).any id)) = decide (v = zero p e) := by
    by_cases hz : v = zero p e
    · have ha : (packed w (List.ofFn v)).any id ≠ true := by
        intro h
        obtain ⟨x, hx, hn⟩ := (any_packed_iff hw _).mp h
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        exact hn (hz ▸ rfl)
      rw [Bool.eq_false_iff.mpr ha, decide_eq_true hz]
      rfl
    · have ha : (packed w (List.ofFn v)).any id = true := by
        rw [any_packed_iff hw]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
        exact ⟨v i, List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩
      simp [hz, ha]
  simpa only [packed_length, List.length_ofFn, hbit] using machine_runs (packed w (List.ofFn v)) flag

end SliceArithmeticZero

end VPVNP
end Computability
end OAI
