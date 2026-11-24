import OAI.Computability.VPVNP.RAMTapeUnaryWord
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord
import OAI.Computability.VPVNP.StructuredStackCall
import OAI.Computability.VPVNP.RoutineSpace

/-! # Encoding the one-based label in a Cramer target row

The evaluator's label port stores its zero-based ordinal in unary. The powered
monomial reader takes a fixed-width binary mark with value one greater. The
original unary stream survives the conversion and can be reused on return.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.LabelWord

open RAMTape UniversalCountStack

private def count : FiniteRoutine UnaryWord.Port :=
  .ofRoutine (Routine.ofCode (UnaryWord.code 0) .count .done)

/-- Convert a zero-based unary label ordinal to its one-based binary mark, preserving the
source stream. -/
def machine : FiniteRoutine UnaryWord.Port :=
  ((SuccessorFields.prependCopy .src .pending .tmp).followedBy
    (FiniteRoutine.ofRoutine (Routine.push .pending true))).followedBy count

/-- Step count for copying the unary label, appending one marker, and counting into a
fixed-width word. -/
def clock (label w : ℕ) := ((5*label+2)+1)+((label+1)*(4*w+3)+1)

theorem machine_bounded (label w : ℕ) (fits : label+1 < 2^w) :
    let bits := List.replicate label true
    machine.BoundedRun (max label w + clock label w) (clock label w)
      (UnaryWord.store bits [] (digits w 0) [] []) (UnaryWord.store bits [] (digits w (label+1)) [] []) := by
  let bits := List.replicate label true
  let src := UnaryWord.store bits [] (digits w 0) [] []
  let saved := UnaryWord.store bits bits (digits w 0) [] []
  let pre := UnaryWord.store bits (List.replicate (label+1) true) (digits w 0) [] []
  have cp := SuccessorFields.prependCopy_runs UnaryWord.Port.src .pending .tmp (by decide) (by decide) (by decide) src rfl
  have hs : Function.update src .pending (bits++[]) = saved := by funext k; cases k <;> simp [src, saved, UnaryWord.store]
  change (SuccessorFields.prependCopy .src .pending .tmp).Runs (5*bits.length+2) src
    (Function.update src .pending (bits++[])) at cp
  rw [hs, show bits.length = label from List.length_replicate] at cp
  have pushed := Routine.runs_push UnaryWord.Port.pending true saved
  have hp : Function.update saved .pending (true :: saved .pending) = pre := by funext k; cases k <;> rfl
  rw [hp] at pushed
  have ctl := Routine.runs_ofCode (by decide : UnaryWord.Phase.count (p := 0) ≠ .done) rfl
    (UnaryWord.count_fixed 0 w (label+1) bits [] fits)
  have call : count.Runs ((label+1)*(4*w+3)+1) pre (UnaryWord.store bits [] (digits w (label+1)) [] []) := by
    dsimp only [count, FiniteRoutine.ofRoutine, FiniteRoutine.Runs, pre]
    rw [digits_zero]
    exact ctl
  have pushRun : (FiniteRoutine.ofRoutine (Routine.push UnaryWord.Port.pending true)).Runs 1 saved pre := pushed
  have run := (cp.followedBy pushRun).followedBy call
  apply spaceRun_of_steps (show machine.Runs (clock label w) src _ from run)
  intro k
  apply Nat.add_le_add_right
  cases k <;> simp [src, bits, UnaryWord.store]

end RankQuery.Stack.Coordinate.LabelWord

end VPVNP
end Computability
end OAI
