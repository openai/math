import OAI.Computability.VPVNP.SliceArithmeticStreamWord
import OAI.Computability.VPVNP.SliceArithmeticLoop
import OAI.Computability.VPVNP.RAMTapeUnaryWordValue

/-!
# Emitting a prime-field coefficient in the extension-field representation

A scalar from the prime field occupies the low limb of its power-basis
representation. The unary extension degree supplies one marker per limb.
The machine copies these markers, discards the one for the low limb, then
prepends one zero word per remaining marker before emitting the low limb.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.ConstantEmit

open RAMTape BurstRAM

set_option backward.isDefEq.respectTransparency false in
/-- Ports for the extension degree, zero-word template, prime-field limb, output, and temporary
marker and copy stacks. -/
inductive Port where
  | degree | zeroWord | limb | out | scratch | marker
  deriving DecidableEq, Fintype

/-- Initial or intermediate state of the constant emitter, including the current marker count
and output suffix. -/
def frame (e w : ℕ) (x : BurstRAM.Word w) (out : List Bool) (markers : ℕ) : Stacks Port
  | .degree => List.replicate e true
  | .zeroWord => wordBits (0 : BurstRAM.Word w)
  | .limb => wordBits x
  | .out => out
  | .scratch => []
  | .marker => List.replicate markers true

private def zeros : FiniteRoutine Port :=
  FiniteRoutine.repeatMarked .marker (StreamWord.store .out .zeroWord .scratch)

private def pad : FiniteRoutine Port :=
  .ofRoutine (Routine.popCase .marker (Routine.halt false) (Routine.halt false) zeros.body)

/-- Fixed instruction table for prepending a scalar with one significant limb. -/
def machine : FiniteRoutine Port :=
  ((SuccessorFields.prependCopy .degree .marker .scratch).followedBy pad).followedBy
    (StreamWord.store .out .limb .scratch)

/-- Time for copying the degree, dropping the first marker, scanning the
remaining markers and storing the low limb. -/
def cost (e w : ℕ) := 5 * e + 2 + ((e - 1) * (5 * w + 3) + 2) + (5 * w + 2)

private theorem update_markers (e w : ℕ) (x : BurstRAM.Word w) (s : List Bool) (m n : ℕ) :
    Function.update (frame e w x s m) .marker (List.replicate n true) = frame e w x s n := by
  funext i
  cases i <;> rfl

private theorem update_output (e w : ℕ) (x : BurstRAM.Word w) (s t : List Bool) (m : ℕ) :
    Function.update (frame e w x s m) .out t = frame e w x t m := by
  funext i
  cases i <;> rfl

private theorem zeros_runs (e w : ℕ) (x : BurstRAM.Word w) (m : ℕ) (s : List Bool) :
    zeros.Runs (m * (5 * w + 3) + 1)
      (frame e w x s m) (frame e w x (List.replicate (m * w) false ++ s) 0) := by
  induction m generalizing s with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.nil_append]
    exact Routine.Runs.popLoop_empty Port.marker (fun _ => true) (Routine.halt false)
      (StreamWord.store Port.out .zeroWord .scratch).body (s := frame e w x s 0) rfl
  | succ m ih =>
    let z := wordBits (0 : BurstRAM.Word w)
    have copy := StreamWord.store_runs (stream := Port.out) (reg := .zeroWord) (scratch := .scratch)
      (by decide) (by decide) (by decide) (frame e w x s m) (0 : BurstRAM.Word w) rfl rfl
    rw [update_output] at copy
    have htail := ih (z ++ s)
    have hbits : List.replicate (m * w) false ++ (z ++ s) =
        List.replicate ((m + 1) * w) false ++ s := by
      rw [Nat.succ_mul, List.replicate_add, List.append_assoc, UnaryWord.zeros_wordBits w]
    rw [hbits] at htail
    rw [show (m + 1) * (5 * w + 3) + 1 = 1 + (5 * w + 2) + (m * (5 * w + 3) + 1) by
      rw [Nat.succ_mul]; omega]
    apply Routine.Runs.popLoop_true_continue Port.marker (fun _ => true) (Routine.halt false)
      (StreamWord.store Port.out .zeroWord .scratch).body
      (tail := List.replicate m true) (List.replicate_succ ..) rfl ?_ htail
    rw [update_markers]
    exact copy

/-- The scalar is written before an arbitrary output suffix, least-significant
limb first. The three input ports are preserved and both temporary ports
return empty. -/
theorem machine_runs {e w : ℕ} (he : 0 < e) (x : BurstRAM.Word w) (suffix : List Bool) :
    machine.Runs (cost e w) (frame e w x suffix 0)
      (frame e w x (wordBits x ++ List.replicate ((e - 1) * w) false ++ suffix) 0) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  let e := m + 1
  have first := SuccessorFields.prependCopy_runs Port.degree .marker .scratch
    (by decide) (by decide) (by decide) (frame e w x suffix 0) rfl
  change (SuccessorFields.prependCopy ..).Runs (5 * (List.replicate e true).length + 2) _
    (Function.update _ Port.marker (List.replicate e true ++ [])) at first
  rw [List.length_replicate, List.append_nil, update_markers] at first
  let padded := List.replicate (m * w) false ++ suffix
  have middle : pad.Runs (m * (5 * w + 3) + 1 + 1)
      (frame e w x suffix e) (frame e w x padded 0) := by
    apply Routine.runs_popCase_true Port.marker (Routine.halt false) (Routine.halt false) zeros.body
      (tail := List.replicate m true) (List.replicate_succ ..)
    rw [update_markers]
    exact zeros_runs e w x m suffix
  have last := StreamWord.store_runs (stream := Port.out) (reg := .limb) (scratch := .scratch)
    (by decide) (by decide) (by decide) (frame e w x padded 0) x rfl rfl
  rw [update_output] at last
  rw [List.append_assoc]
  exact (first.followedBy middle).followedBy last

end SliceArithmetic.ConstantEmit

end VPVNP
end Computability
end OAI
