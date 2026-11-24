import OAI.Computability.VPVNP.AffinePinIndex
import OAI.Computability.VPVNP.EvaluatorDigitLookup
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-! # Native indexed selection from an immutable packed pin table -/

namespace OAI
namespace Computability
namespace VPVNP

namespace AffinePin.Reader

open RAMTape

/-- Stack addresses for a fixed-stride table lookup, including its unary counters, packed
source, saved prefix, reversed entry and output. -/
inductive Port where | index | stride | offset | outer | tmp | width | src | saved | reversed | out
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

private def scalePort : Index.OffsetPort → Port
  | .index => .index | .stride => .stride | .offset => .offset | .outer => .outer | .tmp => .tmp

private def readPort : EvaluatorDigitLookup.Port → Port
  | .src => .src | .offset => .offset | .width => .width | .saved => .saved
  | .revDigit => .reversed | .digit => .out

/-- Encode the index, stride, offset and width in unary and install the source table and output
stack with empty lookup scratch. -/
def bank (i stride offset width : ℕ) (src out : List Bool) : Stacks Port
  | .index => List.replicate i true | .stride => List.replicate stride true
  | .offset => List.replicate offset true | .width => List.replicate width true
  | .src => src | .out => out | _ => []

/-- Prepend the `stride` bits starting at bit `i * stride` of the source table to the output
stack, restoring the source table after the read. -/
def machine : FiniteRoutine Port :=
  ((Index.scale.onPorts scalePort).followedBy (SuccessorFields.prependCopy .stride .width .tmp)).followedBy
    (EvaluatorDigitLookup.lookupRoutine.onPorts readPort)

/-- Exact step count to compute the offset `i * stride`, copy the width marker and retrieve the
full fixed-width table entry at index `i`. -/
def cost (i stride : ℕ) : ℕ :=
  i*(5*stride+6)+2 + (5*stride+2) + EvaluatorDigitLookup.lookupTicks (i*stride) stride

theorem machine_runs (src out : List Bool) (i w : ℕ) (hf : i*w+w ≤ src.length) :
    machine.Runs (cost i w) (bank i w 0 0 src out)
      (bank i w 0 0 src (((src.drop (i*w)).take w) ++ out)) := by
  have scale : (Index.scale.onPorts scalePort).Runs (i*(5*w+6)+2)
      (bank i w 0 0 src out) (bank i w (i*w) 0 src out) := by
    apply FiniteRoutine.runs_onPorts_framed _ (by decide) (Index.scale_runs i w)
    · intro p; cases p <;> rfl
    · intro p; cases p <;> rfl
    · intro p hp; cases p <;> first | rfl | exact (hp .offset rfl).elim
  let s := bank i w (i*w) 0 src out
  have copy := SuccessorFields.prependCopy_runs Port.stride .width .tmp
    (by decide) (by decide) (by decide) s rfl
  have upd : Function.update s Port.width (s .stride ++ s .width) = bank i w (i*w) w src out := by
    funext p; cases p <;> simp [s, bank]
  have hw : (s .stride).length = w := List.length_replicate
  rw [upd, hw] at copy
  have read : (EvaluatorDigitLookup.lookupRoutine.onPorts readPort).Runs
      (EvaluatorDigitLookup.lookupTicks (i*w) w) (bank i w (i*w) w src out)
      (bank i w 0 0 src (((src.drop (i*w)).take w) ++ out)) := by
    apply FiniteRoutine.runs_onPorts_framed _ (by decide)
      (EvaluatorDigitLookup.lookupRoutine_runs_at src out (i*w) w hf)
    · intro p; cases p <;> rfl
    · intro p; cases p <;> rfl
    · intro p hp; cases p <;> first | rfl | exact (hp .offset rfl).elim | exact (hp .width rfl).elim | exact (hp .digit rfl).elim
  exact (scale.followedBy copy).followedBy read

end AffinePin.Reader

end VPVNP
end Computability
end OAI
