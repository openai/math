import OAI.Computability.VPVNP.RAMTapeSortRowAddressUnary
import OAI.Computability.VPVNP.RAMTapeInputParametersMultiply
import OAI.Computability.VPVNP.EvaluatorRadixDivision

/-! # Computing packed pin-table offsets from the live binary row index

The little-endian index is consumed once. Its unary value is multiplied by
the stride of the table on scratch stacks. The multiplication preserves the
unary index and stride for the next table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace AffinePin.Index

open RAMTape EvaluatorRadixDivision

/-- The binary input, reversed bit stream, unary output, and scratch stacks for decoding a
coordinate index. -/
inductive Port where | bits | high | index | tmp
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Initialize the index decoder with the supplied bit streams, a unary index tally, and empty
scratch. -/
def bank (bits high : List Bool) (index : ℕ) : Stacks Port
  | .bits => bits | .high => high | .index => List.replicate index true | .tmp => []

private def unaryPorts : SortRowAddress.Unary.Port → Port
  | .bits => .high | .out => .index | .tmp => .tmp

/-- Reverse the little-endian index bits and decode them into a tally with one true marker per
unit of the index. -/
def decode : FiniteRoutine Port :=
  (reverseOnto .bits .high).followedBy (SortRowAddress.Unary.routine.onPorts unaryPorts)

theorem decode_runs (xs : List Bool) : ∃ k ≤ 7*TapeWord.value xs + 6*xs.length+2,
    decode.Runs k (bank xs [] 0) (bank [] [] (TapeWord.value xs)) := by
  have rev := reverseOnto_runs (src := Port.bits) (dst := .high) (by decide)
    (bank xs [] 0) (bank [] xs.reverse 0) rfl (by simp [bank])
    (by intro j h h'; cases j <;> first | rfl | exact (h rfl).elim | exact (h' rfl).elim)
  obtain ⟨k,hk,hr⟩ := SortRowAddress.Unary.runs xs
  have dec : (SortRowAddress.Unary.routine.onPorts unaryPorts).Runs k (bank [] xs.reverse 0)
      (bank [] [] (TapeWord.value xs)) := by
    apply FiniteRoutine.runs_onPorts_framed _ (by decide) hr
    · intro j; cases j <;> rfl
    · intro j; cases j <;> rfl
    · intro j hj; cases j <;> first | rfl | exact (hj .bits rfl).elim | exact (hj .out rfl).elim
  refine ⟨_, ?_, rev.followedBy dec⟩
  change 2*xs.length+1+k ≤ _
  omega

/-- Tally stacks for an index, stride, and accumulated offset together with the two work stacks
for multiplication. -/
inductive OffsetPort where | index | stride | offset | outer | tmp
  deriving DecidableEq

instance : Fintype OffsetPort := derive_fintype% _

/-- Set the index, stride, and offset tallies to the supplied natural numbers and initialize
the two work tallies to zero. -/
def tallies (index stride offset : ℕ) : Tally.State OffsetPort
  | .index => index | .stride => stride | .offset => offset | _ => 0

/-- Add the product of the unary index and stride to the offset tally while preserving the
index and stride. -/
def scale : FiniteRoutine OffsetPort :=
  .ofRoutine (Tally.mulAdd .index .stride .offset .outer .tmp)

theorem scale_runs (i w : ℕ) : scale.Runs (i*(5*w+6)+2)
    (Tally.encode (tallies i w 0)) (Tally.encode (tallies i w (i*w))) := by
  have h := Tally.mulAdd_runs (K := OffsetPort) .index .stride .offset .outer .tmp
    (by decide) (tallies i w 0) rfl rfl
  have upd : Function.update (tallies i w 0) OffsetPort.offset
      ((tallies i w 0) .offset + (tallies i w 0) .index * (tallies i w 0) .stride) =
      tallies i w (i*w) := by
    funext j; cases j <;> simp [tallies]
  rwa [upd] at h

end AffinePin.Index

end VPVNP
end Computability
end OAI
