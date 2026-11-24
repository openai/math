import OAI.Computability.VPVNP.SliceArithmeticCallPorts
import OAI.Computability.VPVNP.SliceArithmeticAdd

/-!
# Operand and advice ports of the evaluator's multiply-and-add call

The two saved factors are copied onto private streams for the multiplication.
The resulting product then serves as the consumable operand of vector addition.
The original factors and the field advice remain available to the caller.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.MultiplyAccumulate

open BurstRAM RAMTape

/-- Caller ports for the two factors, the running accumulator, and the field parameters used to
add their product. -/
inductive External where
  | prime | zeroWord | degree | coeff | left | returned | acc
  deriving DecidableEq

instance : Fintype External :=
  ⟨{.prime, .zeroWord, .degree, .coeff, .left, .returned, .acc}, by intro i; cases i <;> simp⟩

/-- Private work ports for multiplication, addition, the two operand copies, and the temporary
stack used to copy them. -/
inductive Private where
  | multiply (i : HornerControl.Ports)
  | addition (i : SliceArithmeticStreamRow.Port Unit)
  | multiplicand | product | scratch
  deriving DecidableEq, Fintype

/-- The full stack interface for adding a product to an extension-field accumulator. -/
abbrev Port := Private ⊕ External

/-- Populate the caller's field-advice ports, the two packed factors, and the packed
accumulator. -/
def external (p e w : ℕ) (coeff left returned acc : List Bool) : Stacks External
  | .prime => wordBits (Fin.ofNat (2 ^ w) p)
  | .zeroWord => wordBits (0 : BurstRAM.Word w)
  | .degree => List.replicate e true
  | .coeff => coeff
  | .left => left
  | .returned => returned
  | .acc => acc

/-- At a call boundary all private stacks are empty. The intermediate frames
below name the two private streams that hold the copied operands and product. -/
def workspace (io : Stacks External) (multiplicand product : List Bool) : Stacks Port
  | .inl .multiplicand => multiplicand
  | .inl .product => product
  | .inl _ => []
  | .inr i => io i

/-- Entry and return state with the caller's stacks installed and all multiplication workspace
empty. -/
def clean (io : Stacks External) := workspace io [] []

/-- Connect the field multiplier to the private copies of the factors and the caller's field
advice. -/
def multiplyPorts : MultiplyCall.Port → Port
  | .inl i => .inl (.multiply i)
  | .inr .prime => .inr .prime
  | .inr .zeroWord => .inr .zeroWord
  | .inr .degree => .inr .degree
  | .inr .coeff => .inr .coeff
  | .inr .query => .inl .multiplicand
  | .inr .acc => .inl .product

/-- Connect the coefficientwise adder to the private product stream and the caller's
accumulator. -/
def addPorts : SliceArithmeticStreamRow.Port Unit ⊕ MultiplyCall.External → Port
  | .inl i => .inl (.addition i)
  | .inr .prime => .inr .prime
  | .inr .zeroWord => .inr .zeroWord
  | .inr .degree => .inr .degree
  | .inr .coeff => .inr .coeff
  | .inr .query => .inl .product
  | .inr .acc => .inr .acc

theorem multiplyPorts_injective : Function.Injective multiplyPorts := by
  rintro (i|i) (j|j) h <;> try cases i <;> try cases j <;> simp_all [multiplyPorts]

theorem addPorts_injective : Function.Injective addPorts := by
  rintro (i|i) (j|j) h <;> try cases i <;> try cases j <;> simp_all [addPorts]

/-- Copy the saved left and returned right factors onto the two private multiplication stacks. -/
def stage : FiniteRoutine Port :=
  (SuccessorFields.prependCopy (.inr .left) (.inl .multiplicand) (.inl .scratch)).followedBy
    (SuccessorFields.prependCopy (.inr .returned) (.inl .product) (.inl .scratch))

theorem stage_runs (io : Stacks External) :
    stage.Runs (5 * (io .left).length + 2 + (5 * (io .returned).length + 2))
      (clean io) (workspace io (io .left) (io .returned)) := by
  let s := clean io
  let mid := workspace io (io .left) []
  have h₁ := SuccessorFields.prependCopy_runs (.inr External.left) (.inl Private.multiplicand) (.inl .scratch)
    (by decide) (by decide) (by decide) s rfl
  have h₂ := SuccessorFields.prependCopy_runs (.inr External.returned) (.inl Private.product) (.inl .scratch)
    (by decide) (by decide) (by decide) mid rfl
  rw [show Function.update s (.inl .multiplicand) (s (.inr .left) ++ s (.inl .multiplicand)) = mid by
    funext i; rcases i with i|i; cases i <;> simp [s, mid, clean, workspace]; rfl] at h₁
  rw [show Function.update mid (.inl .product) (mid (.inr .returned) ++ mid (.inl .product)) =
      workspace io (io .left) (io .returned) by
    funext i; rcases i with i|i; cases i <;> simp [mid, workspace]; rfl] at h₂
  exact h₁.followedBy h₂

theorem multiplyRun {routine : FiniteRoutine MultiplyCall.Port} {t p e w : ℕ}
    (coeff left returned acc result : List Bool)
    (run : routine.Runs t (MultiplyCall.clean (MultiplyCall.external p e w coeff left returned))
      (MultiplyCall.clean (MultiplyCall.external p e w coeff [] result))) :
    (routine.onPorts multiplyPorts).Runs t (workspace (external p e w coeff left returned acc) left returned)
      (workspace (external p e w coeff left returned acc) [] result) := by
  apply routine.runs_onPorts_framed multiplyPorts_injective run
  · rintro (i|i)
    · rfl
    · cases i <;> rfl
  · rintro (i|i)
    · rfl
    · cases i <;> rfl
  rintro (i|i) hi
  · cases i with
    | multiplicand => exact (hi (.inr .query) rfl).elim
    | product => exact (hi (.inr .acc) rfl).elim
    | _ => rfl
  · rfl

theorem addRun {routine : FiniteRoutine (SliceArithmeticStreamRow.Port Unit ⊕ MultiplyCall.External)}
    {t p e w : ℕ} (coeff left returned acc product result : List Bool)
    (run : routine.Runs t (Sum.elim (fun _ => []) (MultiplyCall.external p e w coeff product acc))
      (Sum.elim (fun _ => []) (MultiplyCall.external p e w coeff [] result))) :
    (routine.onPorts addPorts).Runs t (workspace (external p e w coeff left returned acc) [] product)
      (clean (external p e w coeff left returned result)) := by
  apply routine.runs_onPorts_framed addPorts_injective run
  · rintro (i|i)
    · rfl
    · cases i <;> rfl
  · rintro (i|i)
    · rfl
    · cases i <;> rfl
  rintro (i|i) hi
  · cases i with
    | product => exact (hi (.inr .query) rfl).elim
    | _ => rfl
  · cases i with
    | acc => exact (hi (.inr .acc) rfl).elim
    | _ => rfl

end SliceArithmetic.MultiplyAccumulate

end VPVNP
end Computability
end OAI
