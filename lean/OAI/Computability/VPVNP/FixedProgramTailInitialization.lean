import OAI.Computability.VPVNP.FixedProgramTailOrder
import OAI.Computability.VPVNP.LiveCertificateAssembly
import OAI.Computability.VPVNP.LiveFirstTailPhysicalCount

/-!
# The fixed diagonal program's native initialization function

The scalar evaluator and the physical midpoint store each exponent in the
same finite word width. Their complete initialization functions agree on
arbitrary natural inputs, including inputs reduced modulo that width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM Compression LiveProgram LiveEvaluatorEncoding JointLabelSystem
open scoped Fin.CommRing

open private runtime_congr from OAI.Computability.VPVNP.FixedProgramTailOrder

variable {K : Type*} [Field K] {S : BlockSchedule K} (D : Program) (B : S.Templates)
variable {n C : ℕ} (denseCount : physicalLabelCount D (n := n) = B.denseCount n C)

/-- Both ordinal maps select the same input coordinate, even when the
natural number supplied there requires reduction to the exponent width. -/
theorem nativeRuntimeNat_eq (xs : Fin (physicalLabelCount D (n := n)) → ℕ) :
    EvaluatorProgramRawInput.runtime (fun a =>
      Fin.ofNat (2^(physicalCounterWidth D (n := n))) (xs ((nativeLabelOrder D B denseCount).symm a))) =
    EvaluatorProgramRawInput.runtime (D.exponentWords n (B.formalExponents (xs ∘ (finCongr denseCount).symm))) := by
  let ht := denseCount.trans (FixedRows.labelOrder_length B.Entry n C)
  apply runtime_congr ht (physicalCounterWidth_eq D)
  intro j
  let a := (nativeLabelOrder D B denseCount).symm j
  change xs a % (2^(physicalCounterWidth D (n := n))) = xs a % (2^D.counterWidth n)
  rw [physicalCounterWidth_eq]

private theorem function_heq {a b r s extra : ℕ} (count : a=b) (radius : r=s)
    (f : (Fin a → ℕ) → Code extra r) (g : (Fin b → ℕ) → Code extra s)
    (point : ∀ xs, HEq (f xs) (g (xs ∘ (finCongr count).symm))) : HEq f g := by
  subst b
  subst s
  exact heq_of_eq (funext fun xs => eq_of_heq (point xs))

variable {hn : 2 ≤ n} {p : Nat.Primes}
variable {model : LabelEvaluator.Model p (B.compressorDegree n) (B.compressorEquations hn C)}
variable (data : D.ScalarData B hn model)

/-- The initializer of the physical tail continuation is the initializer
of the scalar model, with only the two equal index sizes transported. -/
theorem midpointInitial_heq {ht : 21 ≤ 2^(D.geometry n).w} {hf : 44 ≤ n^10000} :
    HEq (EvaluatorRoutes.midpointInitial (D.executionGroup n ht hf) data.raw (nativeLabelOrder D B denseCount))
      data.init := by
  apply function_heq denseCount (physicalRadius_eq D (n := n))
  intro xs
  unfold EvaluatorRoutes.midpointInitial ScalarData.init initial
  change HEq (LiveEvaluatorTail.initialCode (D.constants.radius.eval (D.geometry n))
    (UniversalMachine.initial D.evaluator (data.raw ++ EvaluatorProgramRawInput.runtime
      (fun a => Fin.ofNat (2^(physicalCounterWidth D (n := n))) (xs ((nativeLabelOrder D B denseCount).symm a)))))) _
  rw [nativeRuntimeNat_eq,physicalRadius_eq]
  rfl

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
