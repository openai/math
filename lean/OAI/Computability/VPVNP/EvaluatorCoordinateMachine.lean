import OAI.Computability.VPVNP.EvaluatorReadInterface

/-!
# The binary evaluator from its two deterministic coordinate readers

The entire stack machine, including binary input decoding and terminal
branching, has fixed control as soon as its two entry readers are fixed.
The two coordinate-query contracts concern only the stored row and column
and the field element returned. The exponent width occurs only in the input,
radix conversion and digit traversal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator.MatrixCallbacks

open RAMTape SliceArithmetic EvaluatorProgramRawInput

variable {P : Type} [DecidableEq P] (ps : List (WeightedStep.Port P))
    (frobenius label : FiniteRoutine (ReadPort P))

/-- A single literal two-tape evaluator table built from the fixed entry
readers, independently of the ground field or exponent width at a given input. -/
noncomputable def program [Fintype P] : UniversalMachine.Program :=
  BinaryMachine.program ps outputPort (machine frobenius) (machine label)

variable {p d v w t Z : ℕ} [Fact p.Prime] {K A : Type} [Field K] [Fintype K]
    [Algebra (ZMod p) K] [CommRing A] [Algebra K A] [Algebra (ZMod p) A]
    [IsScalarTower (ZMod p) K A] {c : Vector p (d+1)}
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K) (dim : BurstRAM.Word v)
    (extra : Stacks P) (u : Fin dim.val) (basis : Module.Basis (Fin dim.val) K A)
    (X : Fin t → A) (es : Fin t → BurstRAM.Word Z) (divisor : List Bool)

local notation "pay" => payload φ dim extra w
local notation "T" f => WeightedStep.ticks v (d+1) w f

/-- Equation (8.2) for the actual bit-stack machine, assuming just correctness
and running times for the two deterministic coordinate-entry readers on the
advised matrix data. The scalar update and nondeterministic control are the
concrete programs of the preceding modules. -/
theorem count_from_readers (hp : ps.Nodup) (hall : ∀ a, a ∈ ps) (hunit : basis u = 1)
    (hu : u.val = 0) (hw : Word.workingWidth p ≤ w)
    (hcoord : ∀ y, SliceEvaluator.primeCoordinate p K (φ (value (modulus c) y)) =
      ((y (0 : Fin (d+1))).val : ZMod p))
    (hd : TapeWord.value divisor = Fintype.card K)
    (R F L : ℕ) (hr : ∀ s, readTicks ps es divisor (pay s) ≤ R)
    (hf : ReadsEntry φ dim extra frobenius w 0 F
      ((LinearMap.toMatrixAlgEquiv basis) (FiniteField.frobeniusAlgHom K A).toLinearMap).transpose)
    (hl : ∀ i : Fin t, ReadsEntry φ dim extra label w i.val L
      ((LinearMap.toMatrixAlgEquiv basis) (LinearMap.mulLeft K (X i))).transpose)
    (fuel : ℕ) (ht : 3*w+3+v + (R + (EvaluatorProgramInput.convertTicks t Z divisor.length +
      EvaluatorMonomialSchedule.budget t Z divisor.length (TapeWord.value divisor) (T F) (T L))) ≤ fuel) :
    let r := (BinaryMachine.evaluator ps outputPort (machine frobenius) (machine label)).body
    let raw := advice ps t divisor (pay (u,1)) ++ runtime es
    (stackPaths (r.close false) fuel (some r.entry) (StackCompiler.labeledInput none raw) : ZMod p) =
      primeFunctional basis u (SliceEvaluator.primeCoordinate p K) (∏ i, X i ^ (es i).val) := by
  exact BinaryMachine.stackCount_mod basis u (SliceEvaluator.primeCoordinate p K) X es divisor pay
    outputPort (machine frobenius) (machine label) (T F) (T L) ps hp hall outputPort_injective hunit hu
    dim.isLt.le hw hd (fun s ↦ output_data dim extra φ hcoord hw s.1 s.2) R hr
    (frobenius_realizes φ dim extra basis X es divisor (by omega) hw frobenius F hf)
    (label_callback φ dim extra basis X es divisor (by omega) hw label L hl) fuel ht

end Evaluator.MatrixCallbacks

end VPVNP
end Computability
end OAI
