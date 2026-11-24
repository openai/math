import OAI.Computability.VPVNP.EvaluatorCoordinateMachine
import OAI.Computability.VPVNP.EvaluatorNativeResources
import OAI.Computability.VPVNP.EvaluatorPhysicalBounds

/-!
# Counts, time and space of the literal evaluator from streamed coordinate queries

The program table is fixed by its two coordinate readers. Its correctness and
resources hold simultaneously for all binary exponent arrays. The same bounded
query executions justify both the field-valued path count and all-path storage.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator.MatrixCallbacks

open RAMTape SliceArithmetic EvaluatorChronologicalLoop EvaluatorProgramRawInput
  EvaluatorProgramMonomial BinaryMachine

variable {P : Type} [DecidableEq P] (ps : List (WeightedStep.Port P))
    (frobenius label : FiniteRoutine (ReadPort P))

variable {p d v w t Z : ℕ} [Fact p.Prime] {K A : Type} [Field K] [Fintype K]
    [Algebra (ZMod p) K] [CommRing A] [Algebra K A] [Algebra (ZMod p) A]
    [IsScalarTower (ZMod p) K A] {c : Vector p (d+1)}
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K) (dim : BurstRAM.Word v)
    (extra : Stacks P) (extraSpace : ℕ) (hextra : ∀ k, (extra k).length ≤ extraSpace)
    (u : Fin dim.val) (basis : Module.Basis (Fin dim.val) K A)
    (X : Fin t → A) (es : Fin t → BurstRAM.Word Z) (divisor : List Bool)

local notation "pay" => payload φ dim extra w
local notation "Amax" => adviceCap ps.length t divisor.length (WeightedStep.bankSpace v (d+1) w extraSpace)
local notation "Qsize" => TapeWord.value divisor
local notation "cost" => WeightedStep.ticks v (d+1) w
local notation "room" => workspace v (d+1) w extraSpace
local notation "raw" => advice ps t divisor (pay (u,1)) ++ runtime es
local notation "bankPorts" => MachinePort (WeightedStep.Port P)
local notation "stack" => FiniteRoutine.body (evaluator ps outputPort (machine frobenius) (machine label))

variable (hp : ps.Nodup) (hall : ∀ a, a ∈ ps) (hw : Word.workingWidth p ≤ w)
    (hd : TapeWord.value divisor = Fintype.card K) (F L peak : ℕ)
    (hf : ReadsEntryWithin φ dim extra frobenius w 0 F peak
      ((LinearMap.toMatrixAlgEquiv basis) (FiniteField.frobeniusAlgHom K A).toLinearMap).transpose)
    (hl : ∀ i : Fin t, ReadsEntryWithin φ dim extra label w i.val L peak
      ((LinearMap.toMatrixAlgEquiv basis) (LinearMap.mulLeft K (X i))).transpose)

include hp hall hextra hw in
omit [Fintype K] [Algebra (ZMod p) A] [IsScalarTower (ZMod p) K A] in
/-- The all-path resource proof uses only the two deterministic read contracts
and positivity of the radix. It applies to any two matrices in the field. -/
theorem stack_from_bounded_matrices (hq : 2 ≤ TapeWord.value divisor)
    (MF : Matrix (Fin dim.val) (Fin dim.val) K) (ML : Fin t → Matrix (Fin dim.val) (Fin dim.val) K)
    (hF : ReadsEntryWithin φ dim extra frobenius w 0 F peak MF)
    (hL : ∀ j, ReadsEntryWithin φ dim extra label w j.val L peak (ML j)) :
    StopsWithin ((stack).close false) (fullTicks t Z divisor.length Qsize Amax (cost F) (cost L) v w)
      (some (stack).entry) (StackCompiler.labeledInput none (raw)) ∧
      ∀ ⦃q s⦄, StackCompiler.Reach ((stack).close false) (some (stack).entry)
        (StackCompiler.labeledInput none (raw)) q s →
        stackFits (fullSpace t Z divisor.length (room peak) Amax v w) s := by
  have native := native_from_readers φ dim extra es divisor extraSpace hextra (by omega) hw hq
    frobenius label F L peak _ _ hF hL
  exact full_space_clock es divisor pay (room peak) (payload_length φ dim extra extraSpace hextra peak)
    (machine frobenius) (machine label) (cost F) (cost L) ps hp hall Amax
    (advice_le φ dim extra divisor extraSpace hextra ps) native outputPort outputPort_injective v w
    (fun s ↦ BurstRAM.length_wordBits (Fin.castLE dim.isLt.le s.1 : BurstRAM.Word v))
    (fun _ ↦ List.length_replicate ..) false (u,1)

include hp hall hextra hw hd hf hl in
omit [Algebra (ZMod p) A] [IsScalarTower (ZMod p) K A] in
/-- All paths of the linked bit-stack routine meet their clock and the same
height bound, even when a guessed ordinal is rejected. -/
theorem stack_from_bounded_readers :
    StopsWithin ((stack).close false) (fullTicks t Z divisor.length Qsize Amax (cost F) (cost L) v w)
      (some (stack).entry) (StackCompiler.labeledInput none (raw)) ∧
      ∀ ⦃q s⦄, StackCompiler.Reach ((stack).close false) (some (stack).entry)
        (StackCompiler.labeledInput none (raw)) q s →
        stackFits (fullSpace t Z divisor.length (room peak) Amax v w) s := by
  have hq : 2 ≤ Qsize := hd ▸ Fintype.one_lt_card (α := K)
  exact stack_from_bounded_matrices ps frobenius label φ dim extra extraSpace hextra u es divisor
    hp hall hw F L peak hq _ _ hf hl

include hp hall hextra hw hd hf hl in
/-- Equation (8.2) and the two literal head bounds for the same fixed binary
table. The clock may be enlarged arbitrarily without changing the path count. -/
theorem literal_from_bounded_readers [Fintype P] (hunit : basis u = 1) (hu : u.val = 0)
    (hcoord : ∀ y, SliceEvaluator.primeCoordinate p K (φ (value (modulus c) y)) =
      ((y (0 : Fin (d+1))).val : ZMod p))
    (ticks : ℕ) (hticks : tapeTicks (raw).length (Fintype.card bankPorts)
      (fullTicks t Z divisor.length Qsize Amax (cost F) (cost L) v w) ≤ ticks) :
    let E := MatrixCallbacks.program ps frobenius label
    (UniversalMachine.paths E ticks (UniversalMachine.initial E (raw)) : ZMod p) =
        primeFunctional basis u (SliceEvaluator.primeCoordinate p K) (∏ i, X i ^ (es i).val) ∧
      ∀ bits, let dis := choiceDisplacement E (UniversalMachine.initial E (raw)) bits
        StackCompiler.HeadBox (headRadius (Fintype.card bankPorts)
          (fullSpace t Z divisor.length (room peak) Amax v w)) dis.1 dis.2 := by
  have h := stack_from_bounded_readers ps frobenius label φ dim extra extraSpace hextra u basis X es
    divisor hp hall hw hd F L peak hf hl
  let T := fullTicks t Z divisor.length Qsize Amax (cost F) (cost L) v w
  refine ⟨?_, fun bits ↦ ?_⟩
  · have hcount := count_from_readers ps frobenius label φ dim extra u basis X es divisor hp hall
      hunit hu hw hcoord hd (readerBudget t Z Amax) F L (fun s ↦ by
        apply (readTicks_le ps es divisor (pay s)).trans
        rw [runtime_length]
        have ha := advice_le (w := w) (t := t) φ dim extra divisor extraSpace hextra ps s
        exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.add_le_add_right ha _)) 1)
      (ReadsEntryWithin.readsEntry φ dim extra hf) (fun i ↦ ReadsEntryWithin.readsEntry φ dim extra (hl i)) T le_rfl
    have hphys := program_paths_eq ps outputPort (machine frobenius) (machine label) (raw) T ticks h.1 hticks
    exact (congrArg (fun n : ℕ ↦ (n : ZMod p)) hphys).trans hcount
  · apply program_head_space ps outputPort (machine frobenius) (machine label) (raw) _ bits
    dsimp only
    intro q s path
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦ h.2 path k)
    simpa only [packedCap, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id] using Nat.add_le_add_left hh (Fintype.card bankPorts+1)

end Evaluator.MatrixCallbacks

end VPVNP
end Computability
end OAI
