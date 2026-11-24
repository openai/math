import OAI.Computability.VPVNP.EvaluatorMatrixCallbacks

/-!
# Coordinate-reader interface for the binary evaluator

The deterministic entry query takes the previous and chosen basis ordinals
in canonical binary registers. Its output is a packed element in the advised
field basis. This interface isolates the indexed Macaulay and Cramer computation
from the nondeterministic choices, finite-field multiplication and digit loops.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator.MatrixCallbacks

open RAMTape SliceArithmetic EvaluatorRoutine EvaluatorDigitFetch EvaluatorMonomialSchedule
open EvaluatorScheduleEffects

variable {P : Type} [DecidableEq P] {p e w v : ℕ} [Fact p.Prime]
    {K : Type} [Field K] [Algebra (ZMod p) K] {c : Vector p e}
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K) (dim : BurstRAM.Word v) (extra : Stacks P)

/-- Encoded current ordinal and scalar, between two successive linear steps. -/
noncomputable def payload (w : ℕ) (s : Fin dim.val × K) : Stacks (WeightedStep.Port P) :=
  WeightedStep.bank φ w dim s.1 [] [] s.2 extra

/-- Deterministic finite-control entry query with a common time bound. It
restores the ordinal registers, the advised field and the caller's private
workspace. Its only output is the requested matrix entry. -/
def ReadsEntry (read : FiniteRoutine (ReadPort P)) (w label time : ℕ)
    (matrix : Matrix (Fin dim.val) (Fin dim.val) K) : Prop :=
  ∀ (s : Fin dim.val × K) (j : Fin dim.val), ∃ d ≤ time, read.Runs d
    (queryBank (List.replicate label true) (WeightedStep.bank φ w dim s.1
      (BurstRAM.wordBits (Fin.castLE dim.isLt.le j : BurstRAM.Word v)) [] s.2 extra))
    (queryBank (List.replicate label true) (WeightedStep.bank φ w dim s.1
      (BurstRAM.wordBits (Fin.castLE dim.isLt.le j : BurstRAM.Word v))
      (WeightedStep.bits φ w (matrix s.1 j)) s.2 extra))

private theorem count_fixed_frame (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (read : FiniteRoutine (ReadPort P)) (label time : ℕ)
    (matrix : Matrix (Fin dim.val) (Fin dim.val) K)
    (hr : ReadsEntry φ dim extra read w label time matrix)
    (frame : Stacks (WeightedStep.Port P) → Stacks (Host P))
    (hwork : ∀ s k, frame s (.work k) = s k)
    (hlabel : ∀ s, frame s (.addr .labelIndex) = List.replicate label true)
    (hrest : ∀ x y k, (∀ j, EvaluatorDigitFetch.Port.work j ≠ k) → frame x k = frame y k)
    (s : Fin dim.val × K) (fuel : ℕ) (hfuel : WeightedStep.ticks v e w time ≤ fuel) :
    ∃ delay : Fin dim.val → ℕ, (∀ j, delay j ≤ WeightedStep.ticks v e w time) ∧ ∀ cont,
      (machine read).body.count cont fuel (frame (payload φ dim extra w s)) =
        ∑ j, cont (fuel-delay j) (frame (payload φ dim extra w (j, s.2 * matrix s.1 j))) := by
  let ambient := frame (payload φ dim extra w s)
  have hi (x) : installStacks EvaluatorDigitFetch.Port.work ambient x = frame x :=
    installStacks_frame (fun _ _ h ↦ EvaluatorDigitFetch.Port.work.inj h) (hwork x) (hrest x _)
  obtain ⟨d, hd, hc⟩ := count_callback φ dim extra he hw read ambient matrix s.1 s.2 time
    (fun j ↦ by dsimp only [ambient]; rw [hlabel]; exact hr s j) fuel hfuel
  exact ⟨d, hd, fun cont ↦ by simpa only [hi, payload] using hc cont⟩

variable {A : Type} [CommRing A] [Algebra K A] [Fintype K] {t Z : ℕ}
    (b : Module.Basis (Fin dim.val) K A) (X : Fin t → A) (es : Fin t → BurstRAM.Word Z) (d : List Bool)

local notation "data" => EvaluatorRadixRows.packedTable d.length (TapeWord.value d) (List.ofFn es)
local notation "next" => nextIndex b X
local notation "pay" => payload φ dim extra w
local notation "M" => LinearMap.toMatrixAlgEquiv b

/-- Installing a Frobenius entry query gives the counted Frobenius callback
on every column, with the column and digit scheduler registers preserved. -/
theorem frobenius_realizes (he : 0 < e) (hw : Word.workingWidth p ≤ w) (read : FiniteRoutine (ReadPort P))
    (time : ℕ) (hr : ReadsEntry φ dim extra read w 0 time
      (M (FiniteField.frobeniusAlgHom K A).toLinearMap).transpose) (j : Fin Z) (left : ℕ) :
    Realizes (machine read).body (fun x ↦ bank data t Z d.length 0 j 0 left (pay x))
      (fun x ↦ bank data t Z d.length 0 j 0 left (pay x)) (WeightedStep.ticks v e w time)
      (stepEffect next none) := by
  apply Realizes.of_delay
  intro x fuel hf
  apply count_fixed_frame φ dim extra he hw read 0 time _ hr
    (bank data t Z d.length 0 j 0 left) (fun _ _ ↦ rfl) (fun _ ↦ rfl) _ x fuel hf
  intro x y k hk
  cases k <;> first | rfl | exact (hk _ rfl).elim

/-- Installing the formal-coordinate multiplication query gives the label
callback on all live label ordinals, including repeated visits in a digit. -/
theorem label_callback (he : 0 < e) (hw : Word.workingWidth p ≤ w) (read : FiniteRoutine (ReadPort P))
    (time : ℕ) (hr : ∀ i : Fin t, ReadsEntry φ dim extra read w i.val time
      (M (LinearMap.mulLeft K (X i))).transpose) :
    LabelCallback es d.length (TapeWord.value d) (WeightedStep.ticks v e w time) pay next (machine read) := by
  intro i j labels cols x bits fuel _hf enough
  let frame (s : Stacks (WeightedStep.Port P)) := EvaluatorDigitRepeat.frame
    EvaluatorDigitFetch.Port.digit EvaluatorDigitFetch.Port.borrow (bank data t Z d.length i j labels cols s) bits []
  have h := count_fixed_frame φ dim extra he hw read i.val time _ (hr i) frame
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun x y k hk ↦ by
      cases k <;> first | rfl | exact (hk _ rfl).elim) x fuel enough
  simpa only [nextIndex, indexTransition, dite_eq_left i.isLt, Matrix.transpose_apply, frame] using h

end Evaluator.MatrixCallbacks

end VPVNP
end Computability
end OAI
