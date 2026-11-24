import OAI.Computability.VPVNP.CompressorEvaluatorWidths
import OAI.Computability.VPVNP.EvaluatorUniformBounds
import OAI.Computability.VPVNP.LiveEvaluatorRadius
import OAI.Computability.VPVNP.RAMTapePhysicalHalting

/-!
# Advised coordinate readers for the compressor label system

This record describes the exact binary interface between the deterministic
coordinate queries and the fixed nondeterministic evaluator. All fields are
selected at the input length, before the exponent vector and its width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open LabelEvaluator SliceArithmetic RAMTape Evaluator Evaluator.MatrixCallbacks
open EvaluatorProgramRawInput Evaluator.BinaryMachine LiveEvaluatorEncoding UniversalMachine

local instance readerInputPrime (p : Nat.Primes) : Fact p.val.Prime := ⟨p.prop⟩
/-- Finite enumeration of the ground field used by the matrix-entry readers. -/
noncomputable local instance readerInputFintype (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) := Fintype.ofFinite _
/-- Decidable equality of slice ground-field elements for the evaluator input construction. -/
noncomputable local instance readerInputDecidableEq (p : Nat.Primes) (t d : ℕ) : DecidableEq (Ground p t d) := Classical.decEq _
/-- Ambient algebra structure induced by the ground-field embedding used in the reader
presentation. -/
noncomputable local instance readerInputAmbientAlgebra (p : Nat.Primes) (t d : ℕ) : Algebra (Ground p t d) (Ambient p) :=
  (SliceField.embed p.val (columnCountBound t d) (Ambient p)).toRingHom.toAlgebra

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
    {n c : ℕ} {hn : 2 ≤ n} {p : Nat.Primes} {P : Type} [DecidableEq P]
    (M : Model p (B.compressorDegree n) (B.compressorEquations hn c))
    (frob label : FiniteRoutine (ReadPort P))

/-- The physical advice and two verified entry readers for this particular
finite slice. The counters and field inputs are common to all later calls. -/
structure SliceReaderAdvice where
  /-- One less than the extension degree in the polynomial presentation supplied to the reader. -/
  degreePred : ℕ
  /-- Prime-field coefficients specifying the monic modulus for the advised field presentation. -/
  coefficients : Vector p.val (degreePred+1)
  /-- Algebra isomorphism identifying residue classes modulo the advised modulus with elements
  of the slice ground field. -/
  fieldMap : AdjoinRoot (modulus coefficients) ≃ₐ[ZMod p.val] Ground p (B.compressorLabelCount c n) (B.compressorDegree n)
  primeCoordinate (y) : SliceEvaluator.primeCoordinate p.val _ (fieldMap (value (modulus coefficients) y)) =
    ((y (0 : Fin (degreePred+1))).val : ZMod p.val)
  /-- Bit width used to address rows and columns of the advised query matrices. -/
  indexWidth : ℕ
  dimensionFits : (M.queryData (B.compressorCoeff hn c)).dimension < 2^indexWidth
  /-- Width of the arithmetic limbs used by the entry readers, large enough for their
  prime-field operations. -/
  limbWidth : ℕ
  widthFits : Word.workingWidth p.val ≤ limbWidth
  /-- Auxiliary input stacks made available to the Frobenius and label matrix readers. -/
  extra : Stacks P
  /-- Common upper bound on the length of each auxiliary reader stack. -/
  extraSpace : ℕ
  extraFits (a : P) : (extra a).length ≤ extraSpace
  /-- Peak space bound shared by the Frobenius and label entry-reading routines. -/
  peak : ℕ
  /-- Exponent specifying the power-of-two time budget for one advised matrix-entry query. -/
  queryExponent : ℕ
  frobeniusRead : ReadsEntryWithin fieldMap (M.dimensionWord dimensionFits) extra frob limbWidth 0
    (2^queryExponent) peak (fun src dest ↦ (M.queryData (B.compressorCoeff hn c)).matrixEntry .frobenius dest src)
  labelRead (j : Fin (B.compressorLabelCount c n)) :
    ReadsEntryWithin fieldMap (M.dimensionWord dimensionFits) extra label limbWidth j.val (2^queryExponent) peak
      (fun src dest ↦ (M.queryData (B.compressorCoeff hn c)).matrixEntry (.label j) dest src)

variable {B M frob label} (H : B.SliceReaderAdvice M frob label) (ps : List (WeightedStep.Port P))

local notation "t" => B.compressorLabelCount c n
local notation "divisor" => cardinalBits p (B.compressorLabelCount c n) (B.compressorDegree n)
local notation "dimWord" => M.dimensionWord H.dimensionFits
local notation "D" => B.compressorCanonical hn c M
local notation "ports" => MachinePort (WeightedStep.Port P)

/-- All persistent advice fields of the actual evaluator at this length. -/
noncomputable def SliceReaderAdvice.binary : List Bool :=
  let u := (D).ordinal.symm (D).presentation.unitIndex
  advice ps (t) (divisor) (payload H.fieldMap dimWord H.extra H.limbWidth (u,1))

/-- Joint width, workspace and query-time exponent envelope for this length. -/
noncomputable def SliceReaderAdvice.envelope [Fintype P] : ℕ :=
  lengthEnvelope (t) (divisor).length ps.length (Fintype.card ports)
    H.indexWidth (H.degreePred+1) H.limbWidth H.extraSpace H.peak H.queryExponent

theorem SliceReaderAdvice.binary_le [Fintype P] : (H.binary ps).length ≤ H.envelope ps := by
  apply (advice_le H.fieldMap dimWord H.extra (divisor) H.extraSpace H.extraFits ps _).trans
  dsimp only [envelope, lengthEnvelope]
  omega

/-- At every exponent width, the fixed table returns the canonical model's
functional and its literal computation stays inside a polynomial tape window. -/
theorem SliceReaderAdvice.resources_and_value [Fintype P] (hps : ps.Nodup) (hall : ∀ k, k ∈ ps) {Z : ℕ}
    (es : Fin (t) → BurstRAM.Word Z) (ticks : ℕ) (hticks : 2^(6*H.envelope ps+23)*(Z+1)^4 ≤ ticks) :
    let E := MatrixCallbacks.program ps frob label
    let raw := H.binary ps ++ runtime es
    UniversalMachine.AllHalt E ticks (UniversalMachine.initial E raw) ∧
    (UniversalMachine.paths E ticks (UniversalMachine.initial E raw) : ZMod p.val) =
      (M.withCanonicalPresentation (D)).functional (∏ j, M.labels j^(es j).val) ∧
      (∀ choices, let disp := choiceDisplacement E (UniversalMachine.initial E raw) choices
        StackCompiler.HeadBox (2240*(Fintype.card ports+1)*(H.envelope ps+Z+1)^4) disp.1 disp.2) ∧
      ∀ time (bits : Fin time → Bool) (i : Fin (time+1)), StateFits
        (2240*(Fintype.card ports+1)*(H.envelope ps+Z+1)^4) (EvaluatorTail.history E time (UniversalMachine.initial E raw) bits i) := by
  let A := adviceCap ps.length (t) (divisor).length (WeightedStep.bankSpace H.indexWidth (H.degreePred+1)
    H.limbWidth H.extraSpace)
  let raw := H.binary ps ++ runtime es
  have hraw : raw.length ≤ A+(2*((t)*Z)+6*Z+4) := by
    rw [show raw = H.binary ps ++ runtime es from rfl, List.length_append, runtime_length]
    apply Nat.add_le_add_right
    exact advice_le H.fieldMap dimWord H.extra (divisor) H.extraSpace H.extraFits ps _
  have htime := uniform_tape_clock (t) Z (divisor).length ps.length (Fintype.card ports)
    H.indexWidth (H.degreePred+1) H.limbWidth H.extraSpace H.peak H.queryExponent
    (TapeWord.value (divisor)) (2^H.queryExponent) (2^H.queryExponent) raw.length
    (TapeWord.value_lt _).le le_rfl le_rfl hraw
  obtain ⟨count, bound⟩ := M.canonical_literal_evaluator (D) H.dimensionFits H.fieldMap H.primeCoordinate
    ps hps hall frob label H.extra H.extraSpace H.extraFits H.widthFits (divisor) (value_cardinalBits ..)
    _ _ H.peak H.frobeniusRead H.labelRead es ticks (htime.trans hticks)
  have hq : 2 ≤ TapeWord.value (divisor) := (value_cardinalBits ..) ▸
    Fintype.one_lt_card (α := Ground p (t) (B.compressorDegree n))
  have stack := stack_from_bounded_matrices ps frob label H.fieldMap dimWord H.extra H.extraSpace H.extraFits
    ((D).ordinal.symm (D).presentation.unitIndex) es (divisor) hps hall H.widthFits _ _ H.peak hq
    _ _ H.frobeniusRead H.labelRead
  have halt := StackCompiler.input_allHalt_labeled none _ _ raw _ ticks stack.1 (htime.trans hticks)
  have hwindow := uniform_window (t) Z (divisor).length ps.length (Fintype.card ports)
    H.indexWidth (H.degreePred+1) H.limbWidth H.extraSpace H.peak H.queryExponent raw.length hraw
  refine ⟨halt,count,fun choices ↦ ?_, fun time bits i ↦
    LiveEvaluatorRadius.fits_mono hwindow _ (LiveEvaluatorSpace.history_fits _ raw _ bound time bits i)⟩
  have small := bound choices
  exact small.mono ((Nat.le_add_left _ _).trans hwindow)

/-- The algebra value and full history window for callers which execute the
table at their own clock. -/
theorem SliceReaderAdvice.evaluate [Fintype P] (hps : ps.Nodup) (hall : ∀ k, k ∈ ps) {Z : ℕ}
    (es : Fin (t) → BurstRAM.Word Z) (ticks : ℕ) (hticks : 2^(6*H.envelope ps+23)*(Z+1)^4 ≤ ticks) :
    let E := MatrixCallbacks.program ps frob label
    let raw := H.binary ps ++ runtime es
    (UniversalMachine.paths E ticks (UniversalMachine.initial E raw) : ZMod p.val) =
      (M.withCanonicalPresentation (D)).functional (∏ j, M.labels j^(es j).val) ∧
      ∀ time (bits : Fin time → Bool) (i : Fin (time+1)), StateFits
        (2240*(Fintype.card ports+1)*(H.envelope ps+Z+1)^4) (EvaluatorTail.history E time (UniversalMachine.initial E raw) bits i) := by
  have h := H.resources_and_value ps hps hall es ticks hticks
  exact ⟨h.2.1, h.2.2.2⟩

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
