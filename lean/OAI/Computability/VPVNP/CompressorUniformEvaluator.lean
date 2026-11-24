import OAI.Computability.VPVNP.CompressorEvaluatorInput

/-!
# Uniform compilation of the joint label evaluator

The scalar-query implementation provides its two fixed tables and a polynomial
length envelope for their physical inputs. This theorem composes that interface
with algebraic descent, the canonical monomial basis, nondeterministic
evaluation and the literal two-tape compiler. Its exponent and threshold are
chosen before the input length, prime, solution, exponent width or processor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open MvPolynomial LabelEvaluator RAMTape Evaluator.MatrixCallbacks EvaluatorProgramRawInput
open Evaluator.BinaryMachine LiveEvaluatorEncoding

local instance uniformEvaluatorPrime (p : Nat.Primes) : Fact p.val.Prime := ⟨p.prop⟩
/-- Finite enumeration of the ground field used by the uniform joint evaluator. -/
noncomputable local instance uniformEvaluatorFintype (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) := Fintype.ofFinite _
/-- Classical equality decision for the ground-field coefficients used by the uniform
evaluator. -/
noncomputable local instance uniformEvaluatorDecidableEq (p : Nat.Primes) (t d : ℕ) : DecidableEq (Ground p t d) := Classical.decEq _
/-- Algebra structure on the ambient field induced by the slice-field embedding. -/
noncomputable local instance uniformEvaluatorAmbientAlgebra (p : Nat.Primes) (t d : ℕ) : Algebra (Ground p t d) (Ambient p) :=
  (SliceField.embed p.val (columnCountBound t d) (Ambient p)).toRingHom.toAlgebra

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
    {P : Type} [DecidableEq P] [Fintype P]
    (ps : List (Evaluator.WeightedStep.Port P)) (hps : ps.Nodup) (hall : ∀ x, x ∈ ps)
    (frob label : FiniteRoutine (ReadPort P)) (q c : ℕ) [CharP k q]

local notation "ports" => Fintype.card (MachinePort (Evaluator.WeightedStep.Port P))

include hps hall in
/-- The uniform fixed-code evaluator conclusion, with its physical reader
interface left explicit for assembly of the deterministic Cramer routines. -/
theorem uniform_evaluator_of_coordinate_readers (a : ℕ → ℕ) (ha : PolynomiallyBounded a) (N : ℕ)
    (prepare : ∀ n ≥ N, ∀ (hn : 2 ≤ n) (p : Nat.Primes),
      (q ≠ 0 → p.val = q) → (q = 0 → p.val ≤ 2^B.compressorPrimeBits c n) →
      ∀ M : Model p (B.compressorDegree n) (B.compressorEquations hn c),
        ∃ H : B.SliceReaderAdvice M frob label, H.envelope ps ≤ a n) :
    let E := Evaluator.MatrixCallbacks.program ps frob label
    ∃ C N' : ℕ, ∀ n ≥ N', ∀ hn : 2 ≤ n,
      (∃ x : Fin (B.compressorLabelCount c n) → k,
        ∀ i, eval₂ (Int.castRingHom k) x (B.compressorEquations hn c i) = 0) →
      ∃ p : Nat.Primes, (q ≠ 0 → p.val = q) ∧ (q = 0 → p.val ≤ 2^B.compressorPrimeBits c n) ∧
      ∃ M : Model p (B.compressorDegree n) (B.compressorEquations hn c),
      ∃ adviceBits : List Bool, adviceBits.length ≤ n^C ∧
      Finite M.algebra ∧ IsReduced M.algebra ∧ M.functional 1 = 1 ∧
      (∀ i, eval₂ (Int.castRingHom M.algebra) M.labels (B.compressorEquations hn c i) = 0) ∧
      ∀ Z (es : Fin (B.compressorLabelCount c n) → BurstRAM.Word Z),
        let raw := adviceBits ++ runtime es
        UniversalMachine.AllHalt E (2^(n^C)*(Z+1)^4) (UniversalMachine.initial E raw) ∧
        (∀ ticks ≥ 2^(n^C)*(Z+1)^4,
          (UniversalMachine.paths E ticks (UniversalMachine.initial E raw) : ZMod p.val) =
            M.functional (∏ i, M.labels i ^ (es i).val)) ∧
        (∀ choices, let disp := choiceDisplacement E (UniversalMachine.initial E raw) choices
          RAMTape.StackCompiler.HeadBox (2240*(ports+1)*(n^C+Z+1)^4) disp.1 disp.2) ∧
        ∀ time (bits : Fin time → Bool) (i : Fin (time+1)),
          StateFits (2240*(ports+1)*(n^C+Z+1)^4)
            (EvaluatorTail.history E time (UniversalMachine.initial E raw) bits i) := by
  intro E
  obtain ⟨C,N₀,hC⟩ := exists_uniform_clock ha
  refine ⟨C,max N N₀,fun n hn htwo hx ↦ ?_⟩
  obtain ⟨x, hx⟩ := hx
  obtain ⟨p,hp,hz,⟨M⟩⟩ := B.exists_compressorModel_of_solution q htwo x hx
  obtain ⟨H,hH⟩ := prepare n ((le_max_left ..).trans hn) htwo p hp hz M
  let D := B.compressorCanonical htwo c M
  let M' := M.withCanonicalPresentation D
  have ha' : 6*a n+23 ≤ n^C := by
    have he := hC n ((le_max_right ..).trans hn) 0
    simp only [Nat.zero_add, one_pow, Nat.mul_one] at he
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp he
  have env : H.envelope ps ≤ n^C := by omega
  refine ⟨p,hp,hz,M',H.binary ps,(H.binary_le ps).trans env,
    M'.finite_algebra,M'.reduced,M'.functional_one,M'.solution,fun Z es ↦ ?_⟩
  let ticks := 2^(n^C)*(Z+1)^4
  have clock : 2^(6*H.envelope ps+23)*(Z+1)^4 ≤ ticks :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
  have result := H.resources_and_value ps hps hall es ticks clock
  have hsize : 2240*(ports+1)*(H.envelope ps+Z+1)^4 ≤ 2240*(ports+1)*(n^C+Z+1)^4 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  refine ⟨result.1, fun t ht ↦ (H.evaluate ps hps hall es t (clock.trans ht)).1, fun choices ↦ ?_,
    fun time bits i ↦ LiveEvaluatorRadius.fits_mono hsize _ (result.2.2.2 time bits i)⟩
  have small := result.2.2.1 choices
  exact small.mono hsize

omit [CharP k q] in
/-- Per-component size bounds on concrete initialized readers yield the common
length envelope needed for uniform compilation, even if the advised prime and
slice vary across lengths. -/
theorem exists_reader_envelope (iw e lw s peak exp : ℕ → ℕ)
    (hiw : PolynomiallyBounded iw) (he : PolynomiallyBounded e) (hlw : PolynomiallyBounded lw)
    (hs : PolynomiallyBounded s) (hpeak : PolynomiallyBounded peak) (hexp : PolynomiallyBounded exp)
    (N : ℕ)
    (ready : ∀ n ≥ N, ∀ (hn : 2 ≤ n) (p : Nat.Primes),
      (q ≠ 0 → p.val = q) → (q = 0 → p.val ≤ 2^B.compressorPrimeBits c n) →
      ∀ M : Model p (B.compressorDegree n) (B.compressorEquations hn c),
        ∃ H : B.SliceReaderAdvice M frob label,
          H.indexWidth ≤ iw n ∧ H.degreePred+1 ≤ e n ∧ H.limbWidth ≤ lw n ∧
          H.extraSpace ≤ s n ∧ H.peak ≤ peak n ∧ H.queryExponent ≤ exp n) :
    ∃ a : ℕ → ℕ, PolynomiallyBounded a ∧ ∀ n ≥ N, ∀ (hn : 2 ≤ n) (p : Nat.Primes),
      (q ≠ 0 → p.val = q) → (q = 0 → p.val ≤ 2^B.compressorPrimeBits c n) →
      ∀ M : Model p (B.compressorDegree n) (B.compressorEquations hn c),
        ∃ H : B.SliceReaderAdvice M frob label, H.envelope ps ≤ a n := by
  let a (n : ℕ) := lengthEnvelope (B.compressorLabelCount c n) (B.fieldWordBound q c n) ps.length
    (ports) (iw n) (e n) (lw n) (s n) (peak n) (exp n)
  refine ⟨a, lengthEnvelope_polynomial _ _ (B.compressorLabelCount_polynomial c)
    (B.fieldWordBound_polynomial q c) hiw he hlw hs hpeak hexp, ?_⟩
  intro n hn htwo p hp hz M
  obtain ⟨H, h₁, h₂, h₃, h₄, h₅, h₆⟩ := ready n hn htwo p hp hz M
  exact ⟨H, lengthEnvelope_mono le_rfl (B.field_parameters_le q c n p hp hz).1 h₁ h₂ h₃ h₄ h₅ h₆⟩

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
