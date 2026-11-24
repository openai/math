import OAI.Computability.VPVNP.FixedCompressionModels
import OAI.Computability.VPVNP.FixedNativeProgram
import OAI.Computability.VPVNP.SeparationConsequences

/-!
# Choosing the exceptional length after the literal program

The same pair table, evaluator, public operand formulas, and layout powers
serve every candidate length. The actual compiled coefficient machine then
has one common eventual threshold. At a candidate small-circuit length the
integer equations supply the prime and a finite algebra. Only at that point
are the advice, weighted paths and evaluator configurations selected.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal

universe u
set_option maxHeartbeats 2000000

open Compression BurstRAM LiveProgram RAMTape LabelEvaluator Filter MvPolynomial

namespace Program

variable (D : Program) {K : Type*} [Field K] {S : BlockSchedule K} (B : S.Templates)

theorem contradiction (q C : ℕ) (localRuns : D.Realizes B q C)
    (hsmall : ∀ N, ∃ n ≥ N, circuitSize (map (Int.castRingHom K) (P n)) ≤ n^C)
    (models : ∀ n (hn : 2 ≤ n), circuitSize (map (Int.castRingHom K) (P n)) ≤ n^C →
      ∃ p : Nat.Primes, (q ≠ 0 → p.val = q) ∧ (q = 0 → p.val ≤ 2^B.compressorPrimeBits C n) ∧
        Nonempty (Model p (B.compressorDegree n) (B.compressorEquations hn C))) : False := by
  have localAt := (eventually_atTop.1 localRuns)
  obtain ⟨N₁, hN₁⟩ := localAt
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (LiveTranscript.eventually_coefficients D.native D.operands
    D.addressFactor D.numerator D.denominator D.initialLiteral D.address_pos D.denominator_pos D.bucket_lt)
  obtain ⟨n, hn, small⟩ := hsmall (max 2 (max N₁ N₂))
  have hn₂ : 2 ≤ n := (le_max_left ..).trans hn
  have hn₁ : N₁ ≤ n := (le_max_left ..).trans ((le_max_right ..).trans hn)
  have hn' : N₂ ≤ n := (le_max_right ..).trans ((le_max_right ..).trans hn)
  obtain ⟨hg,cert⟩ := hN₁ n hn₁
  have atGeometry := hN₂ n hn'
  rw [← D.literal_eq] at atGeometry
  change D.OperandFits n → LiveTranscript.Coefficients D.literal (D.liveMachine n)
    n (D.geometry n).d (roundedUp D.numerator D.denominator n) (n^10000)
    (Fin.ofNat (2^(D.geometry n).w) D.initialLiteral) at atGeometry
  have sites : LiveTranscript.Coefficients D.literal (D.liveMachine n)
      n (D.geometry n).d (roundedUp D.numerator D.denominator n) (n^10000)
      (Fin.ofNat (2^(D.geometry n).w) D.initialLiteral) := by exact (by assumption : D.OperandFits n → _) (by assumption)
  obtain ⟨p,hp,hsize,hM⟩ := models n hn₂ small
  obtain ⟨_,⟨L⟩⟩ := cert hn₂ p hp hsize hM sites.fits
  exact L.false_of_processor sites.count

end Program

/-- This implication discharges the field quantifiers, the arithmetic
specialization and the physical processor. Its input is the fixed compiler's
eventual local realization on the two compressor templates. -/
theorem uniform_bound_of_local_programs
    (compile : ∀ (C : ℕ), 1 ≤ C → ∀ (q : ℕ) (K : Type) [Field K] [IsAlgClosed K] [Countable K] [CharP K q],
      ∀ (S : BlockSchedule K) (B : S.Templates), (∃ κ : B.Entry → K, B.IsSolution κ) →
        ∃ D : Program, D.Realizes B q C) : UniformPBound.{u} := by
  apply uniform_P_bound_of_diagonal_contradiction
  intro C hC q K _ _ _ _ small
  obtain ⟨S,B,solution,models⟩ := fixed_models_of_small_circuits K q hC small
  obtain ⟨D,localRuns⟩ := compile C hC q K S B solution
  exact D.contradiction B q C localRuns small models

end FixedProgramDiagonal

end VPVNP
end Computability
end OAI
