import OAI.Computability.VPVNP.CompressorLabelEvaluator
import OAI.Computability.VPVNP.EvaluatorAdviceSerialization

/-!
# Polynomial-length slice advice for the joint compressor labels

The prime header allows the fixed positive characteristic, as well as the
good prime chosen at the current length in characteristic zero. With that
header width one fixed padding exponent accommodates the actual serialized
finite-field presentation and all affine-slice pin data.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open JointLabelSystem LabelEvaluator EvaluatorAdviceSerialization SliceArithmetic

local instance advicePrimeFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩
/-- Finite enumeration of the slice ground field used to encode the evaluator's advice. -/
noncomputable local instance adviceGroundFintype (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) :=
  Fintype.ofFinite _

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)

/-- The extra high bit ensures the prime fits even at equality in the
characteristic-zero estimate. -/
noncomputable def compressorHeaderWidth (q c n : ℕ) :=
  Nat.clog 2 q + B.compressorPrimeBits c n + 1

theorem compressorHeaderWidth_polynomial (q c : ℕ) :
    PolynomiallyBounded (B.compressorHeaderWidth q c) :=
  ((PolynomiallyBounded.const _).add (B.compressorPrimeBits_polynomial c)).add (.const 1)

theorem prime_fits_compressorHeader {q c n : ℕ} (p : Nat.Primes) (hp : q ≠ 0 → p.val = q)
    (hzero : q = 0 → p.val ≤ 2 ^ B.compressorPrimeBits c n) :
    p.val < 2 ^ B.compressorHeaderWidth q c n := by
  unfold compressorHeaderWidth
  apply lt_of_le_of_lt _ (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self _))
  by_cases hq : q = 0
  · exact (hzero hq).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left ..))
  · rw [hp hq]
    exact (Nat.le_pow_clog (by decide) _).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..))

/-- A single length exponent works for the slice advice of every eventual
small circuit and every admitted prime of the fixed characteristic. -/
theorem exists_compressorAdvicePadding (q c : ℕ) :
    ∃ a N : ℕ, ∀ n ≥ N, ∀ p : Nat.Primes,
      (q ≠ 0 → p.val = q) → (q = 0 → p.val ≤ 2 ^ B.compressorPrimeBits c n) →
      let t := B.compressorLabelCount c n
      let d := B.compressorDegree n
      length (B.compressorHeaderWidth q c n) p.val (degree p.val t d) t ≤ n ^ a := by
  obtain ⟨a, N, ha⟩ := exists_advice_padding (B.compressorHeaderWidth_polynomial q c)
    (B.compressorLabelCount_polynomial c) B.compressorDegree_polynomial.clog
  exact ⟨a, N, fun n hn p hp hz ↦ ha n hn p (B.prime_fits_compressorHeader p hp hz)⟩

/-- The actual finite-slice advice decoded by the evaluator. The prescribed
padding may be followed by additional public fields. The field presentation
preserves the coordinate used for the final prime-field tally. -/
theorem exists_compressorEvaluatorTape (q c : ℕ) :
    ∃ a N : ℕ, ∀ n ≥ N, ∀ (hn : 2 ≤ n) (p : Nat.Primes)
      (M : Model p (B.compressorDegree n) (B.compressorEquations hn c)),
      (q ≠ 0 → p.val = q) → (q = 0 → p.val ≤ 2 ^ B.compressorPrimeBits c n) →
      let t := B.compressorLabelCount c n
      let d := B.compressorDegree n
      let e := degree p.val t d
      ∃ (tape : List Bool) (advice : Fields p.val e t), tape.length ≤ n ^ a ∧
        (∀ tail, parse (B.compressorHeaderWidth q c n) t d (tape ++ tail) = some ⟨p, advice⟩) ∧
        ∃ φ : AdjoinRoot (modulus advice.coefficients) ≃ₐ[ZMod p.val] Ground p t d,
          Irreducible (modulus advice.coefficients) ∧
          (∀ i, advice.pins i = decide (i ∈ M.pins)) ∧
          (∀ i, φ (value (modulus advice.coefficients) (advice.values i)) = M.values i) ∧
          ∀ v : SliceArithmetic.Vector p.val e,
            SliceEvaluator.primeCoordinate p.val (Ground p t d)
              (φ (value (modulus advice.coefficients) v)) =
                ((v ⟨0, Nat.succ_pos _⟩).val : ZMod p.val) := by
  obtain ⟨a, N, hsize⟩ := B.exists_compressorAdvicePadding q c
  refine ⟨a, N, fun n hN hn p M hp hz ↦ ?_⟩
  obtain ⟨tape, hlen, advice, hparse, φ, hirr, hpins, hvals, hcoord⟩ :=
    exists_model_advice M (B.prime_fits_compressorHeader p hp hz)
  exact ⟨tape, advice, hlen.le.trans (hsize n hN p hp hz), hparse, φ, hirr, hpins, hvals, hcoord⟩

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
