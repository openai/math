import OAI.Computability.VPVNP.EvaluatorAdviceSerialization
import OAI.Computability.VPVNP.PerronBounds

/-!
# Size of the advice and indices of the finite slice evaluator

The parameters are those of the actual coordinate slice in `LabelEvaluator`.
Its ground field has order greater than twice the Macaulay column bound, and
the geometric point count is bounded by the `t`th power of twice that bound.
Both logarithms are polynomial in the input length.

The advice stores the prime in an agreed width, one field element's worth
of coefficients for the defining polynomial, one selection bit per
coordinate, and one field element per coordinate. All these bounds hold
uniformly over the selected prime once its width is fixed.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LabelEvaluator

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.prop⟩

variable {t d : ℕ → ℕ}

theorem columnCountBound_clog (ht : PolynomiallyBounded t)
    (hd : PolynomiallyBounded fun n => Nat.clog 2 (d n)) :
    PolynomiallyBounded fun n => Nat.clog 2 (columnCountBound (t n) (d n)) :=
  PolynomiallyBounded.clog_pow (PolynomiallyBounded.clog_add
    (PolynomiallyBounded.clog_add (RadicalCertificate.polynomiallyBounded_clog_paperBound ht hd) hd)
    ((PolynomiallyBounded.const 1).clog)) ht

theorem pointCountBound_clog (ht : PolynomiallyBounded t)
    (hd : PolynomiallyBounded fun n => Nat.clog 2 (d n)) :
    PolynomiallyBounded fun n => Nat.clog 2 (pointCountBound (t n) (d n)) :=
  PolynomiallyBounded.clog_pow (PolynomiallyBounded.clog_mul
    ((PolynomiallyBounded.const 2).clog) (columnCountBound_clog ht hd)) ht

/-- Uniform width of indices in the monomial list scanned by the evaluator. -/
theorem listingBound_clog (ht : PolynomiallyBounded t)
    (hd : PolynomiallyBounded fun n => Nat.clog 2 (d n)) :
    PolynomiallyBounded fun n => Nat.clog 2 ((pointCountBound (t n) (d n) + 1) ^ t n) :=
  PolynomiallyBounded.clog_pow (PolynomiallyBounded.clog_add (pointCountBound_clog ht hd)
    ((PolynomiallyBounded.const 1).clog)) ht

/-- This is the extension degree and width used by every coefficient block. -/
abbrev elementWidth (p : Nat.Primes) (t d : ℕ) :=
  SliceField.extensionDegree p.val (columnCountBound t d) * Nat.clog 2 p.val

theorem ground_card_eq (p : Nat.Primes) (t d : ℕ) :
    Nat.card (Ground p t d) = p.val ^ SliceField.extensionDegree p.val (columnCountBound t d) :=
  SliceField.field_card ..

theorem ground_card_clog_le (p : Nat.Primes) (t d w : ℕ) (hp : p.val ≤ 2 ^ w) :
    Nat.clog 2 (Nat.card (Ground p t d)) ≤ 1 + Nat.clog 2 (columnCountBound t d) + w := by
  apply Nat.clog_le_of_le_pow
  have hpos : 0 < columnCountBound t d := Nat.pow_pos (Nat.succ_pos _)
  calc
    Nat.card (Ground p t d) ≤ 2 * columnCountBound t d * p.val := SliceField.field_card_le _ hpos
    _ ≤ 2 * 2 ^ Nat.clog 2 (columnCountBound t d) * 2 ^ w :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) _)) hp
    _ = _ := by simp only [pow_add, pow_one]

theorem elementWidth_le (p : Nat.Primes) (t d w : ℕ) (hp : p.val ≤ 2 ^ w) :
    elementWidth p t d ≤ 2 * (1 + Nat.clog 2 (columnCountBound t d) + w) :=
  (SliceField.advice_length_le _ _).trans (Nat.mul_le_mul_left _
    ((Nat.log_le_clog _ _).trans (ground_card_clog_le p t d w hp)))

theorem extensionDegree_le_width (p : Nat.Primes) (t d : ℕ) :
    SliceField.extensionDegree p.val (columnCountBound t d) ≤ elementWidth p t d :=
  Nat.le_mul_of_pos_right _ (Nat.clog_pos (by decide) p.prop.one_lt)

/-- In characteristic zero the prime-width exponent from the integer minor
is polynomially bounded even when the coefficient bit lengths are themselves
singly exponential. An extra bit represents the prime in the equality case. -/
theorem primeHeaderWidth_polynomiallyBounded {b : ℕ → ℕ} (ht : PolynomiallyBounded t)
    (hd : PolynomiallyBounded fun n => Nat.clog 2 (d n))
    (hb : PolynomiallyBounded fun n => Nat.clog 2 (b n)) :
    PolynomiallyBounded fun n =>
      let a := Nat.clog 2 (multiplierDegree (t n) (d n) + d n + 1) * t n
      (2 * (a + Nat.clog 2 (a + b n + 2)) + 1) + 1 :=
  (RadicalCertificate.polynomiallyBounded_good_prime_bits ht
    (RadicalCertificate.polynomiallyBounded_clog_paperBound ht hd) hd hb).add (.const 1)

/-- Numerical upper bound independent of the prime, for the four fields
(prime header, monic polynomial, pin mask, and pin values). -/
def adviceLengthBound (w t d : ℕ) :=
  let v := 2 * (1 + Nat.clog 2 (columnCountBound t d) + w)
  w + v + t + t * v

theorem adviceLength_le (p : Nat.Primes) (w t d : ℕ) (hp : p.val ≤ 2 ^ w) :
    w + elementWidth p t d + t + t * elementWidth p t d ≤ adviceLengthBound w t d := by
  have h := elementWidth_le p t d w hp
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_left h w) t) (Nat.mul_le_mul_left _ h)

theorem adviceLengthBound_polynomiallyBounded {w : ℕ → ℕ} (hw : PolynomiallyBounded w)
    (ht : PolynomiallyBounded t) (hd : PolynomiallyBounded fun n => Nat.clog 2 (d n)) :
    PolynomiallyBounded fun n => adviceLengthBound (w n) (t n) (d n) := by
  have hv := (PolynomiallyBounded.const 2).mul
    (((PolynomiallyBounded.const 1).add (columnCountBound_clog ht hd)).add hw)
  exact ((hw.add hv).add ht).add (ht.mul hv)

/-- A single padding exponent works for all admissible primes at every
sufficiently large length. In particular it is independent of the evaluator
exponents, pin choices, and later processor prefix. -/
theorem exists_advice_padding {w : ℕ → ℕ} (hw : PolynomiallyBounded w)
    (ht : PolynomiallyBounded t) (hd : PolynomiallyBounded fun n => Nat.clog 2 (d n)) :
    ∃ d₁ N : ℕ, ∀ n ≥ N, ∀ p : Nat.Primes, p.val < 2 ^ w n →
      w n + elementWidth p (t n) (d n) + t n + t n * elementWidth p (t n) (d n) ≤ n ^ d₁ := by
  obtain ⟨A, b, N, h⟩ := adviceLengthBound_polynomiallyBounded hw ht hd
  refine ⟨b + 1, max A N, fun n hn p hp => ?_⟩
  exact (adviceLength_le p _ _ _ hp.le).trans <| (h n ((le_max_right ..).trans hn)).trans <| by
    rw [pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ ((le_max_left ..).trans hn)

/-- Padding the actual chosen advice preserves its decoded prime, pin data,
and field presentation. The length is fixed before selecting a prime or model. -/
theorem exists_padded_model_advice {w : ℕ → ℕ} (hw : PolynomiallyBounded w)
    (ht : PolynomiallyBounded t) (hd : PolynomiallyBounded fun n => Nat.clog 2 (d n)) :
    ∃ d₁ N : ℕ, ∀ n ≥ N, ∀ (p : Nat.Primes) (_ : p.val < 2 ^ w n)
      {ι : Type*} {F : ι → MvPolynomial (Fin (t n)) ℤ} (model : Model p (d n) F),
      ∃ tape : List Bool, tape.length = n ^ d₁ ∧
        ∃ a : EvaluatorAdviceSerialization.Fields p.val
            (EvaluatorAdviceSerialization.degree p.val (t n) (d n)) (t n),
          EvaluatorAdviceSerialization.parse (w n) (t n) (d n) tape = some ⟨p, a⟩ ∧
          ∃ φ : AdjoinRoot (SliceArithmetic.modulus a.coefficients) ≃ₐ[ZMod p.val] Ground p (t n) (d n),
            Irreducible (SliceArithmetic.modulus a.coefficients) ∧
            (∀ i, a.pins i = decide (i ∈ model.pins)) ∧
            (∀ i, φ (SliceArithmetic.value (SliceArithmetic.modulus a.coefficients) (a.values i)) = model.values i) := by
  obtain ⟨d₁, N, hN⟩ := exists_advice_padding hw ht hd
  refine ⟨d₁, N, fun n hn p hp ι F model => ?_⟩
  obtain ⟨bits, hl, a, hparse, φ, hf, hs, hv, _⟩ := EvaluatorAdviceSerialization.exists_model_advice model hp
  have hle : bits.length ≤ n ^ d₁ := hl ▸ hN n hn p hp
  let pad := List.replicate (n ^ d₁ - bits.length) false
  exact ⟨bits ++ pad, by simp [pad, Nat.add_sub_of_le hle], a, hparse pad, φ, hf, hs, hv⟩

end LabelEvaluator

end VPVNP
end Computability
end OAI
