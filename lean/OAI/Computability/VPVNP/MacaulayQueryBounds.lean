import OAI.Computability.VPVNP.MacaulaySliceBasis
import OAI.Computability.VPVNP.MacaulayIndexISA

/-!
# Widths of the numerical Macaulay queries

The binary logarithms of the certificate degree, powering exponent, raw
graded keys, and augmented matrix dimensions are bounded using the input
parameters of Lemma 8.2. The fixed radix-scan program uses a common register
width that also covers its digit sum.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex

open PolynomiallyBounded

/-- An explicit common binary word width for every dense ordinal and for
the counting mode. The extra bit accommodates equality with the upper limit. -/
def scanWidth (t D : ℕ) :=
  1 + Nat.clog 2 (2 + rawSize t D + t + t*D)

theorem graded_fits {t D k : ℕ} (hk : k ≤ rawSize t D) :
    ISA.Fits (ISA.graded t D k) (scanWidth t D) := by
  let B := 2 + rawSize t D + t + t*D
  have hb : B < 2 ^ scanWidth t D := by
    have h := Nat.le_pow_clog (b := 2) (by decide) B
    change B < 2^(1 + Nat.clog 2 B)
    rw [pow_add]
    have := Nat.two_pow_pos (Nat.clog 2 B)
    omega
  have hbox : (D+1)^t ≤ rawSize t D := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hbase : D+1 ≤ rawSize t D := Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.succ_pos _))
  dsimp only [B] at hb
  refine ⟨by omega, Nat.succ_pos _, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp [ISA.graded] <;> omega

variable {t e : ℕ → ℕ} {K : ℕ → Type*} (S : (n : ℕ) → QueryData (t n) (e n) (K n))

theorem bounded_rawSize {t D : ℕ → ℕ} (ht : PolynomiallyBounded t)
    (hD : PolynomiallyBounded (fun n => Nat.clog 2 (D n))) :
    PolynomiallyBounded (fun n => Nat.clog 2 (rawSize (t n) (D n))) := by
  have hb := clog_add hD (clog (PolynomiallyBounded.const 1))
  exact clog_mul hb (clog_pow hb ht)

theorem bounded_scanWidth {t D : ℕ → ℕ} (ht : PolynomiallyBounded t)
    (hD : PolynomiallyBounded (fun n => Nat.clog 2 (D n))) :
    PolynomiallyBounded (fun n => scanWidth (t n) (D n)) :=
  (PolynomiallyBounded.const 1).add
    (clog_add (clog_add (clog_add (clog (PolynomiallyBounded.const 2)) (bounded_rawSize ht hD)) (clog ht))
      (clog_mul (clog ht) hD))

/-- Row and column dimensions, and the word widths of each monomial lookup,
are polynomial on a binary logarithmic scale for the exact QueryData parameters. -/
theorem bounded_query_dimensions
    (ht : PolynomiallyBounded t) (he : PolynomiallyBounded (fun n => Nat.clog 2 (e n)))
    (hQ : PolynomiallyBounded (fun n => Nat.clog 2 (S n).fieldOrder))
    (hd : PolynomiallyBounded (fun n => Nat.clog 2 (S n).degreeBound))
    (hN : PolynomiallyBounded (fun n => Nat.clog 2 (S n).pointBound))
    (hQpos : ∀ n, 2 ≤ (S n).fieldOrder) :
    PolynomiallyBounded (fun n => Nat.clog 2 (e n * size (t n) (S n).multiplierDegree + size (t n) (S n).pointBound)) ∧
    PolynomiallyBounded (fun n => Nat.clog 2 (size (t n) (S n).columnDegree)) ∧
    PolynomiallyBounded (fun n => scanWidth (t n) (S n).multiplierDegree) ∧
    PolynomiallyBounded (fun n => scanWidth (t n) (S n).columnDegree) ∧
    PolynomiallyBounded (fun n => scanWidth (t n) (S n).pointBound) := by
  have one := clog (PolynomiallyBounded.const 1)
  have hR : PolynomiallyBounded (fun n => Nat.clog 2 (S n).targetDegree) := clog_mul (clog_add hN one) hQ
  have hmax : PolynomiallyBounded (fun n => Nat.clog 2 (max (S n).degreeBound ((S n).targetDegree+1))) :=
    (clog_add hd (clog_add hR one)).of_le fun n => Nat.clog_mono_right _ (by omega)
  have hH : PolynomiallyBounded (fun n => Nat.clog 2 (S n).certificateDegree) :=
    clog_pow (clog_mul (clog (PolynomiallyBounded.const 2)) hmax)
      ((PolynomiallyBounded.const 4).mul (ht.add (PolynomiallyBounded.const 3)))
  have hs : PolynomiallyBounded (fun n => (S n).powerExponent) := hH.of_le fun n =>
    Nat.clog_anti_left (by decide) (hQpos n)
  have hP : PolynomiallyBounded (fun n => Nat.clog 2 (S n).power) := clog_pow hQ hs
  have hL : PolynomiallyBounded (fun n => Nat.clog 2 (S n).multiplierDegree) := clog_add hH (clog_mul hP hR)
  have hD : PolynomiallyBounded (fun n => Nat.clog 2 (S n).columnDegree) := clog_add hL hd
  have hsize (D : ℕ → ℕ) (hb : PolynomiallyBounded (fun n => Nat.clog 2 (D n))) :
      PolynomiallyBounded (fun n => Nat.clog 2 (size (t n) (D n))) := by
    simpa only [size_eq_card] using polynomiallyBounded_clog_boundedMonomial ht hb
  exact ⟨clog_add (clog_mul he (hsize _ hL)) (hsize _ hN), hsize _ hD,
    bounded_scanWidth ht hL, bounded_scanWidth ht hD, bounded_scanWidth ht hN⟩

end RadicalCertificate.MonomialIndex

end VPVNP
end Computability
end OAI
