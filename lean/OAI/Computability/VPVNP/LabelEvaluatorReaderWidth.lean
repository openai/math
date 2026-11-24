import OAI.Computability.VPVNP.MacaulayReaderWidth
import OAI.Computability.VPVNP.LabelEvaluatorIndexedPins
import OAI.Computability.VPVNP.EvaluatorAdviceBounds

/-! # Prime-independent word widths for the actual finite-slice equations -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LabelEvaluator

open RadicalCertificate.MonomialIndex PolynomiallyBounded

local instance readerWidthsPrime (p : Nat.Primes) : Fact p.val.Prime := ⟨p.prop⟩
/-- Finite enumeration of the ground field used in bounding the reader's register widths. -/
noncomputable local instance readerWidthsFintype (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) := Fintype.ofFinite _

/-- Address widths chosen before the prime, pins, or target monomial. -/
def readerPlan (m t d primeBits : ℕ) : ReaderPlan :=
  ⟨t,m,t,d,pointCountBound t d,2^(1+Nat.clog 2 (columnCountBound t d)+primeBits)⟩

theorem readerPlan_covers {p : Nat.Primes} {m t d primeBits : ℕ} {ι : Type*}
    {F : ι → MvPolynomial (Fin t) ℤ} (M : Model p d F) (read : Fin m → (Fin t → ℕ) → ℤ)
    (hp : p.val ≤ 2^primeBits) :
    (readerPlan m t d primeBits).Covers (M.queryData read) := by
  refine ⟨Fintype.one_lt_card, ?_, le_rfl, le_rfl⟩
  change Fintype.card (Ground p t d) ≤ 2^(1 + Nat.clog 2 (columnCountBound t d) + primeBits)
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.clog_le_iff_le_pow (by decide : 1<2)).mp (ground_card_clog_le p t d primeBits hp)

/-- Uniform polynomial in the input length for the register width of the
augmented matrix and its target rows. -/
theorem readerWordWidth_polynomial {m t d b : ℕ → ℕ} (hm : PolynomiallyBounded fun n => Nat.clog 2 (m n))
    (ht : PolynomiallyBounded t) (hd : PolynomiallyBounded fun n => Nat.clog 2 (d n))
    (hb : PolynomiallyBounded b) : PolynomiallyBounded (fun n => (readerPlan (m n) (t n) (d n) (b n)).wordWidth) :=
  ReaderPlan.width_polynomial _ ht hm ht.clog hd (pointCountBound_clog ht hd)
    (clog_pow (clog (PolynomiallyBounded.const 2)) (((PolynomiallyBounded.const 1).add (columnCountBound_clog ht hd)).add hb))

/-- Uniform working widths for the coefficient limbs and the number of
extension coefficients staged in each matrix reader. -/
def readerLimbWidth (b : ℕ) := 2*b+1

/-- Bound for the extension degree in terms of the monomial column count and a bound on the
prime's bit length. -/
def readerExtensionBound (t d b : ℕ) := 2*(1+Nat.clog 2 (columnCountBound t d)+b)

theorem readerFieldWidths {p : Nat.Primes} {t d b : ℕ} (hp : p.val ≤ 2^b) :
    SliceArithmetic.Word.workingWidth p.val ≤ readerLimbWidth b ∧
    SliceField.extensionDegree p.val (columnCountBound t d) ≤ readerExtensionBound t d b :=
  ⟨Nat.add_le_add_right (Nat.mul_le_mul_left 2 ((Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr hp)) 1,
    (extensionDegree_le_width p t d).trans (elementWidth_le p t d b hp)⟩

theorem readerFieldWidths_polynomial {t d b : ℕ → ℕ} (ht : PolynomiallyBounded t)
    (hd : PolynomiallyBounded fun n => Nat.clog 2 (d n)) (hb : PolynomiallyBounded b) :
    PolynomiallyBounded (fun n => readerLimbWidth (b n)) ∧
    PolynomiallyBounded (fun n => readerExtensionBound (t n) (d n) (b n)) :=
  ⟨((PolynomiallyBounded.const 2).mul hb).add (.const 1),
    (PolynomiallyBounded.const 2).mul (((PolynomiallyBounded.const 1).add (columnCountBound_clog ht hd)).add hb)⟩

end LabelEvaluator

end VPVNP
end Computability
end OAI
