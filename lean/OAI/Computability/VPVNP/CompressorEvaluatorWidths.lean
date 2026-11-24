import OAI.Computability.VPVNP.CompressorEvaluatorAdvice
import OAI.Computability.VPVNP.CompressorLabelReadback
import OAI.Computability.VPVNP.EvaluatorCanonicalLiteral

/-!
# Uniform field widths and the canonical compressor presentation

The physical slice-field representation, including the Frobenius divisor and
Fermat-inversion workspace, uses a width bounded before choosing the advised
prime or the exponent array. The indexed matrices come from the same joint
grammar and compressor equations used by the algebraic descent.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open LabelEvaluator EvaluatorAdviceSerialization SliceArithmetic MvPolynomial
open JointLabelSystem RadicalCertificate.MonomialIndex

local instance fieldWidthPrime (p : Nat.Primes) : Fact p.val.Prime := ⟨p.prop⟩
/-- Finite enumeration of the slice ground field used when bounding its physical
representation. -/
noncomputable local instance fieldWidthFintype (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) := Fintype.ofFinite _
/-- Decidable equality of elements of the slice ground field used in the width calculation. -/
noncomputable local instance fieldWidthDecidableEq (p : Nat.Primes) (t d : ℕ) : DecidableEq (Ground p t d) := Classical.decEq _
/-- Algebra structure induced on the ambient field by the slice embedding for the given column
bound. -/
noncomputable local instance fieldWidthAmbientAlgebra (p : Nat.Primes) (t d : ℕ) : Algebra (Ground p t d) (Ambient p) :=
  (SliceField.embed p.val (columnCountBound t d) (Ambient p)).toRingHom.toAlgebra

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Width for field limbs and their Fermat-inversion counters. -/
noncomputable def fieldWordBound (q c n : ℕ) :=
  2*(1+Nat.clog 2 (columnCountBound (B.compressorLabelCount c n) (B.compressorDegree n))+
    B.compressorHeaderWidth q c n)+1

theorem fieldWordBound_polynomial (q c : ℕ) : PolynomiallyBounded (B.fieldWordBound q c) := by
  have hc := columnCountBound_clog (B.compressorLabelCount_polynomial c) B.compressorDegree_polynomial.clog
  have hh := B.compressorHeaderWidth_polynomial q c
  exact (((PolynomiallyBounded.const 2).mul (((PolynomiallyBounded.const 1).add hc).add hh)).add (.const 1))

/-- Choose the actual bit array for the field-cardinality divisor with one
extra bit so a cardinality which is a power of two is encoded literally. -/
noncomputable def cardinalBits (p : Nat.Primes) (t d : ℕ) : List Bool :=
  let N := Fintype.card (Ground p t d)
  BurstRAM.wordBits (⟨N, (Nat.le_pow_clog (by decide : 1 < 2) N).trans_lt
    (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))⟩ : BurstRAM.Word (Nat.clog 2 N+1))

@[simp] theorem value_cardinalBits (p : Nat.Primes) (t d : ℕ) :
    TapeWord.value (cardinalBits p t d) = Fintype.card (Ground p t d) := TapeWord.value_wordBits _

@[simp] theorem length_cardinalBits (p : Nat.Primes) (t d : ℕ) :
    (cardinalBits p t d).length = Nat.clog 2 (Nat.card (Ground p t d))+1 := by
  rw [Nat.card_eq_fintype_card]; exact BurstRAM.length_wordBits _

/-- Every allowed characteristic uses the same length bounds for the input
divisor, extension degree and required field working width. -/
theorem field_parameters_le (q c n : ℕ) (p : Nat.Primes) (hp : q ≠ 0 → p.val = q)
    (hz : q = 0 → p.val ≤ 2 ^ B.compressorPrimeBits c n) :
    let t := B.compressorLabelCount c n
    let d := B.compressorDegree n
    let e := degree p.val t d
    (cardinalBits p t d).length ≤ B.fieldWordBound q c n ∧ e ≤ B.fieldWordBound q c n ∧
      max (Word.workingWidth p.val) (e*Nat.clog 2 p.val+1) ≤ B.fieldWordBound q c n := by
  intro t d e
  have hprime := (B.prime_fits_compressorHeader p hp hz).le
  have hlog := Nat.clog_le_of_le_pow hprime
  have hcard := ground_card_clog_le p t d _ hprime
  have hlimb := elementWidth_le p t d _ hprime
  have he := extensionDegree_le_width p t d
  change e * Nat.clog 2 p.val ≤ _ at hlimb
  change e ≤ e*Nat.clog 2 p.val at he
  rw [length_cardinalBits]
  unfold fieldWordBound Word.workingWidth
  dsimp only [t,d] at hcard hlimb ⊢
  exact ⟨by omega, by omega, max_le (by omega) (by omega)⟩

/-- The canonical monomial listing for the actual two-block compressor model.
Its integer reader addresses word equations first, followed by the two fixed
templates' equations. -/
noncomputable def compressorCanonical {p : Nat.Primes} {n : ℕ} (hn : 2 ≤ n) (c : ℕ)
    (M : Model p (B.compressorDegree n) (B.compressorEquations hn c)) :
    (M.queryData (B.compressorCoeff hn c)).Canonical (E := Ambient p)
      (sliceIdeal p (B.compressorDegree n) (B.compressorEquations hn c) M.pins M.values) :=
  M.canonicalPresentation (FixedRows.rowIndex B.EquationIndex n) (B.compressorCoeff hn c)
    (le_max_left ..) (B.compressorEquation_degree hn c) (B.compressorCoeff_eq hn c)

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
