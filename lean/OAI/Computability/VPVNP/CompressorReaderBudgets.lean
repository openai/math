import OAI.Computability.VPVNP.CompressorEvaluatorAdvice
import OAI.Computability.VPVNP.CompressorLabelReadback
import OAI.Computability.VPVNP.LabelEvaluatorReaderWidth
import OAI.Computability.VPVNP.MacaulayLeafBudgets
import OAI.Computability.VPVNP.JointScalarLeafResources

/-! # Uniform raw matrix-reader budgets for the actual compressor equations

The widths and the two bounds are fixed for the input length and circuit-size
exponent. They cover the prime and affine slice selected from any circuit at
that length, all integer equation queries, and the operation-dependent target
row. The word width can be increased for the outer rank computation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open LabelEvaluator JointLabelSystem RadicalCertificate.MonomialIndex
open PolynomiallyBounded

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Reader plan sized for the compressor's equations, joint labels, degree bound, and advised
prime header. -/
noncomputable def compressorReaderPlan (q c n : ℕ) : ReaderPlan :=
  readerPlan (2^n+Fintype.card B.EquationIndex) (B.compressorLabelCount c n)
    (B.compressorDegree n) (B.compressorHeaderWidth q c n)

/-- Upper bound on the extension degree needed by the compressor reader at the given
characteristic and input length. -/
noncomputable def readerDegreeBudget (q c n : ℕ) :=
  readerExtensionBound (B.compressorLabelCount c n) (B.compressorDegree n) (B.compressorHeaderWidth q c n)

/-- Arithmetic limb-width budget derived from the compressor's prime-header width. -/
noncomputable def readerLimbBudget (q c n : ℕ) :=
  readerLimbWidth (B.compressorHeaderWidth q c n)

theorem compressorReaderWidths (q c : ℕ) :
    PolynomiallyBounded (fun n => (B.compressorReaderPlan q c n).wordWidth) ∧
    PolynomiallyBounded (B.readerDegreeBudget q c) ∧ PolynomiallyBounded (B.readerLimbBudget q c) := by
  have he := clog_add (clog_pow (clog (PolynomiallyBounded.const 2)) PolynomiallyBounded.id)
    (clog (PolynomiallyBounded.const (Fintype.card B.EquationIndex)))
  have ht := B.compressorLabelCount_polynomial c
  have hd := B.compressorDegree_polynomial.clog
  have hb := B.compressorHeaderWidth_polynomial q c
  have h := readerFieldWidths_polynomial ht hd hb
  exact ⟨readerWordWidth_polynomial he ht hd hb,h.2,h.1⟩

theorem compressorReaderCovers (q c : ℕ) {n : ℕ} (hn : 2 ≤ n) (p : Nat.Primes)
    (M : Model p (B.compressorDegree n) (B.compressorEquations hn c))
    (hp : q ≠ 0 → p.val = q) (hz : q=0 → p.val ≤ 2^B.compressorPrimeBits c n) :
    (B.compressorReaderPlan q c n).Covers (M.queryData (B.compressorCoeff hn c)) ∧
    SliceField.extensionDegree p.val (columnCountBound (B.compressorLabelCount c n) (B.compressorDegree n))
      ≤ B.readerDegreeBudget q c n ∧ SliceArithmetic.Word.workingWidth p.val ≤ B.readerLimbBudget q c n := by
  have hb := (B.prime_fits_compressorHeader p hp hz).le
  have h := readerFieldWidths (t := B.compressorLabelCount c n) (d := B.compressorDegree n) hb
  exact ⟨readerPlan_covers M (B.compressorCoeff hn c) hb,h.2,h.1⟩

/-- The bank, peak space and binary clock exponent supplied to the actual
Macaulay reader are polynomially bounded before selecting the circuit. -/
theorem compressorRawReaderBudgets (q c : ℕ) {w : ℕ → ℕ} (hw : PolynomiallyBounded w) :
    ∃ signedSpace signedExp : ℕ → ℕ, PolynomiallyBounded signedSpace ∧ PolynomiallyBounded signedExp ∧
      (PolynomiallyBounded fun n => (B.compressorReaderPlan q c n).live
        (B.readerDegreeBudget q c n) (B.readerLimbBudget q c n) (w n) (signedSpace n)) ∧
      (PolynomiallyBounded fun n => (B.compressorReaderPlan q c n).armSpace
        (B.readerDegreeBudget q c n) (B.readerLimbBudget q c n) (w n) (signedSpace n)) ∧
      (PolynomiallyBounded fun n => Nat.clog 2 ((B.compressorReaderPlan q c n).readTime
        (B.readerDegreeBudget q c n) (B.readerLimbBudget q c n) (w n) (signedSpace n) (signedExp n))) ∧
      ∀ n (hn : 2 ≤ n) (p e v : ℕ), e ≤ B.readerDegreeBudget q c n → v ≤ B.readerLimbBudget q c n →
        let L := JointScalar.Leaf.layout B.Entry B.EquationIndex B.equation c hn (w n) p e v
        let C := JointScalar.checker B.Entry B.EquationIndex B.equation c hn (w n)
        let b := JointScalar.Leaf.bankSize L (w n) (B.compressorLabelCount c n * w n)
        let work := JointScalar.Leaf.localCost L b
        max (UniversalCountStack.stackLimit C) b + work ≤ signedSpace n ∧
          2*(2^L.witnessBits * UniversalCountStack.perChoice C) + work ≤ 2^(signedExp n) := by
  obtain ⟨_,he,hv⟩ := B.compressorReaderWidths q c
  obtain ⟨sp,ex,hsp,hex,hcall⟩ := JointScalar.Leaf.budgets B.Entry B.EquationIndex B.equation c hw hw he hv
  have ht := B.compressorLabelCount_polynomial c
  have hd := B.compressorDegree_polynomial.clog
  have hb := B.compressorHeaderWidth_polynomial q c
  have hq := clog_pow ((PolynomiallyBounded.const 2).clog)
    (((PolynomiallyBounded.const 1).add (columnCountBound_clog ht hd)).add hb)
  obtain ⟨hl,hs,hx⟩ := ReaderPlan.leaf_resources (B.compressorReaderPlan q c) hw he hv hsp hex ht hd
    (pointCountBound_clog ht hd) hq
  exact ⟨sp,ex,hsp,hex,hl,hs,hx,fun n hn p e v hed hvw => hcall n hn p e v (w n) hed hvw le_rfl⟩

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
