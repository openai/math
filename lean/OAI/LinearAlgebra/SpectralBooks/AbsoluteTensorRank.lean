import OAI.LinearAlgebra.SpectralBooks.AlgebraicExtensionRank
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PrimeField
import Mathlib.Algebra.Algebra.ZMod

/-! # Asymptotic rank over all fields of a characteristic

The polynomial equations expressing a decomposition over any field extension
have a solution over the algebraic closure. Combining this specialization
with finite-extension descent gives scalar invariance without an algebraicity
hypothesis, hence characteristic invariance for matrix multiplication tensors.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation

section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable (K : Type*) [Field K] [Algebra F K] [IsAlgClosed K]

/-- Specialize a finite tuple to an algebraically closed field while preserving
all polynomial equalities over its ground field. -/
theorem exists_specialization {V : Type*} [Finite V] (a : V → E) :
    ∃ b : V → K, ∀ p : MvPolynomial V F, MvPolynomial.aeval a p = 0 →
      MvPolynomial.aeval b p = 0 := by
  let I := MvPolynomial.vanishingIdeal F {a}
  obtain ⟨J, hJ, hIJ⟩ := Ideal.exists_le_maximal I (Ideal.IsPrime.ne_top (inferInstance : I.IsPrime))
  obtain ⟨b, hb⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hJ
  refine ⟨b, fun p hp ↦ (MvPolynomial.mem_vanishingIdeal_singleton_iff b p).mp ?_⟩
  rw [← hb]
  exact hIJ ((MvPolynomial.mem_vanishingIdeal_singleton_iff a p).mpr hp)

/-- A finite tensor defined over `F` admitting an exact rank decomposition over
`E` admits one of the same size over an algebraically closed `K` extending `F`. -/
theorem rankAtMost_of_extension_to_algClosed {X Y Z : Type*}
    [Finite X] [Finite Y] [Finite Z] {T : Tensor F X Y Z} {r : ℕ}
    (h : Tensor.RankAtMost (fun x y z ↦ algebraMap F E (T x y z)) r) :
    Tensor.RankAtMost (fun x y z ↦ algebraMap F K (T x y z)) r := by
  classical
  obtain ⟨A, B, C, habc⟩ := h
  let v : Fin r × (X ⊕ Y ⊕ Z) → E := fun p ↦ p.2.elim (A p.1) (Sum.elim (B p.1) (C p.1))
  obtain ⟨w, hw⟩ := exists_specialization (F := F) K v
  refine ⟨fun i x ↦ w (i, .inl x), fun i y ↦ w (i, .inr (.inl y)),
    fun i z ↦ w (i, .inr (.inr z)), ?_⟩
  funext x y z
  let p : MvPolynomial (Fin r × (X ⊕ Y ⊕ Z)) F := MvPolynomial.C (T x y z) - ∑ i,
    MvPolynomial.X (i, .inl x) * MvPolynomial.X (i, .inr (.inl y)) * MvPolynomial.X (i, .inr (.inr z))
  have hp : MvPolynomial.aeval v p = 0 := by
    simpa [p, v, Tensor.rankOne, sub_eq_zero] using congrFun (congrFun (congrFun habc x) y) z
  simpa [p, Tensor.rankOne, sub_eq_zero] using hw p hp

/-- A scalar extension of any transcendence degree preserves the asymptotic
rank of every finite three-tensor. -/
theorem asymptoticRank_map_eq {X Y Z : Type*} [Fintype X] [Fintype Y] [Finite Z]
    (T : Tensor F X Y Z) :
    asymptoticRank (fun x y z ↦ algebraMap F E (T x y z)) = asymptoticRank T := by
  apply le_antisymm (asymptoticRank_map_le T)
  rw [← asymptoticRank_map_eq_of_isAlgebraic (K := AlgebraicClosure F) T]
  apply le_ciInf
  intro n
  let U := fun x y z ↦ algebraMap F E (T x y z)
  let V := fun x y z ↦ algebraMap F (AlgebraicClosure F) (T x y z)
  have h : Tensor.RankAtMost (fun x y z ↦ algebraMap F E (Tensor.power T (n + 1) x y z))
      (tensorRank (Tensor.power U (n + 1))) := by
    rw [← power_scalarExtension (K := E)]
    exact rankAtMost_tensorRank _
  have hV := rankAtMost_of_extension_to_algClosed (AlgebraicClosure F) h
  have hle : tensorRank (Tensor.power V (n + 1)) ≤ tensorRank (Tensor.power U (n + 1)) := by
    apply tensorRank_le_of_rankAtMost
    rw [← power_scalarExtension (K := AlgebraicClosure F)] at hV
    exact hV
  apply (ciInf_le (f := fun k : ℕ ↦ (tensorRank (Tensor.power V (k+1)) : ℝ) ^ ((k+1:ℝ)⁻¹))
    ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩ n).trans
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hle) (by positivity)

/-- All fields extending `F` give the same asymptotic rank to the matrix tensor. -/
theorem asymptoticRank_matrixTensor_baseChange (F E : Type*) [Field F] [Field E] [Algebra F E]
    (a b c : ℕ) : asymptoticRank (matrixTensor E a b c) = asymptoticRank (matrixTensor F a b c) := by
  convert asymptoticRank_map_eq (E := E) (matrixTensor F a b c) using 2
  funext x y z
  simp only [matrixTensor, Tensor.matrixCoefficients]
  split <;> simp

/-- The rectangular matrix tensor's asymptotic rank depends only on the
characteristic, including characteristic zero. -/
theorem asymptoticRank_matrixTensor_eq_of_ringChar_eq (F E : Type*) [Field F] [Field E]
    (hchar : ringChar F = ringChar E) (a b c : ℕ) :
    asymptoticRank (matrixTensor F a b c) = asymptoticRank (matrixTensor E a b c) := by
  by_cases hzero : ringChar F = 0
  · let : CharZero F := (CharP.ringChar_zero_iff_CharZero F).mp hzero
    let : CharZero E := (CharP.ringChar_zero_iff_CharZero E).mp (hchar.symm.trans hzero)
    exact (asymptoticRank_matrixTensor_baseChange ℚ F a b c).trans
      (asymptoticRank_matrixTensor_baseChange ℚ E a b c).symm
  · let : Fact (ringChar F).Prime := ⟨(CharP.char_is_prime_or_zero F (ringChar F)).resolve_right hzero⟩
    let : CharP E (ringChar F) := ringChar.eq_iff.mp hchar.symm
    let : Algebra (ZMod (ringChar F)) E := ZMod.algebra _ _
    let : Algebra (ZMod (ringChar F)) F := ZMod.algebra _ _
    exact (asymptoticRank_matrixTensor_baseChange (ZMod (ringChar F)) F a b c).trans
      (asymptoticRank_matrixTensor_baseChange (ZMod (ringChar F)) E a b c).symm

/-- The characteristic-wise comparison in the notation `CharP F p`, with `p = 0`
allowed. -/
theorem matrix_asymptoticRank_eq_of_charP (F G : Type*) [Field F] [Field G]
    (p : ℕ) [CharP F p] [CharP G p] (x y z : ℕ) :
    asymptoticRank (matrixTensor F x y z) = asymptoticRank (matrixTensor G x y z) :=
  asymptoticRank_matrixTensor_eq_of_ringChar_eq F G
    ((ringChar.eq_iff.mpr (inferInstance : CharP F p)).trans
      (ringChar.eq_iff.mpr (inferInstance : CharP G p)).symm) x y z

end

end SpectralBooks
end LinearAlgebra
end OAI
