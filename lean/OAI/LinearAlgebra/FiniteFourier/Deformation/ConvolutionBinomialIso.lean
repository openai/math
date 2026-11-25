import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionJetRoots
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Binomial factors at the endpoints of the integral convolution deformation

A unit scaling identifies two binomial algebras when the ratio of their
parameters is its m-th power. At the split endpoint, evaluation in the
power basis has Vandermonde matrix.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial

variable {R : Type*} [CommRing R]

/-- The binomial algebra on a single active axis. -/
abbrev BinomialAxis (m : ℕ) (β : R) := AdjoinRoot ((X : R[X]) ^ m - C β)

theorem binomialAxis_root_pow (m : ℕ) (β : R) :
    AdjoinRoot.root ((X : R[X]) ^ m - C β) ^ m = algebraMap R (BinomialAxis m β) β := by
  apply sub_eq_zero.mp
  simpa only [eval₂_sub, eval₂_X_pow, eval₂_C, AdjoinRoot.algebraMap_eq] using
    AdjoinRoot.eval₂_root ((X : R[X]) ^ m - C β)

private noncomputable def binomialScaleHom (m : ℕ) {a b : R} (w : Rˣ)
    (hw : b * (w : R) ^ m = a) : BinomialAxis m a →ₐ[R] BinomialAxis m b :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId ..)
    (algebraMap R _ (w : R) * AdjoinRoot.root _) (by
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, Algebra.ofId_apply, AlgHom.coe_toRingHom,
        mul_pow, binomialAxis_root_pow, ← map_pow, ← map_mul, mul_comm ((w : R)^m), hw, sub_self])

private theorem binomialScaleHom_root (m : ℕ) {a b : R} (w : Rˣ)
    (hw : b * (w : R)^m = a) :
    binomialScaleHom m w hw (AdjoinRoot.root _) =
      algebraMap R _ (w : R) * AdjoinRoot.root _ :=
  AdjoinRoot.liftAlgHom_root ..

/-- The generator at the source is sent to the scaled generator at the target. -/
noncomputable def binomialScaleEquiv (m : ℕ) {a b : R} (w : Rˣ)
    (hw : b * (w : R)^m = a) : BinomialAxis m a ≃ₐ[R] BinomialAxis m b := by
  have hi : a * (↑w⁻¹ : R)^m = b := by
    rw [← hw, mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow, mul_one]
  refine .ofAlgHom (binomialScaleHom m w hw) (binomialScaleHom m w⁻¹ hi)
    (AdjoinRoot.algHom_ext ?_) (AdjoinRoot.algHom_ext ?_) <;>
    rw [AlgHom.comp_apply, binomialScaleHom_root, map_mul, AlgHom.commutes,
      binomialScaleHom_root, ← mul_assoc, ← map_mul, ← Units.val_mul] <;> simp

@[simp] theorem binomialScaleEquiv_root (m : ℕ) {a b : R} (w : Rˣ)
    (hw : b * (w : R)^m = a) :
    binomialScaleEquiv m w hw (AdjoinRoot.root _) =
      algebraMap R _ (w : R) * AdjoinRoot.root _ :=
  binomialScaleHom_root m w hw

/-- Evaluation at all the specified roots of a defining relation. -/
noncomputable def axisEvalHom (p : R[X]) {m : ℕ} (v : Fin m → R)
    (hv : ∀ i, p.eval (v i) = 0) : AdjoinRoot p →ₐ[R] (Fin m → R) :=
  AlgHom.pi fun i => AdjoinRoot.liftAlgHom p (AlgHom.id R R) (v i)
    (hv i)

@[simp] theorem axisEvalHom_root (p : R[X]) {m : ℕ} (v : Fin m → R)
    (hv : ∀ i, p.eval (v i) = 0) :
    axisEvalHom p v hv (AdjoinRoot.root p) = v := by
  funext i
  exact AdjoinRoot.liftAlgHom_root p (AlgHom.id R R) (v i) (hv i)

/-- Evaluation on a full set of roots is an algebra isomorphism whenever
their pairwise differences are units. In power coordinates it is the
Vandermonde transform. -/
noncomputable def axisEvalEquiv (p : R[X]) (hp : p.Monic) (m : ℕ)
    (hd : Nontrivial R → p.natDegree = m) (v : Fin m → R)
    (hv : ∀ i, p.eval (v i) = 0) (hsep : Pairwise fun i j => IsUnit (v i - v j)) :
    AdjoinRoot p ≃ₐ[R] (Fin m → R) := by
  classical
  refine AlgEquiv.ofBijective (axisEvalHom p v hv) ?_
  cases subsingleton_or_nontrivial R with
  | inl hs =>
    have := Algebra.subsingleton R (AdjoinRoot p)
    exact ⟨fun _ _ _ => Subsingleton.elim .., fun _ => ⟨0, Subsingleton.elim ..⟩⟩
  | inr hn =>
    let pb := AdjoinRoot.powerBasis' hp
    let b := pb.basis.reindex (finCongr (hd hn))
    have hb (i : Fin m) : b i = AdjoinRoot.root p ^ i.val := by
      rw [Module.Basis.reindex_apply, pb.basis_eq_pow]
      rfl
    have hdet : IsUnit (Matrix.vandermonde v).det := by
      rw [Matrix.det_vandermonde, IsUnit.prod_univ_iff]
      exact fun i => IsUnit.prod_iff.mpr fun j hj => hsep (Finset.mem_Ioi.mp hj).ne'
    let V := Matrix.vandermonde v
    let E := V.toLinearEquiv' (V.invertibleOfIsUnitDet hdet)
    apply (Function.Bijective.of_comp_iff _ b.equivFun.symm.bijective).mp
    have hcomp : (axisEvalHom p v hv) ∘ b.equivFun.symm = E := by
      funext x i
      change axisEvalHom p v hv (b.equivFun.symm x) i = (V.mulVec x) i
      rw [Module.Basis.equivFun_symm_apply, map_sum, Finset.sum_apply]
      simp only [hb, map_smul, map_pow, axisEvalHom_root, Pi.smul_apply, smul_eq_mul, Pi.pow_apply,
        Matrix.mulVec, dotProduct, V, Matrix.vandermonde_apply, mul_comm]
    exact hcomp ▸ E.bijective

@[simp] theorem axisEvalEquiv_root (p : R[X]) (hp : p.Monic) (m : ℕ)
    (hd : Nontrivial R → p.natDegree = m) (v : Fin m → R)
    (hv : ∀ i, p.eval (v i) = 0) (hsep : Pairwise fun i j => IsUnit (v i - v j)) :
    axisEvalEquiv p hp m hd v hv hsep (AdjoinRoot.root p) = v :=
  axisEvalHom_root p v hv

/-- The binomial factor at the split endpoint, evaluated at its m roots. -/
noncomputable def binomialSplitEquiv {m : ℕ} (hm : m ≠ 0) (a : R) (v : Fin m → R)
    (hv : ∀ i, v i ^ m = a) (hsep : Pairwise fun i j => IsUnit (v i - v j)) :
    BinomialAxis m a ≃ₐ[R] (Fin m → R) :=
  axisEvalEquiv _ (monic_X_pow_sub_C a hm) m (fun _ => natDegree_X_pow_sub_C)
    v (by simpa using fun i => sub_eq_zero.mpr (hv i)) hsep

@[simp] theorem binomialSplitEquiv_root {m : ℕ} (hm : m ≠ 0) (a : R) (v : Fin m → R)
    (hv : ∀ i, v i ^ m = a) (hsep : Pairwise fun i j => IsUnit (v i - v j)) :
    binomialSplitEquiv hm a v hv hsep (AdjoinRoot.root _) = v :=
  by simp [binomialSplitEquiv]

/-- At the original endpoint the binomial component is identified with its
undeformed algebra by a scaling congruent to one modulo the jet parameter. -/
theorem binomialAxisAtOne (z : R) (β : Rˣ) (hz : IsNilpotent z) (m : ℕ)
    (hm : IsUnit (m : R)) :
    ∃ w : Rˣ, z ∣ (w : R) - 1 ∧
      ∃ e : BinomialAxis m (1 + ((β : R) - 1) * (1 + z)) ≃ₐ[R] BinomialAxis m (β : R),
        e (AdjoinRoot.root _) = algebraMap R _ (w : R) * AdjoinRoot.root _ := by
  obtain ⟨w, hw, he⟩ := binomialScalingAtOne z β hz m hm
  exact ⟨w, hw, binomialScaleEquiv m w he, binomialScaleEquiv_root m w he⟩

/-- At the split endpoint the evaluation nodes are all powers of the
specified root of unity multiplied by the same lifted unit. -/
theorem binomialAxisAtZero (z β : R) (hz : IsNilpotent z) {m : ℕ} (hm : m ≠ 0)
    (hmR : IsUnit (m : R)) (u : R) (hu : u ^ m = 1)
    (hsep : Pairwise fun i j : Fin m => IsUnit (u ^ i.val - u ^ j.val)) :
    ∃ w : Rˣ, z ∣ (w : R) - 1 ∧
      ∃ e : BinomialAxis m (1 + (β - 1) * z) ≃ₐ[R] (Fin m → R),
        e (AdjoinRoot.root _) = fun i => (w : R) * u ^ i.val := by
  obtain ⟨w, hw, he⟩ := binomialScalingAtZero z β hz m hmR
  have he' : (1 : R) * (w : R) ^ m = 1 + (β - 1) * z := by simpa using he
  have hroot (i : Fin m) : (u ^ i.val) ^ m = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hu, one_pow]
  let e := binomialSplitEquiv hm 1 (fun i => u ^ i.val) hroot hsep
  refine ⟨w, hw, (binomialScaleEquiv m w he').trans e, ?_⟩
  rw [AlgEquiv.trans_apply, binomialScaleEquiv_root, map_mul, AlgEquiv.commutes,
    binomialSplitEquiv_root]
  rfl

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
