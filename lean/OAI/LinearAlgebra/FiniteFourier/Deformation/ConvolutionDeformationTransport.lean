import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionDeformationBlock
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Transport of the integral deformation at the original endpoint

The map at one is the tensor product of the changes of generator on all
active axes. Its inverse gives the common input map for the two operands.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial TensorProduct PiTensorProduct

variable {A σ : Type*} [CommRing A]

/-- A family of algebra equivalences induces an algebra equivalence of its tensor products. -/
noncomputable def piTensorAlgCongr {S T : σ → Type*}
    [∀ i, CommRing (S i)] [∀ i, CommRing (T i)] [∀ i, Algebra A (S i)] [∀ i, Algebra A (T i)]
    (e : ∀ i, S i ≃ₐ[A] T i) : (⨂[A] i, S i) ≃ₐ[A] (⨂[A] i, T i) := by
  refine AlgEquiv.ofLinearEquiv (PiTensorProduct.congr fun i => (e i).toLinearEquiv) ?_ ?_
  · change PiTensorProduct.congr _ (tprod A 1) = tprod A 1
    simp [congr_tprod]
    rfl
  · intro x y
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      induction y using PiTensorProduct.induction_on with
      | smul_tprod s y =>
        simp only [smul_mul_assoc, mul_smul_comm, map_smul, tprod_mul_tprod, congr_tprod,
          Pi.mul_apply, AlgEquiv.toLinearEquiv_apply, map_mul]
        rfl
      | add y₁ y₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
    | add x₁ x₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]

@[simp] theorem piTensorAlgCongr_tprod {S T : σ → Type*} [∀ i, CommRing (S i)]
    [∀ i, CommRing (T i)] [∀ i, Algebra A (S i)] [∀ i, Algebra A (T i)]
    (e : ∀ i, S i ≃ₐ[A] T i) (x : ∀ i, S i) :
    piTensorAlgCongr e (tprod A x) = tprod A (fun i => e i (x i)) :=
  PiTensorProduct.congr_tprod ..

/-- Transport the active block by the indicated generator changes on each axis. -/
noncomputable def blockCongr {m : σ → ℕ} {c₁ c₂ b₁ b₂ : σ → A}
    (q : ∀ i, QuadraticAxis (c₁ i) ≃ₐ[A] QuadraticAxis (c₂ i))
    (b : ∀ i, BinomialAxis (m i) (b₁ i) ≃ₐ[A] BinomialAxis (m i) (b₂ i)) :
    Block m c₁ b₁ ≃ₐ[A] Block m c₂ b₂ :=
  piTensorAlgCongr fun i => Algebra.TensorProduct.congr (q i) (b i)

@[simp] theorem blockCongr_tprod_tmul {m : σ → ℕ} {c₁ c₂ b₁ b₂ : σ → A}
    (q : ∀ i, QuadraticAxis (c₁ i) ≃ₐ[A] QuadraticAxis (c₂ i))
    (b : ∀ i, BinomialAxis (m i) (b₁ i) ≃ₐ[A] BinomialAxis (m i) (b₂ i))
    (x : ∀ i, QuadraticAxis (c₁ i)) (y : ∀ i, BinomialAxis (m i) (b₁ i)) :
    blockCongr q b (tprod A fun i => x i ⊗ₜ[A] y i) =
      tprod A fun i => q i (x i) ⊗ₜ[A] b i (y i) := by
  simp [blockCongr]

/-- The simultaneous change of all generators at one. The image of each quadratic
generator is congruent to the original one modulo the jet parameter, and each
binomial generator is multiplied by a scalar unit congruent to one. -/
theorem exists_blockTransportAtOne (m : σ → ℕ) (z : A) (ρ : σ → A) (β : σ → Aˣ)
    (hz : IsNilpotent z) (hm : ∀ i, IsUnit (m i : A)) (hdisc : ∀ i, IsUnit (1-4*ρ i)) :
    ∃ (e : Block m (fun i => ρ i*(1+z)) (fun i => 1+((β i : A)-1)*(1+z)) ≃ₐ[A]
          Block m ρ (fun i => (β i : A)))
      (v : ∀ i, QuadraticAxis (ρ i)) (w : σ → Aˣ),
      (∀ i, algebraMap A _ z ∣ v i - AdjoinRoot.root (quadraticAxisPoly (ρ i))) ∧
      (∀ i, z ∣ (w i : A)-1) ∧
      ∀ j k : σ → ℕ, e (tprod A fun i =>
        ((AdjoinRoot.root (quadraticAxisPoly (ρ i*(1+z))))^(j i)) ⊗ₜ[A]
        ((AdjoinRoot.root ((X : A[X])^(m i) - C (1+((β i : A)-1)*(1+z))))^(k i))) =
      tprod A fun i => ((v i)^(j i)) ⊗ₜ[A]
        ((algebraMap A _ (w i : A) * AdjoinRoot.root ((X : A[X])^(m i) - C (β i : A)))^(k i)) := by
  choose q hq using fun i => exists_quadraticAxisChangeAtOne z (ρ i) hz (hdisc i)
  choose w hw b hb using fun i => binomialAxisAtOne z (β i) hz (m i) (hm i)
  refine ⟨blockCongr q b, _, w, hq, hw, fun j k => ?_⟩
  simp only [blockCongr_tprod_tmul, map_pow, hb]

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
