import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicDeformationProduct
import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionDeformationBlock

/-! # Correctness in the tensor product of binomial algebras

The monomial-coordinate product computed by the common deformation represents
multiplication in the original tensor product of the active axes.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation.Dyadic

open Polynomial Module TensorProduct
open scoped BigOperators

variable {A σ : Type*} [CommRing A]

/-- One binomial algebra on each active axis. -/
abbrev Block (m : σ → ℕ) (β : σ → A) := ⨂[A] i, BinomialAxis (m i) (β i)

/-- The tensor product of the binomial power bases. -/
noncomputable def blockBasis [Nontrivial A] [Fintype σ]
    (m : σ → ℕ) (hm : ∀ i, 0 < m i) (β : σ → A) :
    Basis (Address m) A (Block m β) :=
  Basis.piTensorProduct fun i => binomialBasis (hm i) (β i)

theorem axisBasis_repr_mul [Nontrivial A] {m : ℕ} (hm : 0 < m)
    (β : A) (a b k : Fin m) :
    let B := binomialBasis hm β
    B.repr (B a * B b) k = axisCoeff β a b k := by
  let B := binomialBasis hm β
  let g := algebraMap A (BinomialAxis m β)
  let y := AdjoinRoot.root ((X : A[X])^m - C β)
  have hs : B.equivFun.symm (axisCoeff β a b) = B a * B b := by
    rw [Basis.equivFun_symm_apply]
    simpa only [B, Algebra.smul_def, binomialBasis_apply, map_axisCoeff] using
      axisCoeff_normal_form (g β) y (binomialAxis_root_pow m β) a b
  exact congrFun ((B.equivFun.symm_apply_eq).mp hs).symm k

theorem blockBasis_repr_mul [Nontrivial A] [Fintype σ]
    (m : σ → ℕ) (hm : ∀ i, 0 < m i) (β : σ → A) (a b k : Address m) :
    let B := blockBasis m hm β
    B.repr (B a * B b) k = coeff β m a b k := by
  simp only [blockBasis, Basis.piTensorProduct_apply, PiTensorProduct.tprod_mul_tprod,
    Basis.piTensorProduct_repr_tprod_apply, Pi.mul_apply, axisBasis_repr_mul, coeff]

/-- The wrapped product of coordinate arrays gives precisely multiplication in the active block. -/
theorem blockBasis_mul [Nontrivial A] [Fintype σ] [DecidableEq σ]
    (m : σ → ℕ) (hm : ∀ i, 0 < m i) (β : σ → A) (x y : Block m β) :
    let B := blockBasis m hm β
    B.equivFun (x*y) = multiply (coeff β m) (B.equivFun x) (B.equivFun y) := by
  intro B
  let T := Block m β
  let : IsScalarTower A T T := IsScalarTower.right (R := A) (A := T)
  let : SMulCommClass A T T := Algebra.to_smulCommClass (R := A) (A := T)
  funext k
  calc
    _ = B.equivFun ((∑ a, (B.repr x a) • B a) * (∑ b, (B.repr y b) • B b)) k := by
      rw [B.sum_repr, B.sum_repr]
    _ = _ := by
      change B.coord k _ = _
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum, map_sum, multiply]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [smul_mul_smul_comm, map_smul, smul_eq_mul, Basis.coord_apply]
      rw [show B.repr (B a * B b) k = _ from blockBasis_repr_mul m hm β a b k]
      rfl

/-- The common deformation algorithm computes the actual binomial block product in
the original coordinates. The short-jet power bases need nontrivial coefficients. -/
theorem split_block_product [Fintype σ] [DecidableEq σ] (r : ℕ) (hr : 0 < r)
    [Nontrivial (Jet A r)] (m : σ → ℕ) (hmpos : ∀ i, 0 < m i) (β : σ → Aˣ)
    (hm : ∀ i, IsUnit (m i : A)) (ζ : ∀ i, Fin (m i) → A)
    (hζ : ∀ i j, ζ i j ^ m i = 1) (hd : ∀ i, Pairwise fun j k => IsUnit (ζ i j - ζ i k)) :
    let H := 2*r + Fintype.card σ
    let B := blockBasis m hmpos (fun i => algebraMap A (Jet A r) (β i : A))
    ∃ (u : σ → (Jet A r)ˣ) (v : σ → (Jet A H)ˣ), ∀ x y,
      transformOutput m u v ζ (transformInput m u v ζ (B.equivFun x) *
        transformInput m u v ζ (B.equivFun y)) = B.equivFun (x * y) := by
  obtain ⟨u, v, huv⟩ := split_product r hr m β hm ζ hζ hd
  exact ⟨u, v, fun x y => (huv _ _).trans (blockBasis_mul m hmpos _ x y).symm⟩

end Deformation.Dyadic

end FiniteFourier
end LinearAlgebra
end OAI
