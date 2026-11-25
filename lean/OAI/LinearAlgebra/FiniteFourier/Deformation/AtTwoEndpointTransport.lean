import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionDeformationTransport

/-! # Sparse coordinate matrices at the original endpoint of the deformation -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial TensorProduct Module Matrix
open scoped BigOperators Kronecker

variable {A σ : Type*} [CommRing A]

private theorem quadraticTransportColumn {c d : A} (q : QuadraticAxis c ≃ₐ[A] QuadraticAxis d) :
    ∀ i : Fin 2, LinearMap.toMatrix (quadraticBasis c) (quadraticBasis d)
      q.toAlgHom.toLinearMap i 0 = (1 : Matrix (Fin 2) (Fin 2) A) i 0 := by
  intro i
  have he (x : A) : quadraticBasis x 0 = 1 := by simp [quadraticBasis_apply]
  rw [LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, he, map_one, ← he d,
    Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
  simp [eq_comm]

/-- A change between quadratic generators fixes the constant basis vector and
has a unit coefficient on the linear term. -/
theorem exists_quadraticTransportMatrix {c d : A} (q : QuadraticAxis c ≃ₐ[A] QuadraticAxis d) :
    ∃ x : A, ∃ y : Aˣ, LinearMap.toMatrix (quadraticBasis c) (quadraticBasis d)
      q.toAlgHom.toLinearMap = !![1,x;0,(y:A)] := by
  let M := LinearMap.toMatrix (quadraticBasis c) (quadraticBasis d) q.toAlgHom.toLinearMap
  let N := LinearMap.toMatrix (quadraticBasis d) (quadraticBasis c) q.symm.toAlgHom.toLinearMap
  have hNM : N * M = 1 := by
    rw [show N * M = _ from (LinearMap.toMatrix_comp _ _ _
      q.symm.toAlgHom.toLinearMap q.toAlgHom.toLinearMap).symm]
    have h : q.symm.toAlgHom.toLinearMap.comp q.toAlgHom.toLinearMap = LinearMap.id := by
      ext x
      exact q.symm_apply_apply x
    rw [h, LinearMap.toMatrix_id]
  have hN : N 1 0 = 0 := quadraticTransportColumn q.symm 1
  have hu : N 1 1 * M 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hN] using congrArg (fun B => B 1 1) hNM
  let u : Aˣ := Units.mkOfMulEqOne (M 1 1) (N 1 1) (by rw [mul_comm]; exact hu)
  refine ⟨M 0 1, u, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · exact quadraticTransportColumn q 0
  · rfl
  · exact quadraticTransportColumn q 1
  · rfl

private theorem binomialTransportMatrix [Nontrivial A] {a b : A} {m : ℕ} (hm : 0 < m)
    (e : BinomialAxis m a ≃ₐ[A] BinomialAxis m b) (w : Aˣ)
    (hw : e (AdjoinRoot.root _) = algebraMap A _ (w : A) * AdjoinRoot.root _) :
    LinearMap.toMatrix (binomialBasis hm a) (binomialBasis hm b) e.toAlgHom.toLinearMap =
      diagonal (fun j : Fin m => (w : A)^j.val) := by
  ext i j
  rw [LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply]
  change (binomialBasis hm b).repr (e (binomialBasis hm a j)) i = _
  rw [binomialBasis_apply, map_pow, hw, mul_pow, ← map_pow, ← binomialBasis_apply hm b j,
    ← Algebra.smul_def, map_smul, Basis.repr_self]
  by_cases h : i = j <;> simp_all [eq_comm]

variable [Fintype σ] [DecidableEq σ] [Nontrivial A]
variable {m : σ → ℕ} {c d a b : σ → A}

/-- In the full power basis, a coordinatewise algebra transport is the tensor
grid of the local changes in the two generators. -/
theorem blockCongr_toMatrix (hm : ∀ i, 0 < m i)
    (q : ∀ i, QuadraticAxis (c i) ≃ₐ[A] QuadraticAxis (d i))
    (e : ∀ i, BinomialAxis (m i) (a i) ≃ₐ[A] BinomialAxis (m i) (b i)) :
    LinearMap.toMatrix (blockBasis m hm c a) (blockBasis m hm d b)
      (blockCongr q e).toAlgHom.toLinearMap =
    gridTensor (fun i => LinearMap.toMatrix (quadraticBasis (c i)) (quadraticBasis (d i))
      (q i).toAlgHom.toLinearMap ⊗ₖ LinearMap.toMatrix (binomialBasis (hm i) (a i))
        (binomialBasis (hm i) (b i)) (e i).toAlgHom.toLinearMap) := by
  ext s t
  simp only [LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom,
    blockBasis, Basis.piTensorProduct_apply, Basis.tensorProduct_apply', blockCongr_tprod_tmul,
    Basis.piTensorProduct_repr_tprod_apply, gridTensor, kroneckerMap_apply]
  apply Finset.prod_congr rfl
  intro i _
  rw [Basis.tensorProduct_repr_tmul_apply _ _ _ _ (s i).1 (s i).2, smul_eq_mul]
  apply mul_comm

/-- The simultaneous rotation and scaling of the active generators. -/
noncomputable def transportGrid (m : σ → ℕ) (x : σ → A) (y w : σ → Aˣ) :
    Matrix (Address m) (Address m) A :=
  gridTensor fun i => !![1, x i; 0, (y i : A)] ⊗ₖ
    diagonal (fun j : Fin (m i) => (w i : A)^j.val)

theorem exists_transportGrid (hm : ∀ i, 0 < m i)
    (q : ∀ i, QuadraticAxis (c i) ≃ₐ[A] QuadraticAxis (d i))
    (e : ∀ i, BinomialAxis (m i) (a i) ≃ₐ[A] BinomialAxis (m i) (b i))
    (w : σ → Aˣ) (h : ∀ i, e i (AdjoinRoot.root _) =
        algebraMap A _ (w i : A) * AdjoinRoot.root _) :
    ∃ x y, LinearMap.toMatrix (blockBasis m hm c a) (blockBasis m hm d b)
      (blockCongr q e).toAlgHom.toLinearMap = transportGrid m x y w := by
  choose x y hq using fun i => exists_quadraticTransportMatrix (q i)
  refine ⟨x, y, ?_⟩
  rw [blockCongr_toMatrix]
  simp only [transportGrid, hq, binomialTransportMatrix _ _ _ (h _)]

omit [Nontrivial A] in
private theorem binomialTransport_symm_root {n : ℕ} {a b : A}
    (e : BinomialAxis n a ≃ₐ[A] BinomialAxis n b) (w : Aˣ)
    (h : e (AdjoinRoot.root _) = algebraMap A _ (w : A) * AdjoinRoot.root _) :
    e.symm (AdjoinRoot.root _) = algebraMap A _ (↑w⁻¹ : A) * AdjoinRoot.root _ := by
  apply e.injective
  rw [e.apply_symm_apply, map_mul, e.commutes, h, ← mul_assoc, ← map_mul]
  simp

omit [Fintype σ] [DecidableEq σ] [Nontrivial A] in
private theorem blockCongr_symm
    (q : ∀ i, QuadraticAxis (c i) ≃ₐ[A] QuadraticAxis (d i))
    (e : ∀ i, BinomialAxis (m i) (a i) ≃ₐ[A] BinomialAxis (m i) (b i)) :
    (blockCongr q e).symm = blockCongr (fun i => (q i).symm) (fun i => (e i).symm) := by
  rfl

/-- The same sparse grid description holds on inputs pulled back through the inverse transport. -/
theorem exists_transportGrid_symm (hm : ∀ i, 0 < m i)
    (q : ∀ i, QuadraticAxis (c i) ≃ₐ[A] QuadraticAxis (d i))
    (e : ∀ i, BinomialAxis (m i) (a i) ≃ₐ[A] BinomialAxis (m i) (b i))
    (w : σ → Aˣ) (h : ∀ i, e i (AdjoinRoot.root _) =
        algebraMap A _ (w i : A) * AdjoinRoot.root _) :
    ∃ x y, LinearMap.toMatrix (blockBasis m hm d b) (blockBasis m hm c a)
      (blockCongr q e).symm.toAlgHom.toLinearMap = transportGrid m x y (fun i => (w i)⁻¹) := by
  rw [blockCongr_symm]
  exact exists_transportGrid hm _ _ _ fun i => binomialTransport_symm_root (e i) (w i) (h i)

/-- At the near-one specialization the algebra isomorphism and its inverse both
act on power coordinates by sparse grids. The binomial scalings are reciprocal. -/
theorem exists_transportGridAtOne (m : σ → ℕ) (hm : ∀ i, 0 < m i)
    (z : A) (ρ : σ → A) (β : σ → Aˣ)
    (hz : IsNilpotent z) (hwidth : ∀ i, IsUnit (m i : A))
    (hdisc : ∀ i, IsUnit (1 - 4 * ρ i)) :
    let c := fun i => ρ i * (1 + z)
    let b := fun i => 1 + ((β i : A) - 1) * (1 + z)
    ∃ (e : Block m c b ≃ₐ[A] Block m ρ (fun i => (β i : A)))
      (w : σ → Aˣ) (x : σ → A) (y : σ → Aˣ) (x' : σ → A) (y' : σ → Aˣ),
      LinearMap.toMatrix (blockBasis m hm c b) (blockBasis m hm ρ (fun i => (β i : A)))
        e.toAlgHom.toLinearMap = transportGrid m x y w ∧
      LinearMap.toMatrix (blockBasis m hm ρ (fun i => (β i : A))) (blockBasis m hm c b)
        e.symm.toAlgHom.toLinearMap = transportGrid m x' y' (fun i => (w i)⁻¹) := by
  dsimp only
  choose q _ using fun i => exists_quadraticAxisChangeAtOne z (ρ i) hz (hdisc i)
  choose w _ e he using fun i => binomialAxisAtOne z (β i) hz (m i) (hwidth i)
  obtain ⟨x, y, hf⟩ := exists_transportGrid hm q e w he
  obtain ⟨x', y', hi⟩ := exists_transportGrid_symm hm q e w he
  exact ⟨blockCongr q e, w, x, y, x', y', hf, hi⟩

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
