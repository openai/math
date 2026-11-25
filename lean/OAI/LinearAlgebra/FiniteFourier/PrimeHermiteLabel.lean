import OAI.LinearAlgebra.FiniteFourier.PrimeHermiteTable

/-! # Independent spectral coordinates for each rectangle label -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K L α β ν : Type*} [CommSemiring K]

/-- Apply a linear operator to each label's own coordinates. -/
def primeLabelMap (Q : L → (α → K) →ₗ[K] (β → K)) :
    (L × α → K) →ₗ[K] (L × β → K) where
  toFun x o := Q o.1 (fun a => x (o.1, a)) o.2
  map_add' x y := funext fun ⟨l, b⟩ =>
    congrFun ((Q l).map_add (fun a => x (l, a)) (fun a => y (l, a))) b
  map_smul' c x := funext fun ⟨l, b⟩ =>
    congrFun ((Q l).map_smul c (fun a => x (l, a))) b

/-- Apply the same spectral change of coordinates at every label. -/
def primeLabelSpectralEquiv (L : Type*) (S : (α → K) ≃ₗ[K] (ν → K)) :
    (L × α → K) ≃ₗ[K] (L × ν → K) where
  __ := primeLabelMap (fun _ : L => S.toLinearMap)
  invFun y p := S.symm (fun v => y (p.1, v)) p.2
  left_inv x := funext fun ⟨l, a⟩ => congrFun (S.symm_apply_apply (fun i => x (l, i))) a
  right_inv y := funext fun ⟨l, v⟩ => congrFun (S.apply_symm_apply (fun i => y (l, i))) v

theorem realizesOp_primeLabelSpectralEquiv [Fintype α] (L : Type*) [Fintype L]
    (S : (α → K) ≃ₗ[K] (ν → K)) {c : ℕ} (h : RealizesOp S c) :
    RealizesOp (primeLabelSpectralEquiv L S) (Fintype.card L * c) :=
  h.rows L

theorem realizesOp_primeLabelSpectralEquiv_symm [Fintype ν] (L : Type*) [Fintype L]
    (S : (α → K) ≃ₗ[K] (ν → K)) {c : ℕ} (h : RealizesOp S.symm c) :
    RealizesOp (primeLabelSpectralEquiv L S).symm (Fintype.card L * c) :=
  h.rows L

/-- At a labeled frequency, the induced query has exactly its original
eigenvalue for that label. -/
theorem primeLabelMap_spectral (S : (α → K) ≃ₗ[K] (ν → K))
    (Q : L → Module.End K (α → K)) (z : L → ν → K)
    (hQ : ∀ l x v, S (Q l x) v = z l v * S x v) (x : L × α → K) (v : L × ν) :
    primeLabelSpectralEquiv L S (primeLabelMap Q x) v =
      z v.1 v.2 * primeLabelSpectralEquiv L S x v :=
  hQ v.1 (fun a => x (v.1, a)) v.2

/-- Inverting a labeled multiplier recovers the action of the ordinary matrix
on each label. This is the output read by the independent repair batches. -/
theorem primeLabelSpectralEquiv_symm_mul [Fintype α] (S : (α → K) ≃ₗ[K] (ν → K))
    (M : L → Matrix α α K) (z : L × ν → K)
    (hM : ∀ l x v, S ((M l).mulVec x) v = z (l, v) * S x v) (x : L × α → K) :
    (primeLabelSpectralEquiv L S).symm (z * primeLabelSpectralEquiv L S x) =
      fun p => (M p.1).mulVec (fun a => x (p.1, a)) p.2 := by
  apply (primeLabelSpectralEquiv L S).injective
  rw [LinearEquiv.apply_symm_apply]
  exact funext fun ⟨l, v⟩ => (hM l (fun a => x (l, a)) v).symm

end FiniteFourier
end LinearAlgebra
end OAI
