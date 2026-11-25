import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Raw
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # A two-site matrix tensor is equivalent to the wire of its rank -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open OAI.LinearAlgebra.SpectralBooks.SiteTensor

variable {K O I : Type*} [Field K] [Fintype O] [Fintype I]

/-- The rank factorization and its reverse, given by a projection to the image
and a section from it. Both use the same wire dimension. -/
theorem matrix_wire_factors (M : Matrix O I K) :
    ∃ (P : Matrix O (Fin M.rank) K) (Q : Matrix (Fin M.rank) I K)
      (P' : Matrix (Fin M.rank) O K) (Q' : Matrix I (Fin M.rank) K),
      M = P * Q ∧ (1 : Matrix (Fin M.rank) (Fin M.rank) K) = P' * M * Q' := by
  classical
  let f := M.mulVecLin
  let e : LinearMap.range f ≃ₗ[K] (Fin M.rank → K) :=
    (Module.finBasis K (LinearMap.range f)).equivFun
  let p := (LinearMap.range f).subtype.comp e.symm.toLinearMap
  let q := e.toLinearMap.comp f.rangeRestrict
  have hcomp : p.comp q = f := by ext v i; simp [p, q]
  obtain ⟨p', hp'⟩ := p.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr
    (Subtype.val_injective.comp e.symm.injective))
  obtain ⟨q', hq'⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr
    (e.surjective.comp (LinearMap.range_eq_top.mp f.range_rangeRestrict)))
  have hM : LinearMap.toMatrix' f = M := by
    change LinearMap.toMatrix' M.mulVecLin = M
    rw [← Matrix.toLin'_apply']
    exact LinearMap.toMatrix'.apply_symm_apply M
  refine ⟨LinearMap.toMatrix' p, LinearMap.toMatrix' q, LinearMap.toMatrix' p',
    LinearMap.toMatrix' q', ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hcomp, hM]
  · have h : (p'.comp f).comp q' = LinearMap.id := by
      rw [← hcomp]
      change ((p'.comp p).comp q).comp q' = LinearMap.id
      rw [hp', LinearMap.id_comp, hq']
    simpa only [LinearMap.toMatrix'_comp, hM, LinearMap.toMatrix'_id] using
      congrArg (fun g ↦ LinearMap.toMatrix' g) h.symm


/-- The coefficient matrix of a two-site tensor in its given local bases. -/
def twoSiteMatrix (T : Raw (Fin 2) K) : Matrix (T.Leg 0) (T.Leg 1) K :=
  fun o i ↦ T.coeff ((piFinTwoEquiv T.Leg).symm (o, i))

/-- A matrix factorization by left and right multipliers gives a tensor
restriction with those two local maps. -/
theorem twoSite_restricts_of_factor {X Y : Raw (Fin 2) K}
    (P : Matrix (X.Leg 0) (Y.Leg 0) K) (Q : Matrix (Y.Leg 1) (X.Leg 1) K)
    (h : twoSiteMatrix X = P * twoSiteMatrix Y * Q) : X.Restricts Y := by
  let L : ∀ i, X.Leg i → Y.Leg i → K :=
    Fin.cons P (Fin.cons (fun i j ↦ Q j i) (fun i ↦ i.elim0))
  refine ⟨L, fun x ↦ ?_⟩
  have hx : X.coeff x = twoSiteMatrix X (x 0) (x 1) :=
    congrArg X.coeff ((piFinTwoEquiv X.Leg).symm_apply_apply x).symm
  have hsum := Equiv.sum_comp (piFinTwoEquiv Y.Leg).symm
    (fun a ↦ Y.coeff a * ∏ i, L i (x i) (a i))
  rw [hx, h]
  trans ∑ p : Y.Leg 0 × Y.Leg 1, Y.coeff ((piFinTwoEquiv Y.Leg).symm p) *
    ∏ i, L i (x i) ((piFinTwoEquiv Y.Leg).symm p i)
  rotate_left
  · convert! hsum
  rw [Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Finset.sum_mul, Fin.prod_univ_two]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  change P _ i * twoSiteMatrix Y i j * Q j _ = twoSiteMatrix Y i j * (P _ i * Q j _)
  ring

/-- A two-site diagonal has the identity matrix as its coefficient matrix. -/
theorem twoSiteMatrix_diagonal (D : Type*) [Fintype D] [DecidableEq D] :
    twoSiteMatrix (Raw.diagonal (Fin 2) K D) = (1 : Matrix D D K) := by
  classical
  funext (i : D) (j : D)
  change (∑ d : D, @ite K ((piFinTwoEquiv (fun _ : Fin 2 ↦ D)).symm (i,j) = (fun _ ↦ d))
    (Classical.propDecidable _) 1 0) = (1 : Matrix D D K) i j
  have he (d : D) : (piFinTwoEquiv (fun _ : Fin 2 ↦ D)).symm (i,j) = (fun _ ↦ d) ↔
      i = d ∧ j = d := by rw [Equiv.symm_apply_eq, Prod.ext_iff]; rfl
  simp only [he, ite_and]
  simp [Matrix.one_apply, eq_comm]

/-- The tensor of two local spaces is mutually restricted with the wire of
its matrix rank. -/
theorem twoSite_equivalent_wire (T : Raw.{0} (Fin 2) K) :
    T.Equivalent (Raw.diagonal (Fin 2) K (Fin (twoSiteMatrix T).rank)) := by
  obtain ⟨P, Q, P', Q', hT, hI⟩ := matrix_wire_factors (twoSiteMatrix T)
  constructor
  · apply twoSite_restricts_of_factor P Q
    rw [twoSiteMatrix_diagonal]
    change twoSiteMatrix T = P * (1 : Matrix (Fin (twoSiteMatrix T).rank) (Fin (twoSiteMatrix T).rank) K) * Q
    simpa only [Matrix.mul_one] using hT
  · apply twoSite_restricts_of_factor P' Q'
    rw [twoSiteMatrix_diagonal]
    exact hI

end

end

end FiniteFourier
end LinearAlgebra
end OAI
