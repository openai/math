import OAI.LinearAlgebra.SpectralBooks.DiagonalProduct
import OAI.LinearAlgebra.SpectralBooks.SpectralSpace

/-! # Endpoint matrices and their two wire bounds

A matrix on two occupied slots is obtained by applying its columns or its rows
to one end of an identity wire. All other tensor sites have trivial factors.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical BigOperators

namespace SiteTensor.Raw

variable {I K : Type*}

/-- A matrix placed at two named slots. The equality witnesses index exactly the
local factors present at a site. -/
def endpointMatrix (a b : I) (A B : Type) [Fintype A] [Fintype B] (M : A → B → K) :
    Raw.{0} I K :=
  ⟨fun i ↦ (i = a → A) × (i = b → B), fun _ ↦ Fintype.ofFinite _,
    fun x ↦ M ((x a).1 rfl) ((x b).2 rfl)⟩

variable [Fintype I] [Field K]

private theorem grouped_diagonal_coeff_basis (a b : I) (D : Type) [Fintype D] :
    ((diagonal (Fin 2) K D).group ![a,b]).coeff =
      Crossing.basisTensor (F := K)
        (fun (d : D) (i : I) (_ : {j : Fin 2 // ![a,b] j = i}) ↦ d) := by
  funext x
  apply Finset.sum_congr rfl
  intro d _
  let z (j : Fin 2) : D := x (![a,b] j) ⟨j, rfl⟩
  have he : (z = fun _ ↦ d) ↔ x = fun _ _ ↦ d := by
    constructor
    · intro h
      funext i ⟨j, hj⟩
      subst i
      exact congrFun h j
    · rintro rfl
      rfl
  by_cases h : z = fun _ ↦ d
  · exact (ite_eq_left h).trans (ite_eq_left (he.mp h)).symm
  · exact (ite_eq_right h).trans (ite_eq_right (h ∘ he.mpr)).symm

private theorem endpointMatrix_restricts_factor (a b : I) {A B D : Type}
    [Fintype A] [Fintype B] [Fintype D] (M : A → B → K) (L : A → D → K) (R : B → D → K)
    (hM : ∀ x y, M x y = ∑ d, L x d * R y d) :
    (endpointMatrix a b A B M).Restricts ((diagonal (Fin 2) K D).group ![a,b]) := by
  unfold Restricts
  rw [grouped_diagonal_coeff_basis]
  apply (Crossing.restriction_basisTensor_iff _ _).mpr
  refine ⟨fun i x y ↦
    (if h : i = a then L (x.1 h) (y ⟨0,h.symm⟩) else 1) *
    (if h : i = b then R (x.2 h) (y ⟨1,h.symm⟩) else 1), fun x ↦ ?_⟩
  change M ((x a).1 rfl) ((x b).2 rfl) = _
  rw [hM]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_eq_single a] <;> simp_all
  · rw [Finset.prod_eq_single b] <;> simp_all

/-- The identity wire on row labels restricts to the matrix. -/
theorem endpointMatrix_restricts_leftWire (a b : I) {A B : Type} [Fintype A] [Fintype B]
    (M : A → B → K) :
    (endpointMatrix a b A B M).Restricts ((diagonal (Fin 2) K A).group ![a,b]) := by
  apply endpointMatrix_restricts_factor a b M (fun x d ↦ if d = x then 1 else 0)
    (fun y d ↦ M d y)
  intro x y
  simp [ite_mul]

/-- The identity wire on column labels restricts to the matrix. -/
theorem endpointMatrix_restricts_rightWire (a b : I) {A B : Type} [Fintype A] [Fintype B]
    (M : A → B → K) :
    (endpointMatrix a b A B M).Restricts ((diagonal (Fin 2) K B).group ![a,b]) := by
  apply endpointMatrix_restricts_factor a b M (fun x d ↦ M x d)
    (fun y d ↦ if d = y then 1 else 0)
  intro x y
  simp [mul_ite]

private def endpointLegEquiv (a b i : I) (D : Type) :
    ({j : Fin 2 // ![a,b] j = i} → D) ≃ ((i = a → D) × (i = b → D)) where
  toFun x := (fun h ↦ x ⟨0,h.symm⟩, fun h ↦ x ⟨1,h.symm⟩)
  invFun x t := by
    obtain ⟨t,ht⟩ := t
    by_cases h : t = 0
    · exact x.1 ((h ▸ ht : ![a,b] (0 : Fin 2) = i).symm)
    · have h1 : t = 1 := by omega
      exact x.2 ((h1 ▸ ht : ![a,b] (1 : Fin 2) = i).symm)
  left_inv x := by
    funext ⟨t,ht⟩
    fin_cases t <;> rfl
  right_inv x := by rfl

/-- An identity endpoint matrix is the placed two-slot diagonal. -/
theorem ofRaw_endpointMatrix_diagonal (a b : I) (A : Type) [Fintype A] :
    ofRaw (endpointMatrix a b A A (fun x y ↦ if x = y then (1 : K) else 0)) =
      ofRaw ((diagonal (Fin 2) K A).group ![a,b]) := by
  symm
  apply ofRaw_eq_iff.mpr (reindex_equivalent (fun i ↦ endpointLegEquiv a b i A) ?_)
  intro x
  let z (j : Fin 2) : A := x (![a,b] j) ⟨j,rfl⟩
  change (diagonal (Fin 2) K A).coeff z = if z 0 = z 1 then 1 else 0
  rw [diagonal_coeff_at (1 : Fin 2)]
  simp [Fin.forall_fin_two]

end SiteTensor.Raw

end

end SpectralBooks
end LinearAlgebra
end OAI
