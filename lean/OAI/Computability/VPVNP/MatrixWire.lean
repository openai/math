import OAI.Computability.VPVNP.WireTensor

/-!
# Matrix restrictions of a wire

A wire carries the summation index of a matrix factorization between its two
endpoints. Taking the rows or the columns as the factorization index bounds
the wire dimension by either local dimension in the split-star construction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

variable {k J I K Z : Type*} [Fintype I] [Fintype K] [Fintype Z]

/-- Place the row and column indices of a matrix at the indicated parties. -/
noncomputable def matrixTensor (a b : J) (M : Matrix I K k) : Tensor k J where
  Basis j := (j = a → I) × (j = b → K)
  finiteBasis _ := by classical exact inferInstance
  coeff x := M ((x a).1 rfl) ((x b).2 rfl)

theorem matrixTensor_one [DecidableEq I] [Zero k] [One k] (a b : J) :
    matrixTensor a b (1 : Matrix I I k) = wire a b I := by
  unfold matrixTensor wire
  congr 1
  funext x
  simp [Matrix.one_apply]

private def wireEndpoints (a b : J) (Z : Type*) :
    (Z × Z) ≃ ((j : J) → (j = a → Z) × (j = b → Z)) where
  toFun p _ := (fun _ ↦ p.1, fun _ ↦ p.2)
  invFun x := ((x a).1 rfl, (x b).2 rfl)
  left_inv _ := rfl
  right_inv x := by
    funext j
    apply Prod.ext <;> funext h <;> subst j <;> rfl

variable [Fintype J] [CommSemiring k]

/-- An exact factorization with inner index `Z` is obtained by acting with
its two factors at the respective ends of a `Z`-dimensional wire. -/
theorem wire_restricts_matrixTensor_of_factorization (a b : J) (M : Matrix I K k)
    (A : Matrix I Z k) (B : Matrix Z K k) (h : ∀ i j, M i j = ∑ z, A i z * B z j) :
    Restricts (wire (k := k) a b Z) (matrixTensor a b M) := by
  classical
  let L (j : J) (x : (j = a → I) × (j = b → K)) (y : (j = a → Z) × (j = b → Z)) :=
    (if e : j = a then A (x.1 e) (y.1 e) else 1) *
    (if e : j = b then B (y.2 e) (x.2 e) else 1)
  refine ⟨L, ?_⟩
  funext x
  let f (y : ∀ j, (j = a → Z) × (j = b → Z)) :=
    (∏ j, L j (x j) (y j)) * (wire (k := k) a b Z).coeff y
  change (∑ y, f y) = M ((x a).1 rfl) ((x b).2 rfl)
  rw [← (wireEndpoints a b Z).sum_comp f, Fintype.sum_prod_type, h]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only [f, L, wireEndpoints, wire, Equiv.coe_fn_mk]
  simp only [Finset.prod_mul_distrib, Fintype.prod_dite_eq']
  simp [mul_ite]

/-- Use the row index as the wire index and put the whole matrix at the column endpoint. -/
theorem wire_restricts_matrixTensor_left (a b : J) (M : Matrix I K k) :
    Restricts (wire (k := k) a b I) (matrixTensor a b M) := by
  classical
  apply wire_restricts_matrixTensor_of_factorization a b M (1 : Matrix I I k) M
  intro i j
  simp [Matrix.one_apply, ite_mul]

/-- Use the column index as the wire index and put the whole matrix at the row endpoint. -/
theorem wire_restricts_matrixTensor_right (a b : J) (M : Matrix I K k) :
    Restricts (wire (k := k) a b K) (matrixTensor a b M) := by
  classical
  apply wire_restricts_matrixTensor_of_factorization a b M M (1 : Matrix K K k)
  intro i j
  simp [Matrix.one_apply, mul_ite]

end WireTensor

end VPVNP
end Computability
end OAI
