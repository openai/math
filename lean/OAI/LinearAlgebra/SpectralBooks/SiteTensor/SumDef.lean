import OAI.LinearAlgebra.SpectralBooks.Crossing

/-! # Direct sums in coordinates

The direct sum of tensors extends their coefficient functions by zero along the
two summand inclusions at every site and adds the resulting coefficients.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

noncomputable section

variable {X Y Z K : Type*} [Fintype X]

/-- Push coefficients forward by summing on fibers. -/
def pushCoeff [AddCommMonoid K] (f : X → Y) (T : X → K) (y : Y) : K :=
  ∑ x, if f x = y then T x else 0

/-- Successive pushes sum over the fibers of the composite. -/
theorem pushCoeff_comp [AddCommMonoid K] [Fintype Y]
    (g : Y → Z) (f : X → Y) (T : X → K) :
    pushCoeff g (pushCoeff f T) = pushCoeff (g ∘ f) T := by
  funext z
  unfold pushCoeff
  have hs (y : Y) : (if g y = z then ∑ x, if f x = y then T x else 0 else 0) =
      ∑ x, if g y = z then if f x = y then T x else 0 else 0 := by
    by_cases h : g y = z <;> simp [h]
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (f x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

/-- Fiberwise summation preserves addition. -/
theorem pushCoeff_add [AddCommMonoid K] (f : X → Y) (T U : X → K) :
    pushCoeff f (T + U) = pushCoeff f T + pushCoeff f U := by
  funext y
  simp only [pushCoeff, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split <;> simp

/-- A bijection transports each coefficient to its new index. -/
theorem pushCoeff_equiv [AddCommMonoid K] (e : X ≃ Y) (T : X → K) (y : Y) :
    pushCoeff e T y = T (e.symm y) := by
  simp [pushCoeff, ← e.eq_symm_apply]

/-- Contracting a pushed tensor pulls the test coefficients back. -/
theorem sum_pushCoeff_mul [Semiring K] [Fintype Y] (f : X → Y) (T : X → K) (g : Y → K) :
    ∑ y, pushCoeff f T y * g y = ∑ x, T x * g (f x) := by
  simp only [pushCoeff, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

variable {I : Type*} [Fintype I] {A B : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [AddCommMonoid K]

/-- Block direct sum, with a copy of the summand label at every site. -/
def sumCoeff (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) (y : ∀ i, A i ⊕ B i) : K :=
  pushCoeff (fun x i => Sum.inl (x i)) T y + pushCoeff (fun x i => Sum.inr (x i)) U y

/-- The all-left block carries the first tensor. -/
theorem sumCoeff_inl [Nonempty I] (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (x : ∀ i, A i) : sumCoeff T U (fun i => Sum.inl (x i)) = T x := by
  have hl (y : ∀ i, A i) : (fun i => (Sum.inl (y i) : A i ⊕ B i)) =
      (fun i => Sum.inl (x i)) ↔ y = x := by
    simp [funext_iff]
  have hr (y : ∀ i, B i) : (fun i => (Sum.inr (y i) : A i ⊕ B i)) ≠
      (fun i => Sum.inl (x i)) := by
    intro h
    cases congrFun h (Classical.arbitrary I)
  simp [sumCoeff, pushCoeff, hl, hr]

/-- The all-right block carries the second tensor. -/
theorem sumCoeff_inr [Nonempty I] (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (x : ∀ i, B i) : sumCoeff T U (fun i => Sum.inr (x i)) = U x := by
  have hr (y : ∀ i, B i) : (fun i => (Sum.inr (y i) : A i ⊕ B i)) =
      (fun i => Sum.inr (x i)) ↔ y = x := by
    simp [funext_iff]
  have hl (y : ∀ i, A i) : (fun i => (Sum.inl (y i) : A i ⊕ B i)) ≠
      (fun i => Sum.inr (x i)) := by
    intro h
    cases congrFun h (Classical.arbitrary I)
  simp [sumCoeff, pushCoeff, hl, hr]

/-- Every mixed block has zero coefficient. -/
theorem sumCoeff_mixed (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (y : ∀ i, A i ⊕ B i)
    (hl : ∀ x : ∀ i, A i, (fun i => Sum.inl (x i)) ≠ y)
    (hr : ∀ x : ∀ i, B i, (fun i => Sum.inr (x i)) ≠ y) :
    sumCoeff T U y = 0 := by
  simp [sumCoeff, pushCoeff, hl, hr]

end

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
