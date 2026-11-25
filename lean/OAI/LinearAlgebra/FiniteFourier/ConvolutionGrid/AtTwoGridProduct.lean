import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionDeformation

/-! # Tensoring the prime-axis changes of basis

The columns for a prime cyclic axis are the images of its monomials in a
product algebra. Their local multiplication tables determine the table for a
product of axes, with independent choices of summands on the axes.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace ConvolutionGrid

open Matrix
open scoped BigOperators Classical

variable {R σ : Type*} [CommSemiring R] [Fintype σ]
  {G K : σ → Type*} [∀ i, Fintype (G i)] [∀ i, Fintype (K i)]

/-- A possibly rectangular tensor of coordinate matrices. Selecting the rows in
one algebra summand gives such a matrix even when the full basis change is square. -/
def columns (A : ∀ i, Matrix (K i) (G i) R) : Matrix (∀ i, K i) (∀ i, G i) R :=
  fun k g => ∏ i, A i (k i) (g i)

/-- The product of the rectangular tensors of two compatible families is
the tensor of the products, including for different basis labels on both sides. -/
theorem columns_mul {I J K : σ → Type*} [∀ i, Fintype (J i)]
    (A : ∀ i, Matrix (I i) (J i) R) (B : ∀ i, Matrix (J i) (K i) R) :
    columns A * columns B = columns (fun i => A i * B i) := by
  ext s t
  simp only [columns, Matrix.mul_apply, Fintype.prod_sum, Finset.prod_mul_distrib]

theorem columns_identity {I : σ → Type*} [∀ i, DecidableEq (I i)] :
    columns (fun i => (1 : Matrix (I i) (I i) R)) = 1 := by
  ext s t
  by_cases he : s = t
  · subst t
    simp [columns]
  · obtain ⟨i,hi⟩ : ∃ i, s i ≠ t i := by
      contrapose! he
      exact funext he
    rw [Matrix.one_apply_ne he]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

/-- The structure constants in a product monomial basis. -/
def coeff (c : ∀ i, K i → K i → K i → R) (a b k : ∀ i, K i) : R :=
  ∏ i, c i (a i) (b i) (k i)

variable [∀ i, Add (G i)]

omit [∀ i, Fintype (G i)] in
/-- Tensoring monomial columns preserves the multiplication rule on a cyclic grid. -/
theorem columns_add (A : ∀ i, Matrix (K i) (G i) R) (c : ∀ i, K i → K i → K i → R)
    (h : ∀ i g t k, A i k (g+t) =
       Deformation.multiply (c i) (fun a => A i a g) (fun b => A i b t) k)
    (g t : ∀ i, G i) (k : ∀ i, K i) :
    columns A k (g+t) = Deformation.multiply (coeff c)
        (fun a => columns A a g) (fun b => columns A b t) k := by
  classical
  simp only [columns, Pi.add_apply, h, Deformation.multiply, coeff, Fintype.prod_sum,
    Finset.prod_mul_distrib]

/-- Cyclic convolution in the coefficient coordinates of a finite additive group. -/
def cyclicProduct {I : Type*} [Fintype I] [Add I] [DecidableEq I] (x y : I → R) (k : I) : R :=
  ∑ i, ∑ j, if i+j = k then x i*y j else 0

omit [Fintype σ] [∀ i, Fintype (G i)] [∀ i, Fintype (K i)] [∀ i, Add (G i)] in
/-- Extending multiplicative monomial columns linearly computes the product on all inputs. -/
theorem mulVec_cyclicProduct {I J : Type*} [Fintype I] [Fintype J] [Add I] [DecidableEq I]
    (A : Matrix J I R) (c : J → J → J → R)
    (h : ∀ g t k, A k (g+t) =
       Deformation.multiply c (fun a => A a g) (fun b => A b t) k)
    (x y : I → R) :
    A *ᵥ cyclicProduct x y = Deformation.multiply c (A *ᵥ x) (A *ᵥ y) := by
  funext k
  have lhs : (A *ᵥ cyclicProduct x y) k = ∑ g, ∑ t, A k (g+t) * (x g*y t) := by
    simp only [mulVec, dotProduct, cyclicProduct, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_comm]
    simp
  rw [lhs]
  simp only [h, Deformation.multiply, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    enter [2,g]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs =>
    enter [2,g]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun g _ => by ring

/-- The simultaneous prime-axis transform takes cyclic convolution into the
product algebra in any chosen combination of summands. -/
theorem columns_cyclicProduct (A : ∀ i, Matrix (K i) (G i) R)
    (c : ∀ i, K i → K i → K i → R)
    (h : ∀ i g t k, A i k (g+t) =
       Deformation.multiply (c i) (fun a => A i a g) (fun b => A i b t) k)
    (x y : (∀ i, G i) → R) :
    columns A *ᵥ cyclicProduct x y =
      Deformation.multiply (coeff c) (columns A *ᵥ x) (columns A *ᵥ y) :=
  mulVec_cyclicProduct (columns A) (coeff c) (columns_add A c h) x y

section Sectors

variable (S : Finset σ)

/-- Insert a scalar summand label on every inactive axis. -/
noncomputable def sectorIndex (k : ∀ i : S, K i.val) (i : σ) : Option (K i) :=
  if hi : i ∈ S then some (k ⟨i,hi⟩) else none

/-- The subset-indexed blocks exhaust all rows, including the all-scalar block. -/
noncomputable def sectorEquiv : (Σ S : Finset σ, ∀ i : S, K i.val) ≃ (∀ i, Option (K i)) :=
  Equiv.ofBijective (fun v => sectorIndex v.1 v.2) (by
    constructor
    · rintro ⟨s,k⟩ ⟨t,l⟩ he
      have hs : s = t := by
        ext i
        have h := congrArg Option.isSome (congrFun he i)
        change (sectorIndex s k i).isSome = (sectorIndex t l i).isSome at h
        by_cases hi : i ∈ s <;> by_cases hj : i ∈ t <;> simp_all [sectorIndex]
      subst t
      congr 1
      funext i
      have hi := congrFun he i
      exact Option.some.inj (by simpa [sectorIndex,i.property] using hi)
    · intro v
      let s := Finset.univ.filter (fun i => (v i).isSome)
      let k (i : s) : K i.val := (v i.val).get ((Finset.mem_filter.mp i.property).2)
      refine ⟨⟨s,k⟩, funext fun i => ?_⟩
      change sectorIndex s k i = v i
      cases h : v i <;> simp [sectorIndex,s,k,h])

omit [∀ i, Fintype (G i)] [∀ i, Fintype (K i)] [∀ i, Add (G i)] in
/-- Extracting a direct-product summand of a tensor factors its matrix into
the nontrivial axes and the scalar factors on the complementary axes. -/
theorem columns_sectorIndex (A : ∀ i, Matrix (Option (K i)) (G i) R)
    (k : ∀ i : S, K i.val) (g : ∀ i, G i) :
    columns A (sectorIndex S k) g =
      (∏ i : S, A i (some (k i)) (g i)) * (∏ i : ↥Sᶜ, A i none (g i)) := by
  unfold columns
  rw [← Finset.prod_mul_prod_compl S, ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort Sᶜ]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp [sectorIndex,i.property]
  · apply Finset.prod_congr rfl
    intro i _
    simp [sectorIndex,Finset.mem_compl.mp i.property]

/-- Multiplication in each chosen summand. Non-scalar structure constants
occur only on the active axes, so the number of factors in its deformation
degree is the size of this subset. -/
theorem sector_cyclicProduct [∀ i, DecidableEq (G i)] (A : ∀ i, Matrix (Option (K i)) (G i) R)
    (c : ∀ i, K i → K i → K i → R)
    (h₀ : ∀ i g t, A i none (g+t) = A i none g * A i none t)
    (h₁ : ∀ i g t k, A i (some k) (g+t) =
       Deformation.multiply (c i) (fun a => A i (some a) g) (fun b => A i (some b) t) k)
    (x y : (∀ i, G i) → R) :
    (columns A *ᵥ cyclicProduct x y) ∘ sectorIndex S =
      Deformation.multiply (coeff (fun i : S => c i.val))
        ((columns A *ᵥ x) ∘ sectorIndex S) ((columns A *ᵥ y) ∘ sectorIndex S) := by
  apply mulVec_cyclicProduct (fun k g => columns A (sectorIndex S k) g)
  intro g t k
  simp only [columns_sectorIndex, Pi.add_apply, h₀, h₁, Deformation.multiply,
    Fintype.prod_sum, Finset.prod_mul_distrib, coeff, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end Sectors
end ConvolutionGrid

end FiniteFourier
end LinearAlgebra
end OAI
