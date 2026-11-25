import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Star.BigOperators

/-! Zero padding for the synchronized product of cyclic-axis transforms.
The occupied coordinates on axis `i` are the left summand of `A i ⊕ B i`.
On its complement each local transform is the identity, as in the
exact-restoration construction in the integer multiplication algorithm. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedPadding

open Finset Matrix

variable {ι R : Type*} {A : ι → Type*} (B : ι → Type*)

/-- Embed the occupied product box into the product of padded axes. -/
def occupied (x : ∀ i, A i) (i : ι) : A i ⊕ B i := .inl (x i)

theorem occupied_injective : Function.Injective (occupied (A := A) B) :=
  fun _ _ h ↦ funext fun i ↦ Sum.inl.inj (congrFun h i)

/-- Store an array at the occupied addresses and write zero at the other addresses. -/
noncomputable def zeroExtend [Zero R] (f : (∀ i, A i) → R) : (∀ i, A i ⊕ B i) → R :=
  Function.extend (occupied B) f (fun _ ↦ 0)

@[simp] theorem zeroExtend_occupied [Zero R] (f : (∀ i, A i) → R) (x : ∀ i, A i) :
    zeroExtend B f (occupied B x) = f x :=
  (occupied_injective B).extend_apply ..

theorem zeroExtend_off [Zero R] (f : (∀ i, A i) → R) {y : ∀ i, A i ⊕ B i}
    (hy : y ∉ Set.range (occupied B)) : zeroExtend B f y = 0 :=
  Function.extend_apply' _ _ _ hy

/-- The local operation on its occupied axis and its restored complement. -/
def axisPadding {a b : Type*} [DecidableEq b] [Zero R] [One R]
    (U : Matrix a a R) : Matrix (a ⊕ b) (a ⊕ b) R :=
  fromBlocks U 0 0 1

/-- Matrix on the product of axes given by independent local matrices. -/
def tensorMatrix [Fintype ι] [CommMonoid R] (U : ∀ i, Matrix (A i) (A i) R) :
    Matrix (∀ i, A i) (∀ i, A i) R :=
  Matrix.of fun x y ↦ ∏ i, U i (x i) (y i)

theorem tensorMatrix_conjTranspose [Fintype ι] [CommMonoid R] [StarMul R]
    (U : ∀ i, Matrix (A i) (A i) R) :
    (tensorMatrix U)ᴴ = tensorMatrix (fun i ↦ (U i)ᴴ) := by
  ext x y
  simp [tensorMatrix, conjTranspose_apply, star_prod]

/-- The spectral product of two zero-padded arrays is zero-padded. -/
theorem zeroExtend_mul [MulZeroClass R] (f g : (∀ i, A i) → R) :
    zeroExtend B f * zeroExtend B g = zeroExtend B (f * g) := by
  classical
  funext y
  by_cases h : y ∈ Set.range (occupied B)
  · obtain ⟨x, rfl⟩ := h
    simp
  · simp [zeroExtend_off B _ h]

private theorem exists_unused {y : ∀ i, A i ⊕ B i} (hy : y ∉ Set.range (occupied B)) :
    ∃ i, ∃ b, y i = Sum.inr b := by
  classical
  by_contra! h
  have hleft (i : ι) : ∃ a, y i = Sum.inl a := by
    cases he : y i with
    | inl a => exact ⟨a, rfl⟩
    | inr b => exact False.elim (h i b he)
  exact hy ⟨fun i ↦ (hleft i).choose, funext fun i ↦ (hleft i).choose_spec.symm⟩

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, DecidableEq (B i)] [CommSemiring R]

/-- The tensor of the actual padded matrices returns exactly the zero-extended
tensor transform. In particular every address with an unused digit is zero. -/
theorem tensorMatrix_axisPadding_mulVec (U : ∀ i, Matrix (A i) (A i) R)
    (f : (∀ i, A i) → R) :
    tensorMatrix (fun i ↦ axisPadding (b := B i) (U i)) *ᵥ zeroExtend B f =
      zeroExtend B (tensorMatrix U *ᵥ f) := by
  classical
  funext y
  let K := tensorMatrix (fun i ↦ axisPadding (b := B i) (U i))
  have reduce : (K *ᵥ zeroExtend B f) y = ∑ x, K y (occupied B x) * f x := by
    symm
    apply Fintype.sum_of_injective (occupied B) (occupied_injective B) _ _
    · intro i hi
      simp [zeroExtend_off B f hi]
    · simp
  change (K *ᵥ zeroExtend B f) y = _
  rw [reduce]
  by_cases hy : y ∈ Set.range (occupied B)
  · obtain ⟨z, rfl⟩ := hy
    rw [zeroExtend_occupied]
    rfl
  · rw [zeroExtend_off B _ hy]
    obtain ⟨i, b, hi⟩ := exists_unused B hy
    apply sum_eq_zero
    intro x _
    have zeroAt : K y (occupied B x) = 0 := by
      apply Finset.prod_eq_zero (mem_univ i)
      simp [hi, occupied, axisPadding]
    simp [zeroAt]

/-- Zero extension also commutes with the adjoint tensor used after pointwise
multiplication. Both adjoints here are matrix conjugate transposes. -/
theorem tensorMatrix_axisPadding_conjTranspose_mulVec [StarRing R]
    (U : ∀ i, Matrix (A i) (A i) R) (f : (∀ i, A i) → R) :
    (tensorMatrix (fun i ↦ axisPadding (b := B i) (U i)))ᴴ *ᵥ zeroExtend B f =
      zeroExtend B ((tensorMatrix U)ᴴ *ᵥ f) := by
  simp only [tensorMatrix_conjTranspose, axisPadding, fromBlocks_conjTranspose, conjTranspose_zero, conjTranspose_one]
  exact tensorMatrix_axisPadding_mulVec B (fun i ↦ (U i)ᴴ) f

/-- The three transforms and the spectral product performed on the full padded
tensor agree with the same computation restricted to the occupied box. -/
theorem paddedSpectralProduct [StarRing R] (U : ∀ i, Matrix (A i) (A i) R)
    (f g : (∀ i, A i) → R) :
    let P := tensorMatrix (fun i ↦ axisPadding (b := B i) (U i))
    let T := tensorMatrix U
    Pᴴ *ᵥ ((P *ᵥ zeroExtend B f) * (P *ᵥ zeroExtend B g)) =
      zeroExtend B (Tᴴ *ᵥ ((T *ᵥ f) * (T *ᵥ g))) := by
  dsimp only
  rw [tensorMatrix_axisPadding_mulVec, tensorMatrix_axisPadding_mulVec, zeroExtend_mul,
    tensorMatrix_axisPadding_conjTranspose_mulVec]

end SynchronizedPadding

end NearSquareRoot
end Computability
end OAI
