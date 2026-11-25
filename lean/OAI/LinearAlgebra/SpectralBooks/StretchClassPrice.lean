import OAI.LinearAlgebra.SpectralBooks.StretchSupportedPrice
import OAI.LinearAlgebra.SpectralBooks.ClassComparison
import OAI.LinearAlgebra.SpectralBooks.BookDiagonalRaw

/-! # Coordinate evaluation of a spectral price on nonzero tensor classes -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open MatrixMultiplication.Foundation
open scoped Classical BigOperators NNReal

section
open SiteTensor

namespace SiteTensor

universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]

/-- Extend a price from the nonzero tensor classes by zero. -/
def classPrice (g : NonzeroProduct.{v} I K →+ ℝ) (x : TensorClass.{v} I K) : ℝ :=
  if h : x = 0 then 0 else g (Additive.ofMul (⟨x, h⟩ : nonzeroClasses I K))

@[simp] theorem classPrice_eq (g : NonzeroProduct.{v} I K →+ ℝ) (x : NonzeroProduct.{v} I K) :
    classPrice g (classOfProduct x) = g x := by
  have h : classOfProduct x ≠ 0 := x.toMul.property
  simp only [classPrice, h, ↓reduceDIte]
  rfl

@[simp] theorem classPrice_zero (x : TensorClass.{v} I K) :
    classPrice 0 x = 0 := by
  simp [classPrice]

theorem classPrice_scaled_log (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → _))
    (c : ℝ) (x : TensorClass.{v} I K) :
    classPrice (c • logPoint φ) x = c * Real.logb 2 (φ.val x : ℝ) := by
  by_cases hx : x = 0
  · simp [classPrice, hx, φ.property.1]
  · simp only [classPrice, hx, ↓reduceDIte]
    rfl

end SiteTensor

namespace SitePriceEval

variable {K : Type*} [Field K] {B C O : Type} [Fintype B] [Fintype C] [Fintype O]
variable (g : NonzeroProduct.{0} (BookSite B C ⊕ O) K →+ ℝ)
variable (hg : IsSpectralPrice unit_le_nonzeroClass g)

/-- The supported coordinate evaluation for a spectral price on the nonzero
tensor classes, including the zero price of a collapsed placement. -/
def ofSupportedClassPrice : SitePriceEval K B C where
  value T := classPrice g (ofRaw (Raw.withTrivial O (bookRaw T)))
  mono := by
    intro U V X X' Y Y' _ _ _ _ _ _ T T' h
    rcases hg with rfl | ⟨φ, c, hc, rfl⟩
    · simp
    · simp only [classPrice_scaled_log]
      exact (ofSupportedSpectralPoint φ c hc.le).mono h

/-- This coordinate price agrees with the original additive price whenever
the given tensor represents the specified nonzero class. -/
theorem ofSupportedClassPrice_agrees {U : Type} {X : B → Type} {Y : C → Type}
    [Fintype U] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    (T : Tensor K U (∀ b, X b) (∀ c, Y c))
    (t : NonzeroProduct.{0} (BookSite B C ⊕ O) K)
    (ht : ofRaw (Raw.withTrivial O (bookRaw T)) = classOfProduct t) :
    (ofSupportedClassPrice g hg).value T = g t := by
  simp [ofSupportedClassPrice, ht]

theorem ofSupportedClassPrice_binaryProductAdditive :
    (ofSupportedClassPrice g hg).BinaryProductAdditive := by
  rcases hg with rfl | ⟨φ, c, hc, rfl⟩
  · intro U V X X' Y Y' _ _ _ _ _ _ T S hT hS
    simp [ofSupportedClassPrice]
  · intro U V X X' Y Y' _ _ _ _ _ _ T S hT hS
    simp only [ofSupportedClassPrice, classPrice_scaled_log]
    exact ofSupportedSpectralPoint_binaryProductAdditive φ c hc.le T S hT hS

theorem ofSupportedClassPrice_wordProductAdditive :
    (ofSupportedClassPrice g hg).WordProductAdditive :=
  wordProductAdditive_of_binaryProductAdditive _ (ofSupportedClassPrice_binaryProductAdditive g hg)

/-- The binary diagonal on the support gives the ordinary-sum coefficient for
every spectral price, including a collapsed price. -/
theorem ofSupportedClassPrice_ordinarySumBound :
    (ofSupportedClassPrice g hg).OrdinarySumBound
      (classPrice g (ofRaw (Raw.supportDiagonal (BookSite B C) O K (Fin 2)))) := by
  rcases hg with rfl | ⟨φ, c, hc, rfl⟩
  · intro L U X Y _ _ _ _ _ T
    exact ⟨Classical.arbitrary L, by simp [ofSupportedClassPrice]⟩
  · intro L U X Y _ _ _ _ _ T
    simp only [ofSupportedClassPrice, classPrice_scaled_log]
    exact ofSupportedSpectralPoint_ordinarySumBound φ c hc.le T

/-- The book's common diagonal represents the partial diagonal in the ambient class. -/
theorem ofSupportedClassPrice_diagAll (W : Type) [Fintype W] :
    (ofSupportedClassPrice g hg).value (PermutationStretch.diagAll B C W) =
      classPrice g (ofRaw (Raw.supportDiagonal (BookSite B C) O K W)) :=
  congrArg (classPrice g) (congrArg (withTrivialHom O) (ofRaw_bookRaw_diagAll (W := W)))

/-- The sharp ordinary-sum loss in coordinates is the price of the binary common diagonal. -/
theorem ofSupportedClassPrice_ordinarySumBound_diagAll :
    let p := ofSupportedClassPrice g hg
    p.OrdinarySumBound (p.value (PermutationStretch.diagAll B C (Fin 2))) := by
  dsimp only
  rw [ofSupportedClassPrice_diagAll]
  exact ofSupportedClassPrice_ordinarySumBound g hg

end SitePriceEval
end

end

end SpectralBooks
end LinearAlgebra
end OAI
