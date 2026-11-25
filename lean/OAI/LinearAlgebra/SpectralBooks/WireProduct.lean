import OAI.LinearAlgebra.SpectralBooks.Tensor

/-! # Matrix multiplication as a product of wires

Each shared wire is an identity matrix at its two endpoints and has a
one-dimensional slot at the remaining site. After grouping the two nontrivial
legs at each site in cyclic order, the three wires give the coefficient tensor
of rectangular matrix multiplication.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation

section

/-- The identity wire between sites one and two. -/
def wire12 (F : Type*) [Zero F] [One F] (n : ℕ) : Tensor F (Fin n) (Fin n) Unit :=
  fun i j _ ↦ if i = j then 1 else 0

/-- The identity wire between sites two and three. -/
def wire23 (F : Type*) [Zero F] [One F] (n : ℕ) : Tensor F Unit (Fin n) (Fin n) :=
  fun _ i j ↦ if i = j then 1 else 0

/-- The identity wire between sites three and one. -/
def wire31 (F : Type*) [Zero F] [One F] (n : ℕ) : Tensor F (Fin n) Unit (Fin n) :=
  fun i _ j ↦ if j = i then 1 else 0

/-- Group the two incident wire legs at the first site. -/
def wireSite1Equiv (n12 n31 : ℕ) :
    Fin n31 × Fin n12 ≃ (Fin n12 × Unit) × Fin n31 where
  toFun x := ((x.2, ()), x.1)
  invFun x := (x.2, x.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Group the two incident wire legs at the second site. -/
def wireSite2Equiv (n12 n23 : ℕ) :
    Fin n12 × Fin n23 ≃ (Fin n12 × Fin n23) × Unit where
  toFun x := (x, ())
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := rfl

/-- Group the two incident wire legs at the third site. -/
def wireSite3Equiv (n23 n31 : ℕ) :
    Fin n23 × Fin n31 ≃ (Unit × Fin n23) × Fin n31 where
  toFun x := (((), x.1), x.2)
  invFun x := (x.1.2, x.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Matrix multiplication is the product of its three two-site diagonals,
up to local bijections of the coordinate bases. -/
theorem matrixTensor_eq_wireProduct (F : Type*) [Field F] (n12 n23 n31 : ℕ) :
    matrixTensor F n12 n23 n31 =
      Tensor.pullback (wireSite1Equiv n12 n31) (wireSite2Equiv n12 n23) (wireSite3Equiv n23 n31)
        (Tensor.product (Tensor.product (wire12 F n12) (wire23 F n23)) (wire31 F n31)) := by
  funext x y z
  simp only [matrixTensor, Tensor.matrixCoefficients, Tensor.pullback, Tensor.product,
    wire12, wire23, wire31, wireSite1Equiv, wireSite2Equiv, wireSite3Equiv,
    Equiv.coe_fn_mk]
  by_cases h12 : x.2 = y.1 <;> by_cases h23 : y.2 = z.1 <;>
    by_cases h31 : z.2 = x.1 <;> simp [h12, h23, h31]

end

end SpectralBooks
end LinearAlgebra
end OAI
