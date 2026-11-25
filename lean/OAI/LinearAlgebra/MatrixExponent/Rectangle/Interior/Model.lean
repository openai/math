import OAI.LinearAlgebra.MatrixExponent.Rectangle.Model

/-! # Bilinear formulas with a private product for each output -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior

/-- Coefficients of a decomposable bilinear form. -/
structure Product (F : Type*) (X Y : Type) where
  left : X → F
  right : Y → F

def Product.apply {F : Type*} [Mul F] {X Y : Type} (p : Product F X Y) (x : X) (y : Y) :=
  p.left x * p.right y

/-- Each output reads its own product and a linear combination of
common products. No other output reads the private product. -/
def Private {F : Type*} [Field F] {X Y Z : Type} (M : Z → X → Y → F) (r : ℕ) : Prop :=
  ∃ (a : Z → Product F X Y) (b : Fin r → Product F X Y) (c : Z → Fin r → F),
    ∀ z x y, M z x y = (a z).apply x y + ∑ l, c z l * (b l).apply x y

def PrivateProducts (F : Type*) [Field F] (i j k r : ℕ) : Prop :=
  Private (fun (z : Pos i j) (x : Pos i k) (y : Pos k j) =>
    if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then (1 : F) else 0) r

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
