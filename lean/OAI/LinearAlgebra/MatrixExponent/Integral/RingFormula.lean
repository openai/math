import OAI.LinearAlgebra.MatrixExponent.FieldFormula
import OAI.LinearAlgebra.MatrixExponent.Integral.UpperBound

/-! # The division-free exponent over nonzero commutative rings -/

namespace OAI.LinearAlgebra.MatrixExponent.Integral

theorem exponent_eq (A : Type*) [CommRing A] [Nontrivial A] {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    exponent A a b c = Rectangle.U a b c :=
  of_fields A ha hb hc (fun F _ => Rectangle.exponent_eq F ha hb hc)

theorem square_exponent (A : Type*) [CommRing A] [Nontrivial A] : exponent A 1 1 1 = 9 / 4 := by
  rw [exponent_eq A zero_le_one zero_le_one zero_le_one]
  norm_num [Rectangle.U, Rectangle.benchmark]

end OAI.LinearAlgebra.MatrixExponent.Integral
