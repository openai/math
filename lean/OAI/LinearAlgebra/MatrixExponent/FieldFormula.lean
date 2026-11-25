import OAI.LinearAlgebra.MatrixExponent.Realization
import OAI.LinearAlgebra.MatrixExponent.Rounds.Installation

/-! # The square exponent and rectangular rigidity over every field -/

namespace OAI.LinearAlgebra.MatrixExponent

theorem omega_eq_and_rigidity (F : Type*) [Field F] : omega F = 9 / 4 ∧ Rectangle.Rigidity F :=
  contact_of_installations (fun p _ => Rounds.installable (ZMod p)) F

/-- The exponent of square matrix multiplication by rational circuits over any field. -/
theorem omega_eq (F : Type*) [Field F] : omega F = 9 / 4 :=
  (omega_eq_and_rigidity F).1

theorem nine_fourths_le_omega (F : Type*) [Field F] : 9 / 4 ≤ omega F :=
  (omega_eq F).ge

/-- The rectangular exponent is the symmetric benchmark, including on the coordinate planes. -/
theorem Rectangle.exponent_eq (F : Type*) [Field F] {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : exponent F a b c = U a b c := by
  obtain ⟨square, rigid⟩ := omega_eq_and_rigidity F
  exact all_shapes rigid square ha hb hc

end OAI.LinearAlgebra.MatrixExponent
