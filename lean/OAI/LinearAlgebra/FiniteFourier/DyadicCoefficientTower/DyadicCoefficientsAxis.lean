import OAI.LinearAlgebra.FiniteFourier.DyadicCoefficientsPacking
import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicPrimeAxis

/-! # The concrete prime-axis presentations of a protected dyadic list -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace DyadicCoefficientTower

open Deformation

noncomputable section

variable {η : ℝ} {n B : ℕ} {D : DyadicAxisPacking GaussianRationals η n B} {L : Finset ℕ}
    (T : DyadicCoefficientTower D L) {p : ℕ} (hp : p ∈ D.packing.axes)

include T hp

theorem axis_prime : p.Prime := (D.axis_properties T.width hp).1

theorem axis_large : 1 < p-1 := by have := (D.axis_properties T.width hp).2.1; omega

theorem predecessor_dvd : p-1 ∣ D.rootOrder := (D.axis_properties T.width hp).2.2.2

theorem axisPredecessorUnit : IsUnit ((p-1 : ℕ) : T.Order) :=
  (T.transform_nodes (T.predecessor_dvd hp) (RingHom.id _)).1

/-- A chosen system of powers in the unit group of the residue classes. -/
def axisOrbit : PrimeAxisOrbit p := by
  let : Fact p.Prime := ⟨T.axis_prime hp⟩
  exact PrimeAxisOrbit.ofPrime p

/-- The unit lifting the chosen predecessor root in the coefficient order. -/
def axisRoot : T.Orderˣ := (T.transform_nodes (T.predecessor_dvd hp) (RingHom.id _)).2.choose

theorem axisRoot_value : (T.axisRoot hp : T.Order) =
    AdjoinRoot.root T.modulus^(D.rootOrder/(p-1)) :=
  (T.transform_nodes (T.predecessor_dvd hp) (RingHom.id _)).2.choose_spec.1

theorem axisRoot_pow : (T.axisRoot hp)^(p-1) = 1 :=
  (T.transform_nodes (T.predecessor_dvd hp) (RingHom.id _)).2.choose_spec.2.1

theorem axisRoot_separate : ∀ i j : Fin (p-1), i ≠ j →
    IsUnit ((T.axisRoot hp : T.Order)^i.val - (T.axisRoot hp : T.Order)^j.val) :=
  (T.transform_nodes (T.predecessor_dvd hp) (RingHom.id _)).2.choose_spec.2.2

theorem axisRoot_primitive : IsPrimitiveRoot (T.axisRoot hp : T.Order) (p-1) := by
  rw [T.axisRoot_value hp]
  exact T.primitive.pow D.rootOrder_pos (Nat.div_mul_cancel (T.predecessor_dvd hp)).symm

/-- The single chosen presentation used by both operand circuits and the return circuit. -/
def primeAxis [Fact p.Prime] [Nontrivial T.Order] :
    DyadicPrimeAxis T.Order p (T.axisOrbit hp) (T.axisRoot hp) (T.axisPredecessorUnit hp) :=
  dyadicPrimeAxis (T.axisOrbit hp) (T.axisRoot hp) (T.axis_large hp)
    (T.axis_unit hp (RingHom.id _)) (T.axisPredecessorUnit hp) (T.axisRoot_pow hp)
    (T.axisRoot_separate hp)

end

end DyadicCoefficientTower

end FiniteFourier
end LinearAlgebra
end OAI
