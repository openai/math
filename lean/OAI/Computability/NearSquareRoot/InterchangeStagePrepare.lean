import OAI.Computability.NearSquareRoot.InterchangeStageConjugate
import OAI.Computability.NearSquareRoot.InterchangeStageLayouts

/-!
# Original and rectangle basis changes in the physical field order

Changing basis in the original reserve is independent of the queried main
pair. The subsequent physical pivot list places precisely the `preparedQuery`
coordinates in the selected slots.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeStageLift

open NearSquareRoot.Interchange IntegerMultiplication.Port

variable {a c e m : ℕ} {K R : Type} [Semiring K] [AddCommMonoid R] [Module K R]

/-- Interpret the prepared reserve block in its original set of physical slots. -/
def reserveMap (hce : c+e=a) (P : (Fin a → R) ≃ₗ[K] (Fin (c+e) → R)) :
    (Fin a → R) ≃ₗ[K] (Fin a → R) :=
  P.trans {
    toFun := fun v i => v (Fin.cast hce.symm i)
    invFun := fun v i => v (Fin.cast hce i)
    left_inv := fun v => by funext i; simp
    right_inv := fun v => by funext i; simp
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem preparedQuery_eq_shuffle (hce : c+e=a)
    (P : (Fin a → ℚ) ≃ₗ[ℚ] (Fin (c+e) → ℚ)) (z : Fin (a+2) → ℚ) :
    preparedQuery P z = reserveBlock (reserveMap hce P) z ∘ shuffle hce := by
  rw [reserveBlock_shuffle]
  rfl

/-- The small commuting diagram of linear equivalences induces its claimed
map on the complete physical address, for every choice of spectator values. -/
theorem lift_prepared_diagram (hce : c+e=a) (j : Fin m)
    (P : (Fin a → ℚ) ≃ₗ[ℚ] (Fin (c+e) → ℚ))
    (F : (Fin (c+(2+e)) → ℚ) ≃ₗ[ℚ] (Fin (c+(2+e)) → ℚ))
    (C : (Fin (c+(2+e)) → ℚ) ≃ₗ[ℚ] (Fin (a+2) → ℚ))
    (S : (Fin (a+2) → ℚ) ≃ₗ[ℚ] (Fin (a+2) → ℚ))
    (h : (preparedQuery P).trans (F.trans C) = S) (x : Duplex (Fin (a+m+a)) ℚ) :
    reserveShift hce
      (update (rectSlots hce j) (fun v => C v ∘ shuffle hce)
        (update (rectSlots hce j) F (reserveShift hce (update (earlySlots a m) (reserveMap hce P) x)))) =
      update (querySlots a j) S x := by
  apply physical_diagram
  intro z
  rw [← preparedQuery_eq_shuffle hce P]
  exact congrArg (fun A : (Fin (a+2) → ℚ) ≃ₗ[ℚ] (Fin (a+2) → ℚ) => A z) h

end InterchangeStageLift

end NearSquareRoot
end Computability
end OAI
