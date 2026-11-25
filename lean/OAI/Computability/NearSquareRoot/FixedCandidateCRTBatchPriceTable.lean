import OAI.Computability.NearSquareRoot.FixedCandidateCRTBatchKernel
import OAI.Computability.NearSquareRoot.PrecisionActualPhaseClock

/-! # Charging the seed and both reflection tables to a batch's storage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTKernel

open IntegerMultiplication.Code NearSquareRoot.Controlled

/-- A polynomial computation on the address width fits in a constant multiple
of the outer arena whenever the arena can hold all occupied record rows. -/
theorem polynomial_setup_le_width {X : Type} {k c width s : X → ℕ}
    (cost : Dom k s) (occupied : ∀ x, 0 < c x)
    (volume : ∃ C : ℕ, ∀ x, 2 ^ k x * c x ≤ C * (width x + 1)) :
    ∃ A : ℕ, ∀ x, s x ≤ A * (width x + 1) := by
  obtain ⟨L, setup⟩ := FixedPoint.setup_le_array cost
  obtain ⟨C, rows⟩ := volume
  refine ⟨L * C, fun x => ?_⟩
  have cells := (Nat.le_mul_of_pos_right (2 ^ k x) (occupied x)).trans (rows x)
  exact (setup x).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left L cells)

/-- A single bound applies to every forward and inverse permutation on a
batch's bit positions, regardless of the coefficient values. -/
theorem seed_tables_le_width {X : Type} (p : X → Batch) {c width : X → ℕ}
    (seedBound : Dom (fun x => (p x).k) (fun x => size (p x).seed))
    (occupied : ∀ x, 0 < c x)
    (volume : ∃ C : ℕ, ∀ x, 2 ^ (p x).k * c x ≤ C * (width x + 1)) :
    ∃ A : ℕ, ∀ x (π : Equiv.Perm (Fin (p x).k)),
      size (p x).seed + size (Reflections.table π) + size (Reflections.table π.symm) ≤
        A * (width x + 1) := by
  have tables : Dom (fun x => (p x).k) (fun x => 4 * ((p x).k + 1)^2) :=
    ⟨2, 4, fun _ => le_rfl⟩
  obtain ⟨A, bound⟩ := polynomial_setup_le_width (seedBound.add tables) occupied volume
  refine ⟨A, fun x π => ?_⟩
  have fwd := Reflections.table_size π
  have inv := Reflections.table_size π.symm
  have both := bound x
  change size (p x).seed + 4 * ((p x).k + 1)^2 ≤ A * (width x + 1) at both
  omega

end FixedCandidate.CRTKernel

end NearSquareRoot
end Computability
end OAI
