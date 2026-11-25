import OAI.LinearAlgebra.MatrixExponent.Sphere.General.Law
import OAI.LinearAlgebra.MatrixExponent.Sphere.General.RawFamily
import OAI.LinearAlgebra.MatrixExponent.Shaving.FieldStage
import OAI.LinearAlgebra.MatrixExponent.Valued.Shared

/-! # Local concentration over a polynomial-size working field -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Raw
open Filter

theorem local_bookkeeping (k : Type) [Field k] [Finite k]
    (sync : Prices.SharedPrice (AlgebraicClosure k)) (g ℓ D : ℕ) (hD : Input.threshold g ≤ D) :
    BookkeepingLaw k g ℓ D hD := by
  obtain ⟨K, _, _, _, p, l, b, _, _, A, h⟩ := ordered_bookkeeping k sync g ℓ D hD
  obtain ⟨L, hL, chooseField⟩ := Shaving.extension k K A
  refine ⟨K, inferInstance, inferInstance, inferInstance, p, l, b, inferInstance, inferInstance, A, L, hL, ?_⟩
  intro c hc
  obtain ⟨B, hB, window⟩ := h c
  refine ⟨B, hB, ?_⟩
  filter_upwards [window, chooseField, eventually_ge_atTop 2] with T ready ext ht
  obtain ⟨d, sc, hk, hu, hsize, works⟩ := ready
  refine ⟨d, sc, hk, hu, hsize, ?_, works⟩
  obtain ⟨F, _, _, _, _, _, _, lo, hi, rank⟩ := ext
  have h₁ : 2 * T ≤ T ^ 4 := calc
    _ ≤ T * T := Nat.mul_le_mul_right _ ht
    _ = T ^ 2 := (pow_two _).symm
    _ ≤ T ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h₂ := (Nat.pow_le_pow_left (Nat.le_succ T) (5 * A + 2)).trans
    (Nat.pow_le_pow_right (Nat.succ_pos T) hc)
  exact ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_left h₁ 1) A)).trans lo,
    hi.trans h₂, rank⟩

theorem local_bookkeeping_of_saving (k : Type) [Field k] [Finite k]
    (hs : omega k < 9 / 4) (g ℓ D : ℕ) (hD : Input.threshold g ≤ D) :
    BookkeepingLaw k g ℓ D hD :=
  local_bookkeeping k (shared_of_saving hs) g ℓ D hD

end OAI.LinearAlgebra.MatrixExponent.Rounds.Raw
