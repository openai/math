import OAI.LinearAlgebra.SpectralBooks.VNP.EpochProfileBudget

/-! # The selector cost of a one-copy crossing identity -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Companion

open OAI.LinearAlgebra.SpectralBooks
open Crossing VNP

/-- The fixed selector code has room for the rounded binary index of every summand.
After reserving this width, the singleton histogram bound remains strict. -/
theorem profile_rounded_saving {D : ℕ} (P : ProfileShape D) (hD : 0 < D) :
    P.epochWireBudget + 2 * D * (Nat.clog 2 P.terms : ℝ) < 2 * D * P.m := by
  have code : P.terms ≤ 2 ^ P.bits := by
    simpa [BitString] using Fintype.card_le_of_injective P.code P.code.injective
  have bits : (Nat.clog 2 P.terms : ℝ) ≤ P.bits := by
    exact_mod_cast (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr code
  have selector := mul_le_mul_of_nonneg_left bits (by positivity : 0 ≤ 2 * (D : ℝ))
  have saving := P.epoch_saving
  have positive : 0 < P.saving * 2 * (D : ℝ) * P.m := by
    have := P.saving_pos
    have := P.width_pos
    positivity
  linarith only [selector, saving, positive]

/-- A profile shortening yields a one-copy identity at positive width with a common
cost bound including the selector width used by the companion stretch theorem. -/
theorem exists_paid_network {F : Type*} [Field F] {D : ℕ} (hD : 0 < D)
    (short : Crossing.HasProfileShortening F D) :
    ∃ (m A : ℕ) (cap : ℝ), 0 < m ∧ 0 < A ∧
      cap + 2 * D * (Nat.clog 2 A : ℝ) < 2 * D * m ∧
      Nonempty (CrossingNetworkSum F D m A cap) := by
  obtain ⟨P, v, hv⟩ := ProfileShape.exists_of_shortening F short
  exact ⟨P.m, P.terms, P.epochWireBudget, P.width_pos, P.terms_pos,
    profile_rounded_saving P hD, ⟨P.epochNetwork hv⟩⟩

end Companion

end FiniteFourier
end LinearAlgebra
end OAI
