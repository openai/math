import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionCutoff
import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionTensor
import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionScales
import OAI.LinearAlgebra.SpectralBooks.Fermion.PascalInverse
import OAI.LinearAlgebra.SpectralBooks.ShiftedCrossing.ShortenLimits

/-! # From the integral field identity to the shifted crossing over every field -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace Fermion

open Filter
open scoped Topology

/-- The two integral channels give the finite crossing in every characteristic. -/
theorem crossing_of_truncated (h : TruncatedIdentity) (H E : ℕ) (s : ℤ)
    (K : Type*) [Field K] :
    Nonempty (ShiftedCrossing.Factorization K (Fintype.card (Label H)) (states E).card
      ((H+1)^3 * (states (E+H+2*s)).card) ((H+1)^3 * (states (E+H-2*s)).card)) := by
  obtain ⟨B, hB⟩ := pairing_left_inverse H
  rw [card_label]
  refine finite_factorization (coefficientIdentity_of_truncated h) ?_ H E s B hB K
  intro i j hij
  simp [pairing, stateMinor, Ne.symm hij]

/-- The two shifted square-root rates follow from the field identity and the
computed asymptotic number of states below each energy. -/
theorem asymptoticFactorizations_of_truncated (h : TruncatedIdentity) (K : Type*) [Field K] :
    ShiftedCrossing.AsymptoticFactorizations K := by
  intro t u δ ht hu hlo hhi
  obtain ⟨H, E, s, hpos, hx, hy, hp, hm⟩ := exists_scaled_dimensions t u δ ht hu hlo hhi
  let rp (n : ℕ) := (H n+1)^3 * (states ((E n : ℤ)+H n+2*s n)).card
  let rm (n : ℕ) := (H n+1)^3 * (states ((E n : ℤ)+H n-2*s n)).card
  refine ⟨fun n ↦ Fintype.card (Label (H n)), fun n ↦ (states (E n)).card, rp, rm,
    fun n ↦ Real.logb 2 (rp n) / n, fun n ↦ Real.logb 2 (rm n) / n, ?_, hx, hy,
    Eventually.of_forall (fun _ ↦ ⟨le_rfl, le_rfl⟩), hp, hm⟩
  filter_upwards [hpos] with n hn
  exact ⟨hn.1, hn.2, crossing_of_truncated h _ _ _ _⟩

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
