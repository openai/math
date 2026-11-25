import OAI.LinearAlgebra.FiniteFourier.AtTwoFourierInverse
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPackedBlockProduct
import OAI.LinearAlgebra.FiniteFourier.DyadicFourierWord

/-! # Protected Fourier transforms on a prime axis of the two-local jet -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation.AtTwoPrimeAxis

/-- The forward and inverse transforms on one half-length prime axis have common
logarithmic depth, using the separated ternary roots in the coefficient tower. -/
theorem jetRoot_words {M p : ℕ} [Fact p.Prime] {hM : Odd M} {hp : p % 4 = 3}
    {hp7 : 7 ≤ p} (a : AtTwoPrimeAxis M p hM hp hp7) (h B : ℕ)
    (hle : (p-1)/2 ≤ B) (h3 : ∀ j, 3^j ≤ 8*B → 3^j ∣ M) :
    let m := (p-1)/2
    let D := 6400*(1 + Nat.clog 2 (2+B))
    OccupiedWord (Fin (13*m)) D (dftMatrix m (a.jetRoot h : IntegralJet M h)) ∧
    OccupiedWord (Fin (13*m)) D (dftMatrix m (a.jetRoot h : IntegralJet M h))⁻¹ := by
  intro m D
  let φ := algebraMap (CyclotomicCoefficients TwoLocalQuadratic M) (IntegralJet M h)
  have hs : Pairwise fun i k : Fin m =>
      IsUnit ((a.jetRoot h : IntegralJet M h)^i.val - (a.jetRoot h : IntegralJet M h)^k.val) := by
    intro i k hik
    simpa [jetRoot, φ] using (a.separated i k hik).map φ
  have roots (j : ℕ) (hj : 3^j ≤ 8*B) : IsUnit ((3^j : ℕ) : IntegralJet M h) ∧
      ∃ u : (IntegralJet M h)ˣ, u^(3^j) = 1 ∧
        Pairwise fun i k : Fin (3^j) => IsUnit ((u : IntegralJet M h)^i.val - (u : IntegralJet M h)^k.val) := by
    obtain ⟨u, _, hu, hsep⟩ := integralJet_axisRoot hM (h3 j hj) h
    exact ⟨isUnit_odd_inIntegralJet _ _ (hM.of_dvd_nat (h3 j hj)), u, hu, hsep⟩
  have pos : 0 < m := by dsimp [m]; omega
  rw [← geometricMatrix_eq_dftMatrix]
  constructor
  · exact protectedFourier_word_up_to (Or.inr rfl) pos hle roots (integralJet_unit_split M h)
      (a.jetRoot h).isUnit hs (Or.inl rfl)
  · exact protectedFourier_word_up_to (Or.inr rfl) pos hle roots (integralJet_unit_split M h)
      (a.jetRoot h).isUnit hs (Or.inr rfl)

end Deformation.AtTwoPrimeAxis

end FiniteFourier
end LinearAlgebra
end OAI
