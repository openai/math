import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.MultiplicativeStates
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.StateObstruction
import OAI.LinearAlgebra.SpectralBooks.Spectrum

/-! # A spectral point from absence of additive compression

We apply the compact state-space construction with a zero detector. The
resulting multiplicative state takes nonnegative real values, so it defines a
point of the normalized spectrum.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.AuxiliarySeparation

/-- A bounded Strassen preorder which cannot absorb a positive scalar into an
additive catalyst admits a normalized monotone semiring homomorphism. -/
theorem spectralPoint_of_no_compression {S : Type*} [CommSemiring S] [Preorder S]
    (R : S → ℕ) (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c d : S, a ≤ b → c ≤ d → a + c ≤ b + d)
    (hmul : ∀ z a b : S, a ≤ b → z * a ≤ z * b)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hno : ∀ (D : S) (m : ℕ), 0 < m → ¬ D + (m : S) ≤ D) :
    (normalizedSpectrum ((· ≤ ·) : S → S → Prop)).Nonempty := by
  have hstates := normalizedStates_nonempty_of_no_catalyst R 0 0 hzero hbound hadd
    (fun D s m hm => by simpa only [Nat.cast_zero, zero_mul, add_zero] using hno D m hm)
  have hdom (z x : S) : z * x ≤ (R x : S) * z :=
    (hmul z _ _ (hbound x)).trans_eq (mul_comm _ _)
  obtain ⟨f, hf, hfbound, _⟩ :=
    exists_monotone_semiringHom_of_normalizedStates R 0 0 hunit hmul hdom (by simpa only [Nat.cast_zero] using hstates)
  refine ⟨fun x => ⟨f x, (hfbound x).1⟩, ?_⟩
  exact ⟨Subtype.ext (map_zero f), Subtype.ext (map_one f),
    fun x y => Subtype.ext (map_add f x y), fun x y => Subtype.ext (map_mul f x y),
    fun _ _ h => hf h⟩

end SpectralBooks
end LinearAlgebra
end OAI
