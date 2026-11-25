import OAI.LinearAlgebra.FiniteFourier.SynchronizedKernelCost
import OAI.LinearAlgebra.FiniteFourier.BoundedEliminationUnits
import OAI.LinearAlgebra.FiniteFourier.IntegralTensorRecovery

/-! # Uniform tensor circuits from protected local transvections

Local elimination gives two lists of unit transvections around one diagonal.
Padding to the length at the maximum dimension lets every factor share
the same sequence of Fourier stages.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- Lift a bounded-slot implementation of each unit transvection to a
protected circuit for any list of prescribed integer matrices. -/
theorem integerImageGridTensorEstimate_of_unit_words {P : Finset ℕ}
    (hP : ∀ l ∈ P, Nat.Prime l) {R : Type*} [CommRing R] [Algebra (protectedRationals P) R]
    (split : ∀ x : R, ∃ y, IsUnit y ∧ IsUnit (x-y)) {p lo hi t : ℕ} {ζ : R}
    (words : ∀ m : ℕ, lo ≤ m → m ≤ hi → ∀ T : Matrix.TransvectionStruct (Fin m) R,
      IsUnit T.c → KernelWord p ζ t T.toMatrix)
    {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hc : ∀ k : ℕ, (complexity (primeTransform p k ζ) : ℝ) ≤ C * (p : ℝ)^k * (1+(k : ℝ))^β) :
    IntegerImageGridTensorEstimate R lo hi β (((t * (4 * hi^2) + 1 : ℕ) : ℝ) * C) := by
  intro k n hn A
  have hw (i : Fin k) : KernelWord p ζ (t * (4 * hi^2) + 1) ((A i).map (Int.castRingHom R)) := by
    obtain ⟨L, L', D, hlen, hu, hu', hd⟩ := exists_integral_unit_shear_factorization hP split (A i)
    have hs := words (n i) (hn i).1 (hn i).2
    apply KernelWord.of_factorization L L' D _ hd
      (fun T hT => hs T (hu T hT)) (fun T hT => hs T (hu' T hT))
    refine hlen.trans ?_
    simp only [Fintype.card_fin]
    gcongr
    exact (hn i).2
  simpa only [Fintype.card_pi, Fintype.card_fin] using KernelWord.grid_bound hw hβ hC
    (fun k _ => hc k)

end FiniteFourier
end LinearAlgebra
end OAI
