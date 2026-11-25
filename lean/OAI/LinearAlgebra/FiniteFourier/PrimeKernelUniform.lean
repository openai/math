import OAI.LinearAlgebra.FiniteFourier.FieldKernelBound
import OAI.LinearAlgebra.FiniteFourier.PrimeBatchDescent
import OAI.LinearAlgebra.FiniteFourier.PrimeCoefficientRing
import OAI.LinearAlgebra.FiniteFourier.PrimeKernelSpecialization
import OAI.LinearAlgebra.FiniteFourier.PrimeCyclotomicRepair
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleSpecialize
import OAI.LinearAlgebra.FiniteFourier.PrimeStrictSaving

/-! # Uniform recursion and coefficient descent for the prime Fourier kernel

The digit count varies after fixing the label set, the repair pencil, and the
finite free extension. The strict saving counts calls relative to all rows
of this fixed batch. Restricting scalars after the recurrence introduces a
single factor depending on the extension degree.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

universe u

/-- The finite batch required of the rectangle and repair construction over a
fixed coefficient ring. The linear local work constant is chosen before the
digit count in `PrimeKernelBatch`. -/
def PrimeRepairedBatches (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K : Type u) [CommRing K] [Nontrivial K] [Invertible (ℓ : K)] (L b m : ℕ)
    (S : PrimeRectangleSystem K ℓ L b) (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ)
    [PrimeSpectrumOrthogonal hζ]
    (_ : PrimeRepairPencil ℓ m (countPencilOrder ℓ m) hζ)
    (ρ : Fin (primePredictorRows ℓ m (countPencilOrder ℓ m)) → K),
    (Pairwise fun i j => IsUnit (ρ i - ρ j)) → 2 ≤ m → m ≡ 1 [MOD ℓ] →
    let R := primePredictorRows ℓ m (countPencilOrder ℓ m)
    ∃ C : ℕ, PrimeKernelBatch ℓ (2*(m+S.D-1)) ((2^b)^L * R)
      (primeKernelCallBudget ℓ L b m S.D R) C ζ

/-- Choose the label parameters, repair coefficients, and basis before `k`.
The only remaining input here is the concrete finite-batch construction.
The coefficient ring need only satisfy the prime cyclotomic relations. -/
theorem primeTransform_bound_of_repairedBatches {ℓ : ℕ} [Fact ℓ.Prime] {θ : ℝ}
    (hθ : 1/2 < θ) (hbuild : PrimeRepairedBatches.{u} ℓ)
    {R : Type u} [CommRing R] [Nontrivial R] {ζ : R} (hp : IsUnit (ℓ : R))
    (hpow : ζ^ℓ = 1) (hsum : ∑ i ∈ Finset.range ℓ, ζ^i = 0) :
    ∃ B > (0 : ℝ), ∀ k : ℕ,
      (complexity (primeTransform ℓ k ζ) : ℝ) ≤ B * (ℓ : ℝ)^k * (1 + (k : ℝ))^θ := by
  have hℓ := (Fact.out : ℓ.Prime).two_le
  obtain ⟨L,b,m,_,_,hm,hcong,hsave⟩ := exists_primeKernelCallBudget_lt hℓ hθ
  let E := PrimeRepairExtension ζ ℓ m
  let a := primeRepairExtensionExponent ℓ m
  let := primeCyclotomicExtension_nontrivial ζ (p := ℓ) a
  have hE : IsUnit (ℓ : E) := by simpa using hp.map (algebraMap R E)
  let := hE.invertible
  let S := PrimeRectangleSystem.specialize E ℓ L b hE
  obtain ⟨env⟩ := exists_primeRepairEnvironment_of_sum hp hpow hsum m
  let := env.orthogonal
  let N := primePredictorRows ℓ m (countPencilOrder ℓ m)
  let W := (2^b)^L * N
  let A := 2*(m+S.D-1)
  let σ := primeKernelCallBudget ℓ L b m S.D N
  obtain ⟨C, hbatch⟩ := hbuild E L b m S _ env.root env.pencil env.nodes env.separated hm hcong
  have hclock : 0 < countPencilOrder ℓ m := by
    exact lt_of_lt_of_le (by decide : 0 < 2)
      ((le_max_left ..).trans (countPencilOrder_bounds hℓ m).1)
  have hN : 0 < N := by dsimp [N,primePredictorRows]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  have hA : 0 < A := by dsimp [A]; omega
  have hs : (σ : ℝ) / W < (A : ℝ)^θ := by
    simpa only [Nat.one_mul, Nat.mul_comm N, σ, A, W] using
      hsave S.D S.dimension_pos S.dimension_le N 1 hN Nat.zero_lt_one
  have hd : 0 < ℓ^a := pow_pos (Fact.out : ℓ.Prime).pos _
  let basis := primeCyclotomicBasis ζ (p := ℓ) a
  obtain ⟨B, hB, h⟩ := uniform_primeTransform_bound_of_extension_batch (d := ℓ^a) (C := C)
    (Fact.out : ℓ.Prime).one_lt hA hW (by linarith : 0 ≤ θ) hs
  exact ⟨B, hB, h R E (Fin (ℓ^a)) basis ⟨0, hd⟩ (by simp) ζ hbatch⟩

/-- A common constant for every specialization of the prime cyclotomic
coefficient ring, including those into rings with zero divisors. -/
def UniformPrimeKernelBound (ℓ : ℕ) (θ : ℝ) : Prop :=
  ∃ B > (0 : ℝ), ∀ (R : Type u) [CommRing R], IsUnit (ℓ : R) → ∀ ζ : R,
    (∑ i ∈ Finset.range ℓ, ζ^i = 0) → ∀ k : ℕ,
      (complexity (primeTransform ℓ k ζ) : ℝ) ≤ B * (ℓ : ℝ)^k * (1 + (k : ℝ))^θ

/-- Solve the recursion once over the integral cyclotomic ring. The same
constant then controls every image of its coefficient circuits, at every
digit length and in arbitrary characteristic. -/
theorem uniformPrimeKernelBound_of_repairedBatches {ℓ : ℕ} [Fact ℓ.Prime] {θ : ℝ}
    (hθ : 1/2 < θ) (hbuild : PrimeRepairedBatches.{0} ℓ) :
    UniformPrimeKernelBound.{u} ℓ θ := by
  obtain ⟨B, hB, h⟩ := primeTransform_bound_of_repairedBatches hθ hbuild
    (primeCoefficientRing_radix_unit ℓ) (primeCoefficientRoot_pow ℓ) (primeCoefficientRoot_sum ℓ)
  refine ⟨B, hB, fun R _ hℓ ζ hsum k => ?_⟩
  have hspec := complexity_primeTransform_map_le (primeCoefficientHom ζ hℓ hsum) ℓ k
    (primeCoefficientRoot ℓ)
  rw [primeCoefficientHom_root] at hspec
  exact (Nat.cast_le.mpr hspec).trans (h k)

/-- Over a field the cyclotomic sum relation follows from primitivity. -/
theorem UniformPrimeKernelBound.field {ℓ : ℕ} [Fact ℓ.Prime] {θ : ℝ}
    (h : UniformPrimeKernelBound.{u} ℓ θ) : UniformFieldKernelBound.{u} ℓ θ := by
  obtain ⟨B, hB, h⟩ := h
  exact ⟨B, hB, fun R _ hp ζ hζ =>
    h R (isUnit_iff_ne_zero.mpr hp) ζ (hζ.geom_sum_eq_zero (Fact.out : ℓ.Prime).one_lt)⟩

end

end

end FiniteFourier
end LinearAlgebra
end OAI
