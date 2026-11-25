import OAI.LinearAlgebra.FiniteFourier.PrimeCyclotomicExtension
import OAI.LinearAlgebra.FiniteFourier.PrimeFixedRepair

/-! # The finite coefficient environment of a repaired prime Fourier template

The clock and parity-check nodes are chosen using just the number of queries
and the radix. Their power-basis extension works for every row length.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Finset

/-- The extension needs enough prime-power roots for both the clock and all
check nodes. The exponent is fixed before the length of the Fourier axes. -/
noncomputable def primeRepairExtensionExponent (ℓ m : ℕ) : ℕ :=
  max (Nat.clog ℓ (max 2 (repairWindowDegree ℓ m)))
    (Nat.clog ℓ (primePredictorRows ℓ m (countPencilOrder ℓ m)))

variable {R : Type*} [CommRing R] {ℓ : ℕ} [Fact ℓ.Prime] [NeZero ℓ]

/-- The explicit finite free ring used for all lengths of one repair template. -/
abbrev PrimeRepairExtension (ζ : R) (ℓ m : ℕ) :=
  PrimeCyclotomicExtension ζ ℓ (primeRepairExtensionExponent ℓ m)

/-- All coefficient data required by the fixed repair, including its pencil
on independent rows and a full set of admissible Vandermonde nodes. -/
structure PrimeRepairEnvironment (ζ : R) (ℓ m : ℕ) [NeZero ℓ] where
  root : IsPrimitiveRoot (algebraMap R (PrimeRepairExtension ζ ℓ m) ζ) ℓ
  orthogonal : PrimeSpectrumOrthogonal root
  invRadix : PrimeRepairExtension ζ ℓ m
  invRadix_mul : invRadix * ℓ = 1
  pencil : PrimeRepairPencil ℓ m (countPencilOrder ℓ m) root
  nodes : Fin (primePredictorRows ℓ m (countPencilOrder ℓ m)) → PrimeRepairExtension ζ ℓ m
  separated : Pairwise fun i j => IsUnit (nodes i - nodes j)

/-- The construction uses only relations preserved under base change. -/
theorem exists_primeRepairEnvironment_of_sum [Nontrivial R] {ζ : R} (hp : IsUnit (ℓ : R))
    (hpow : ζ ^ ℓ = 1) (hsum : ∑ i ∈ Finset.range ℓ, ζ ^ i = 0) (m : ℕ) :
    Nonempty (PrimeRepairEnvironment ζ ℓ m) := by
  let a := primeRepairExtensionExponent ℓ m
  let b := countPencilOrder ℓ m
  let k := Nat.clog ℓ (max 2 (repairWindowDegree ℓ m))
  let W := primePredictorRows ℓ m b
  let E := PrimeRepairExtension ζ ℓ m
  let : Nontrivial E := primeCyclotomicExtension_nontrivial ζ a
  let : NeZero b := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have hk : k ≤ a+1 := (le_max_left _ _).trans (Nat.le_succ a)
  have hW : W ≤ ℓ ^ (a + 1) :=
    (Nat.clog_le_iff_le_pow (Fact.out : ℓ.Prime).one_lt).mp
      ((le_max_right _ _).trans (Nat.le_succ a))
  obtain ⟨hξ, hξu⟩ := primeCyclotomicRoot_power_data a k hk hp hpow hsum
  obtain ⟨hz,hu⟩ := primeCyclotomicRoot_power_data a 1 (Nat.succ_le_succ (Nat.zero_le a)) hp hpow hsum
  have hζ : IsPrimitiveRoot (algebraMap R E ζ) ℓ := by
    simpa only [Nat.add_one_sub_one, primeCyclotomicRoot_pow, pow_one] using hz
  have hunit : ∀ i, 0 < i → i < ℓ → IsUnit ((algebraMap R E ζ) ^ i - 1) := by
    simpa only [Nat.add_one_sub_one, primeCyclotomicRoot_pow, pow_one] using hu
  have hℓ : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  have hb := (le_max_right 2 (repairWindowDegree ℓ m)).trans (countPencilOrder_bounds hℓ m).1
  obtain ⟨pencil⟩ := exists_primeRepairPencil (b := b) hζ hξ.pow_eq_one hξu hb
  have hr : IsUnit (ℓ : E) := by simpa using hp.map (algebraMap R E)
  exact ⟨⟨hζ, PrimeSpectrumOrthogonal.of_unit_sub hζ hunit, ↑hr.unit⁻¹,
    by simp, pencil, _, primeCyclotomicNodes_pairwise_of_sum a hp hpow hsum hW⟩⟩

/-- Over a coefficient domain, primitivity supplies the cyclotomic sum relation. -/
theorem exists_primeRepairEnvironment [IsDomain R] {ζ : R} (hp : IsUnit (ℓ : R))
    (hζ : IsPrimitiveRoot ζ ℓ) (m : ℕ) : Nonempty (PrimeRepairEnvironment ζ ℓ m) :=
  exists_primeRepairEnvironment_of_sum hp hζ.pow_eq_one
    (hζ.geom_sum_eq_zero (Fact.out : ℓ.Prime).one_lt) m

end FiniteFourier
end LinearAlgebra
end OAI
