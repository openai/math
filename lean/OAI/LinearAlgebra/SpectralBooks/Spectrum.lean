import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Algebra.Monoid

/-!
# Compactness of the normalized spectrum

The direct sum and tensor product of restriction classes give a semiring. It suffices here that
each class is a restriction of a natural number, represented by a diagonal tensor. We view a
point as a function into the nonnegative reals with the topology of pointwise convergence.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set NNReal

variable {S : Type*} [Semiring S]

/-- Normalized restriction-monotone semiring homomorphisms, as their pointwise evaluations. -/
def normalizedSpectrum (restricts : S → S → Prop) : Set (S → ℝ≥0) :=
  {f | f 0 = 0 ∧ f 1 = 1 ∧ (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, f (x * y) = f x * f y) ∧ ∀ x y, restricts x y → f x ≤ f y}

/-- A spectral point preserves the semiring operations. -/
def normalizedSpectrum.toRingHom {restricts : S → S → Prop}
    (f : normalizedSpectrum restricts) : S →+* ℝ≥0 where
  toFun := f.1
  map_zero' := f.2.1
  map_one' := f.2.2.1
  map_add' := f.2.2.2.1
  map_mul' := f.2.2.2.2.1

/-- Pointwise limits preserve all the spectral axioms, including every restriction comparison. -/
theorem isClosed_normalizedSpectrum (restricts : S → S → Prop) :
    IsClosed (normalizedSpectrum restricts) := by
  have hmono : IsClosed {f : S → ℝ≥0 | ∀ x y, restricts x y → f x ≤ f y} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_iInter fun _ ↦
      isClosed_le (continuous_apply x) (continuous_apply y)
  exact (isClosed_setOfPred_map_zero S ℝ≥0).inter <|
    (isClosed_setOfPred_map_one S ℝ≥0).inter <|
    (isClosed_setOfPred_map_add S ℝ≥0).inter ((isClosed_setOfPred_map_mul S ℝ≥0).inter hmono)

/-- Finite tensor rank bounds every coordinate of the normalized spectrum. -/
theorem isCompact_normalizedSpectrum (restricts : S → S → Prop)
    (hfinite : ∀ x : S, ∃ r : ℕ, restricts x r) : IsCompact (normalizedSpectrum restricts) := by
  choose r hr using hfinite
  apply IsCompact.of_isClosed_subset
    (isCompact_univ_pi (fun x ↦ isCompact_Icc (a := (0 : ℝ≥0)) (b := (r x : ℝ≥0))))
    (isClosed_normalizedSpectrum restricts)
  intro f hf x _
  have hle := hf.2.2.2.2 x _ (hr x)
  have hcast : f (r x : S) = (r x : ℝ≥0) := map_natCast (normalizedSpectrum.toRingHom ⟨f, hf⟩) _
  exact ⟨bot_le, hle.trans_eq hcast⟩

/-- On any tensor admitting a restriction to the unit, normalized logarithmic price is
continuous on the entire spectrum. -/
theorem continuous_log_price {restricts : S → S → Prop} {x : S} (hx : restricts 1 x) :
    Continuous (fun f : normalizedSpectrum restricts ↦ Real.logb 2 (f.val x : ℝ)) := by
  apply (continuous_subtype_val.comp ((continuous_apply x).comp continuous_subtype_val)).logb
  intro f
  have hone := f.2.2.2.2.2 1 x hx
  rw [f.2.2.1] at hone
  change (f.val x : ℝ) ≠ 0
  exact_mod_cast (zero_lt_one.trans_le hone).ne'

end SpectralBooks
end LinearAlgebra
end OAI
